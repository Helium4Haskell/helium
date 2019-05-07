{-# LANGUAGE FlexibleContexts #-}

{-| Module      :  RepairHeuristics
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Heuristics that supply additional hints with a type error how a program
    can be corrected.
-}

module Helium.StaticAnalysis.HeuristicsOU.RepairHeuristics where

import Helium.StaticAnalysis.HeuristicsOU.OnlyResultHeuristics

import Rhodium.Core
import Rhodium.TypeGraphs.GraphProperties
import Rhodium.TypeGraphs.Graph
import Rhodium.Blamer.Heuristics
import Rhodium.Blamer.HeuristicProperties
import Rhodium.Blamer.HeuristicsUtils
import Rhodium.TypeGraphs.GraphUtils
import Rhodium.Blamer.Path

import Helium.Syntax.UHA_Syntax
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.StaticAnalysis.Messages.HeliumMessages
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU
import Helium.StaticAnalysis.HeuristicsOU.HeuristicsInfo
import Helium.StaticAnalysis.Miscellaneous.DoublyLinkedTree
import Helium.StaticAnalysis.Inferencers.OutsideInX.ConstraintHelper
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumInstances
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.Utils.OneLiner
import Helium.StaticAnalysis.Messages.TypeErrors
import Helium.StaticAnalysis.Messages.Messages (showNumber, ordinal, prettyAndList)

import Unbound.LocallyNameless.Fresh
import Unbound.LocallyNameless hiding (GT, Name, from, to)

import Debug.Trace
   
import Data.List
import Data.Maybe

import Control.Monad

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes



-----------------------------------------------------------------------------

fixHint, becauseHint, possibleHint :: WithHints a => String -> a -> a
fixHint      = addHint "probable fix"
becauseHint  = addHint "because"
possibleHint = addHint "possible fix"


heuristicsMAX :: Int
heuristicsMAX = 120

type Permutation = [Int]

permutationsForLength :: Int -> [Permutation]
permutationsForLength 0 = [ [] ]
permutationsForLength i = [ ys | xs <- permutationsForLength (i-1), ys <- insertSomewhere (i-1) xs ]
  where
   insertSomewhere j []     = [ [j] ]
   insertSomewhere j (x:xs) = (j:x:xs) : map (x:) (insertSomewhere j xs)
         
deleteIndex :: Int -> [a] -> [a]
deleteIndex _ []     = []
deleteIndex 0 (_:as) = as
deleteIndex i (a:as) = a : deleteIndex (i-1) as

permute :: Permutation -> [a] -> [a]
permute is as = map (as !!) is



instance IsPattern ConstraintInfo where
   isPattern cinfo = 
      case (self . attribute . localInfo) cinfo of 
         UHA_Pat _ -> True
         _         -> False


applicationHeuristic :: Fresh m => VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
applicationHeuristic = SingleVoting "Application heuristic" f
   where
      f e@(constraint, eid, ci) = 
         case maybeApplicationEdge ci of
            Nothing -> return Nothing
            Just (isBinary, tuplesForArguments) -> 
               if isGADTPatternApplication ci then
                  return Nothing
               else  
               doWithoutEdge eid $ do
               axioms <- getAxioms 
               let Constraint_Unify t1 t2 _ = constraint
               maybeExpectedType <- getSubstType $ MType t1
               maybeFunctionType <- getSubstType $ MType t2
               case (maybeFunctionType, maybeExpectedType) of 
                  (MType functionType, MType expectedType)
                     | length tuplesForArguments > length functionArguments -> error $ show ("Length not correct", functionType, expectedType, constraint, ci)
                     | length argumentPermutations == 1 && length (concat argumentPermutations) > 1 -> 
                        let p = head argumentPermutations
                        in 
                        if p==[1,0] && isBinary
                           then 
                                 let hint = setTypePair (expectedType, functionType) . fixHint "swap the two arguments"
                                 in return $ Just
                                       (3, "swap the two arguments", constraint, eid, hint ci)
                           else         
                                 let hint = setTypePair (expectedType, functionType) . fixHint "re-order arguments"                              
                                 in return $ Just
                                       (1, "application: permute with "++show p, constraint, eid, hint ci)
                     | length incorrectArguments == 1  ->
                        do 
                           let   
                                 i           = head incorrectArguments
                                 (source,tp) = tuplesForArguments !! i
                                 range       = rangeOfSource source
                                 oneLiner    = oneLinerSource source
                           MType tp'         <- getSubstType $ MType tp
                           let expargtp      = fst (functionSpine expectedType) !! i
                           let infoFun       = typeErrorForTerm (isBinary,isPatternApplication) i oneLiner expectedType (tp',expargtp) range
                           return $ Just 
                                 (3, "incorrect argument of application="++show i, constraint, eid, infoFun ci)
                     | maybe False (< numberOfArguments) maximumForFunction && not isPatternApplication ->
                        case typesZippedWithHoles of
                           -- there is only one possible set to remove arguments 
                           [is] | not isBinary && maybe True (>= 1) maximumForFunction
                                 -> let hint = fixHint ("remove "++prettyAndList (map (ordinal True . (+1)) is)++" argument")
                                    in return $ Just
                                          (4, "too many arguments are given: "++show is, constraint, eid, hint ci)
   
   
                           _    -- the expression to which arguments are given does not have a function type
                                 | maybe False (<= 0) maximumForFunction && not isBinary && not (isPattern ci) ->                       
                                       let hint = becauseHint "it is not a function"
                                       in return $ Just
                                             (6, "not a function", constraint, eid, hint ci)
   
                                 -- function used as infix that expects < 2 arguments
                                 | maybe False (<= 1) maximumForFunction && isBinary && not (isPattern ci) ->
                                       let hint = becauseHint "it is not a binary function"
                                       in return $ Just
                                             (6, "no binary function", constraint, eid, hint ci)
   
                           -- more than one or no possible set of arguments to be removed
                                 | otherwise -> 
                                       let hint = becauseHint "too many arguments are given"
                                       in return $ Just
                                             (2, "too many arguments are given", constraint, eid, hint ci)
                                       
                     -- not enough arguments are given
                     | minimumForContext > numberOfArguments && not isPatternApplication && contextIsUnifiable ->
                        case typesZippedWithHoles of
   
                           [is] | not isBinary 
                                 -> let hint = fixHint ("insert a "++prettyAndList (map (ordinal True . (+1)) is)++" argument")
                                    in return $ Just
                                          (4, "not enough arguments are given"++show is, constraint, eid, hint ci)
   
                           _   -> let hint = becauseHint "not enough arguments are given"
                                    in return $ Just
                                          (2, "not enough arguments are given", constraint, eid, hint ci)
               
                     | otherwise -> return Nothing
         
                    where
                     unifiableTypeLists s1 s2 = runFreshM (runTG (unifiableTypeLists' s1 s2))
                     unifiableTypeLists' s1 s2 = unifyTypes axioms [] [Constraint_Unify (monotypeTuple s1) (monotypeTuple s2) Nothing] (nub (fv functionType ++ fv expectedType))
                     numberOfArguments = length tuplesForArguments     
                     argumentPermutations = 
                                    [ p 
                                    | length functionArguments == length expectedArguments 
                                    , p <- take heuristicsMAX (permutationsForLength numberOfArguments)
                                    , isJust (unifiableTypeLists (functionResult : functionArguments) 
                                                         (expectedResult : permute p expectedArguments)) 
                                    ]   
                     (functionArguments, functionResult) = functionSpineOfLength numberOfArguments functionType
                     (expectedArguments, expectedResult) = functionSpineOfLength numberOfArguments expectedType
                     isPatternApplication = isPattern ci
                     incorrectArguments = [ i 
                        | length functionArguments == length expectedArguments 
                        , i <- [0..numberOfArguments-1]
                        , isNothing (unifiableTypeLists [(functionArguments !! i)] [(expectedArguments !! i)])
                        , isJust (unifiableTypeLists (functionResult : deleteIndex i functionArguments) 
                                             (expectedResult : deleteIndex i expectedArguments))
                        ]
                     maximumForFunction = case functionSpine expectedType of
                           ([], MonoType_Var  _ _) -> Nothing
                           (tps, _   ) -> Just (length tps)
   
                     -- minimum number of arguments that should be applied to the function to meet the expected context type
                     minimumForContext = length allFunctionArgs + numberOfArguments - length allExpectedArgs
                     
                     -- is the context unifiable?
                     contextIsUnifiable    = isJust $ unifiableTypeLists [functionResult] [snd (functionSpineOfLength minimumForContext expectedType)]
                     (allFunctionArgs, allFunctionRes) = functionSpine expectedType
                     (allExpectedArgs, allExpectedRes) = functionSpine functionType
                     typesZippedWithHoles  = [ is 
                        | (is,zl) <- take heuristicsMAX (zipWithHoles allFunctionArgs allExpectedArgs)
                        , let (as,bs) = unzip zl
                        , isJust $ unifiableTypeLists (allFunctionRes : as) 
                                             (allExpectedRes : bs)
                        ]                     

zipWithHoles :: [a] -> [b] -> [ ( [Int] , [(a,b)] ) ] 
zipWithHoles = rec_ 0 where

   rec_ i [] bs = [ (take (length bs) [i..] , []) ]
   rec_ i as [] = [ (take (length as) [i..] , []) ]
   rec_ i (a:as) (b:bs) = case compare (length as) (length bs) of
         LT -> [ (  is,(a,b):zl) | (is,zl) <- rec_ (i+1) as     bs ]
            ++ [ (i:is,      zl) | (is,zl) <- rec_ (i+1) (a:as) bs ]
         EQ -> [ ([],zip (a:as) (b:bs)) ] 
         GT -> [ (  is,(a,b):zl) | (is,zl) <- rec_ (i+1) as bs     ]
            ++ [ (i:is,      zl) | (is,zl) <- rec_ (i+1) as (b:bs) ]

type Sibblings = [[(String, PolyType ConstraintInfo)]]

maybeImportedName :: ConstraintInfo -> Maybe String
maybeImportedName cinfo = 
      case [ name | IsImported name <- properties cinfo ] of
         []  -> Nothing
         n:_ -> Just (show n)

sibblingsHeuristic :: Fresh m => Sibblings -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
sibblingsHeuristic siblings = 
   SingleVoting "Sibling functions" f
   where
      f pair@(constraint, edgeId, info) =
         case maybeImportedName info of 
            Nothing   ->  return Nothing
            Just name
               | null candidates -> return Nothing
               | otherwise -> 
                  doWithoutEdge edgeId $ 
                  do 
                     let mtp = case constraint of
                           Constraint_Unify t1 t2 _ -> Nothing
                           Constraint_Inst t1 t2 _ -> Just (t1, t2)
                           _ -> Nothing
                     case mtp of
                        Nothing -> return Nothing
                        Just (t1, t2) -> do
                           MType contextTp <- getSubstType $ MType t1
                           fits <- mapM (schemeFits contextTp . snd) candidates
                           case [ s | (True, (s, _)) <- zip fits candidates ] of
                              []          -> return Nothing
                              siblings'   ->    -- TODO: put all siblings in the message
                                       let   siblingsTextual = orList siblings'
                                             hint = fixHint ("use " ++ siblingsTextual ++ " instead")
                                       in return $ Just
                                                (10, "Sibling(s) "++siblingsTextual++" instead of "++show name, constraint, edgeId, hint info)
                                       
               where
                  orList :: [String] -> String
                  orList [s]    = s
                  orList (x:xs) = foldr (\y1 y2-> y1 ++ ", " ++ y2) ("or "++x) xs
                  orList []     = "this should never occur"
                  
                  candidates :: [(String, PolyType ConstraintInfo)]
                  candidates = 
                     let 
                        fn list 
                              | name `notElem` map fst list = []
                              | otherwise = filter ( (name /=) . fst) list
                     in concatMap fn siblings
                     
                  schemeFits contextTp scheme = do
                     freshIdentifier <- fresh (string2Name "a")
                     axioms <- getAxioms
                     sub <- unifyTypes axioms [] [Constraint_Unify (var freshIdentifier) contextTp Nothing, Constraint_Inst (var freshIdentifier) scheme Nothing] [freshIdentifier]
                     return $ isJust sub


class MaybeLiteral a where
   maybeLiteral :: a -> Maybe String  


instance MaybeLiteral ConstraintInfo where
   maybeLiteral cinfo = 
      let literalType x = 
               case x of 
                  Literal_Int    _ _ -> "Int"
                  Literal_Char   _ _ -> "Char"
                  Literal_String _ _ -> "String"
                  Literal_Float  _ _ -> "Float"
      in case (self . attribute . localInfo) cinfo of
            UHA_Expr (Expression_Literal _ literal ) -> Just (literalType literal)
            UHA_Pat  (Pattern_Literal    _ literal ) -> Just (literalType literal)
            x                                        -> Nothing


siblingLiterals :: Fresh m => VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
siblingLiterals = 
   SingleVoting "Sibling literals" f 
   where
      f pair@(constraint, eid, info) =
         case maybeLiteral info of 
            Nothing      -> return Nothing
            Just literal -> case constraint of
               Constraint_Unify t1 t2 _ ->
                  doWithoutEdge eid $
                     do 
                        MType tp <- getSubstType $ MType t1
                        --MType tp2 <- getSubstType $ MType t2
                        case (literal,tp) of

                           ("Int", MonoType_Con "Float")
                                 -> let hint = fixHint "use a float literal instead"
                                    in return $ Just
                                          (5, "Int literal should be a Float", constraint, eid, hint info)

                           ("Float", MonoType_Con "Int" )
                                 -> let hint = fixHint "use an int literal instead"
                                    in return $ Just
                                          (5, "Float literal should be an Int", constraint, eid, hint info)

                           ("Char", MonoType_App (MonoType_Con "[]") (MonoType_Con "Char"))
                                 -> let hint = fixHint "use a string literal instead"
                                    in return $ Just
                                          (5, "Char literal should be a String", constraint, eid, hint info)
                           ("Char", MonoType_Fam "String" [])
                                 -> let hint = fixHint "use a string literal instead"
                                    in return $ Just
                                          (5, "Char literal should be a String", constraint, eid, hint info)
                           ("String", MonoType_Con "Char")   
                                 -> let hint = fixHint "use a char literal instead"
                                    in return $ Just
                                          (5, "String literal should be a Char", constraint, eid, hint info)

                           _ -> return Nothing 
               _ -> return Nothing
         
               
class IsExprVariable a where
   isExprVariable          :: a -> Bool
   isEmptyInfixApplication :: a -> Bool

instance IsExprVariable ConstraintInfo where -- misleading name?
   isExprVariable cinfo =
      case (self . attribute . localInfo) cinfo of
         UHA_Expr (Expression_Variable _ _) -> True
         _ -> False
   isEmptyInfixApplication cinfo =
      case (self . attribute . localInfo) cinfo of
         UHA_Expr (Expression_InfixApplication _ MaybeExpression_Nothing _ MaybeExpression_Nothing) -> True
         x  -> False

variableFunction :: Fresh m => VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
variableFunction = SingleVoting "Variable function" f 
   where
      f pair@(constraint, eid, info) =  
         case constraint of 
            Constraint_Inst m1 p2 _ 
               | not (isExprVariable info)
                     -> return Nothing
               | otherwise 
                     -> do graph <- getGraph
                           doWithoutEdge eid $ 
                              do 
                                 let edge = getEdgeFromId graph eid
                                 mt1 <- getSubstType $ MType m1
                                 pt2 <- getSubstType $ PType p2
                                 edges1 <- getNeighbours (from edge)
                                 edges2 <- getNeighbours (to edge) 
                                 let special = filter (\e -> isConstraintEdge e && original e && maybe False isEmptyInfixApplication (getConstraintInfo (getConstraintFromEdge e))) (edges1 ++ edges2)
                                 edges3 <- mapM (\e -> (++) <$> getNeighbours (from e) <*> getNeighbours (to e)) special
                                 let   isApplicationEdge = isJust . maybeApplicationEdge
                                       application = any (maybe False isApplicationEdge . getConstraintInfo . getConstraintFromEdge) (edges1 ++ edges2 ++ concat edges3)  
                                 case (mt1, pt2) of
                                    (MType functionType, PType expectedType) | not application -> 
                                       do 
                                          expectedArgs <- functionSpineP expectedType
                                          let functionArgs = functionSpine functionType
                                          axioms <- getAxioms
                                          let   maxArgumentsForFunction = length (fst expectedArgs)
                                                minArgumentsForContext  = maxArgumentsForFunction - length (fst functionArgs) 
                                          contextIsUnifiable <- 
                                             unifyTypes axioms [] 
                                                [Constraint_Inst (snd $ functionSpineOfLength minArgumentsForContext functionType) expectedType Nothing] 
                                                   []
                                          if minArgumentsForContext <= 0 || isJust contextIsUnifiable
                                             then return Nothing
                                             else let hint = fixHint ("insert "++showNumber minArgumentsForContext++" argument"++
                                                                  if minArgumentsForContext <= 1 then "" else "s")
                                                   in return $ Just 
                                                         (4, "insert arguments to function variable", constraint, eid, hint info)
                                    _ -> return Nothing
            _ -> return Nothing

class IsTupleEdge a where
   isTupleEdge :: a -> Bool

instance IsTupleEdge ConstraintInfo where
   isTupleEdge cinfo = 
      case (self . attribute . localInfo) cinfo of
         UHA_Expr (Expression_Tuple _ _) -> True
         UHA_Pat  (Pattern_Tuple _ _)    -> True
         _                               -> False

tupleHeuristic :: Fresh m => VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
tupleHeuristic = SingleVoting "Tuple heuristics" f
      where      
         f pair@(constraint , eid, info)    
            | not (isTupleEdge info) = return Nothing
            | otherwise              =
               case constraint of
                  Constraint_Unify t1 t2 _ ->
                     doWithoutEdge eid $ 
                  
                        do   
                           MType mTupleTp <- getSubstType $ MType t1
                           MType mExpectedTp <- getSubstType $ MType t2        
                           axioms <- getAxioms            
                           case (leftSpine mTupleTp,leftSpine mExpectedTp) of 
                              ((MonoType_Con s,tupleTps), (MonoType_Con t,expectedTps))
                                 | isTupleConstructor s && isTupleConstructor t ->
                                    case compare (length tupleTps) (length expectedTps) of
                                    
                                       EQ -> -- try if a permutation can make the tuple types equivalent
                                          do
                                             let   perms = take heuristicsMAX (permutationsForLength (length tupleTps))
                                             notUnifiable <- isNothing <$> unifyTypes axioms [] [Constraint_Unify (monotypeTuple tupleTps) (monotypeTuple expectedTps) Nothing] []
                                             let   test perm = 
                                                      let   t1 = monotypeTuple tupleTps
                                                            t2 = monotypeTuple (permute perm expectedTps)
                                                      in isJust <$> unifyTypes axioms [] [Constraint_Unify t1 t2 Nothing] []
                                             testList <- filterM test perms
                                             case testList of
                                                p:_ | notUnifiable -> -- a permutation is possible!
                                                      let hint = fixHint "re-order elements of tuple"
                                                      in return $ Just 
                                                            (4, "tuple: permute with "++show p ++ show (mTupleTp, mExpectedTp), constraint, eid, hint info)
                                                _ -> return Nothing
                                                         
                                       compareVal -> do 
                                                   let cLst = take heuristicsMAX (zipWithHoles tupleTps expectedTps)
                                                   let wantedC = map (\(is, zl) -> (is, let (xs, ys) = unzip zl in Constraint_Unify (monotypeTuple xs) (monotypeTuple ys) Nothing)) cLst
                                                   lst <- mapM (\(is, c) -> (unifyTypes axioms [] [c] (getFreeVariables c)) >>= \r -> return (is, r)) wantedC
                                                   case lst of
                                                      [(is, _)] 
                                                            -> case compareVal of
                                                                  LT -> let hint = fixHint ("insert a "++prettyAndList (map (ordinal True. (+1)) is)++" element to the tuple")
                                                                        in return $ Just 
                                                                              (4, "tuple:insert "++show is, constraint, eid, hint info)
                                                                  GT -> let hint = fixHint ("remove "++prettyAndList (map (ordinal True . (+1)) is)++" element of tuple")
                                                                        in return $ Just 
                                                                              (4, "tuple:remove "++show is, constraint, eid, hint info)
                                                                  EQ -> error "this cannot occur"            
                                                      _    -> let hint = becauseHint ("a "++show (length tupleTps)++"-tuple does not match a "++show (length expectedTps)++"-tuple")
                                                               in return $ Just 
                                                                     (2, "different sizes of tuple", constraint, eid, hint info)
                              _ -> return Nothing  
                  _ -> return Nothing


fbHasTooManyArguments :: Fresh m => VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
fbHasTooManyArguments = SingleVoting "Function binding heuristics" f
   where
      f (constraint, eid, info)   
         | not (isExplicitlyTyped info) = return Nothing
         | otherwise                    =  
            case constraint of
               Constraint_Inst t1 t2 _ -> do 
                  graph <- getGraph
                  let edge = getEdgeFromId graph eid
                  doWithoutEdge eid $ 
                     do 
                        MType m1 <- getSubstType $ MType t1
                        PType p2 <- getSubstType $ PType t2
                        maximumExplicit <- arityOfPolyType p2
                        edgeList <- getNeighbours (from edge) 
                        let maybeNumberOfPatterns = 
                                 case mapMaybe (\e -> getConstraintInfo (getConstraintFromEdge e) >>= maybeFunctionBinding) $ filter isConstraintEdge edgeList of 
                                    [i] -> Just i
                                    _   -> Nothing
                                                      
                        case maybeNumberOfPatterns of
                           Just n | n > maximumExplicit -> 
                              let   msg = "the function binding has "++prettyPat n++", but its type signature "++prettyArg maximumExplicit
                                    prettyPat i = if i == 1 then "1 pattern" else show i++" patterns"
                                    prettyArg 0 = "does not allow patterns"
                                    prettyArg x = "allows at most "++show x
                                    hint = becauseHint msg
                              in return $ Just 
                                    (8, "function binding has too many arguments", constraint, eid, hint info)
                           _ -> return Nothing
               _ -> return Nothing


constraintFromUser :: Fresh m => Path m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo -> VotingHeuristic m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo
constraintFromUser (Path _ path) = MultiVoting "Constraints from .type file" (helper $ map ignoreGraphModifier path)
   where
      helper path' edges = 
         let
            bestEdge = let lst = selectBestEdge path' in if null lst then Nothing else Just (maximum lst)
            edgeNrs  = [ i | (_, i, _) <- edges ]
            
            selectBestEdge :: [(Constraint ConstraintInfo, EdgeId, ConstraintInfo)] -> [EdgeId]
            selectBestEdge path' = [eid | (constraint, eid, ci) <- path', isJust (maybeUserConstraint ci), eid `elem` edgeNrs]

            f :: (a -> a -> a) -> Maybe a -> Maybe a -> Maybe a            
            f g ma mb = 
               case (ma, mb) of
                  (Just a, Just b) -> Just (g a b)
                  (Nothing, _    ) -> mb
                  _                -> ma
         in 
            case [ tuple | tuple@(_, cNR, _) <- edges, Just cNR == bestEdge ] of
               [] -> return Nothing
               (constraint, edgeID, info):_ -> 
                  let   (groupID, number) = fromMaybe (0, 0) (maybeUserConstraint info)
                        otherEdges = let p info' =
                                          case maybeUserConstraint info' of
                                             Just (a, b) -> a == groupID && b > number
                                             Nothing     -> False
                                    in [ e | (c, e, i) <- edges, p i ] -- perhaps over all edges!
                  in return . Just $
                        (8, "constraints from .type file", [], edgeID:otherEdges, info)