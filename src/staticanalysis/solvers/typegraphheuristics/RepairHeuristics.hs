module RepairHeuristics (repairHeuristics) where

import SolveTypeGraph
import IsTypeGraph
import Heuristics
import TypeGraphConstraintInfo
import SolveState
import Types
import TypeErrors
import Messages
import UHA_Syntax
import IsSolver
import EquivalenceGroup
import FixpointSolveState
import List 
import Maybe 

type RepairHeuristics m info = [RepairHeuristic m info]
type RepairHeuristic  m info = EdgeID -> info -> m (Maybe (Int, HeuristicActions, String))

repairHeuristics :: IsTypeGraph (TypeGraph info) info => RepairHeuristics (TypeGraph info) info
repairHeuristics = 
   [ fbHasTooManyArguments                                  
   , similarLiterals
   , similarNegation
   , tupleEdge
   , siblingFunctions                 
   , applicationEdge
   , variableFunction
   ]

----------------------------------------------------------------

siblingFunctions :: (IsTypeGraph m info, MonadState (SolveState m info a) m) => RepairHeuristic m info
siblingFunctions edge@(EdgeID v1 v2) info = 
   case maybeImportedFunction info of 
      Nothing   -> return Nothing
      Just name ->
      
         do siblings <- getSiblings
            let string    = show name
                functions = filter ( (string /=) . fst)
                          . concat
                          . filter ( (string `elem`) .  map fst)
                          $ siblings
                          
            if null functions 
              then return Nothing
              else doWithoutEdge (edge,info) $ 

                   do synonyms <- getTypeSynonyms
                      (_, mtp) <- getSubstitutedTypes info
                                        
                      case mtp of 
                      
                         Nothing -> 
                            return Nothing
                            
                         Just tp -> 
                            case filter (unifiable synonyms tp . unsafeInstantiate . snd) functions of
                               [(s, scheme)] -> let hint = fixHint ("use "++s++" instead")
                                                    msg  = show name++" is similar to "++show s
                                                in return (Just (10, [hint], msg))
                               _             -> return Nothing
                               
similarLiterals :: (IsTypeGraph m info, MonadState (SolveState m info a) m) => RepairHeuristic m info
similarLiterals edge info = 
   case maybeLiteral info of 
      Nothing      -> return Nothing
      Just literal ->

         doWithoutEdge (edge,info) $

            do synonyms <- getTypeSynonyms
               (_, mtp) <- getSubstitutedTypes info

               case (literal,mtp) of

                  (Literal_Int    _ s,Just (TCon "Float"))
                       -> let hint = fixHint "use a float literal instead"
                          in return (Just (5, [hint], "int literal should be a float"))

                  (Literal_Float  _ s,Just (TCon "Int"  ))
                       -> let hint = fixHint "use an int literal instead"
                          in return (Just (5, [hint], "float literal should be an int"))

                  (Literal_Char   _ s,Just (TApp (TCon "[]") (TCon "Char"))) 
                       -> let hint = fixHint "use a string literal instead"
                          in return (Just (5, [hint], "char literal should be a string"))

                  (Literal_String _ s,Just (TCon "Char"))   
                       -> let hint = fixHint "use a char literal instead"
                          in return (Just (5, [hint], "string literal should be a char"))

                  _ -> return Nothing                               
                  
similarNegation :: (IsTypeGraph m info, MonadState (SolveState m info a) m) => RepairHeuristic m info
similarNegation edge@(EdgeID v1 v2) info =
   case maybeNegation info of
      Nothing            -> return Nothing
      Just isIntNegation ->

         doWithoutEdge (edge,info) $

            do synonyms <- getTypeSynonyms
               (_, mtp) <- getSubstitutedTypes info
               
               case mtp of
                  Just tp
                     | floatNegationEdge && intNegation && not floatNegation
                        -> let hint = fixHint "use int negation (-) instead"
                           in return (Just (6, [hint], "int negation should be used"))

                     | intNegationEdge && not intNegation && floatNegation 
                        -> let hint = fixHint "use float negation (-.) instead"
                           in return (Just (6, [hint], "float negation should be used"))
                     
                    where intNegation       = unifiable synonyms tp (intType .->. intType)
                          floatNegation     = unifiable synonyms tp (floatType .->. floatType)
                          intNegationEdge   = isIntNegation
                          floatNegationEdge = not isIntNegation                                           

                  _ -> return Nothing                  

         
      
applicationEdge :: (IsTypeGraph m info, MonadState (SolveState m info a) m, IsSolver m info) => RepairHeuristic m info
applicationEdge edge@(EdgeID v1 v2) info =
   case maybeApplicationEdge info of
      Nothing                            -> return Nothing
      Just (isBinary,tuplesForArguments) ->

       doWithoutEdge (edge,info) $

          do let isPatternApplication = isPattern info 
             synonyms <- getTypeSynonyms                 
             (maybeFunctionType, maybeExpectedType) <- getSubstitutedTypes info
             
             case (maybeFunctionType,maybeExpectedType) of

               (Just functionType,Just expectedType) 

                  -- the expression to which arguments are given does not have a function type
                  | maybe False (<= 0) maximumForFunction && not isBinary && not isPatternApplication ->                       
                       let hint = becauseHint "it is not a function"
                       in return (Just (6, [hint], "no function"))
                  
                  -- function used as infix that expects < 2 arguments
                  | maybe False (<= 1) maximumForFunction && isBinary && not isPatternApplication ->
                       let hint = becauseHint "it is not a binary function"
                       in return (Just (6, [hint], "no binary function"))

                  -- can a permutation of the arguments resolve the type inconsistency
                  | length argumentPermutations == 1 -> 
                       let p = head argumentPermutations
                       in 
                         if p==[1,0] && isBinary
                            then 
                                 let hint = fixHint "swap the two arguments"
                                 in return (Just (3, [hint], "swap the two arguments"))
                            else                                       
                                  let hint = fixHint "re-order arguments"
                                  in return (Just (1, [hint], ("application: permute with "++show p)))
                                
                  -- is there one particular argument that is inconsistent
                  | length incorrectArguments == 1  ->
                      do let (t1, t2) = getTwoTypes info
                         fullTp <- applySubst t1 -- ???
                         let i = head incorrectArguments
                             (oneLiner,tp,range) = tuplesForArguments !! i
                             typeError     = makeTypeErrorForTerm (isBinary,isPatternApplication) i oneLiner (tp,expargtp) range info
                             expargtp      = fst (functionSpine fullTp) !! i
                         return (Just (3, [SetTypeError typeError], ("incorrect argument of application="++show i)))                         
                  
                  -- too many arguments are given
                  | maybe False (< numberOfArguments) maximumForFunction && not isPatternApplication ->
                       case typesZippedWithHoles of

                          -- there is only one possible set to remove arguments 
                          [is] | not isBinary
                              -> let hint = fixHint ("remove "++prettyAndList (map (ordinal True . (+1)) is)++" argument")
                                 in return (Just (4, [hint], ("too many arguments are given: "++show is)))

                          -- more than one or no possible set of arguments to be removed
                          _   -> let hint = becauseHint "too many arguments are given"
                                 in return (Just (2, [hint], "too many arguments are given"))
                                          
                  -- not enough arguments are given
                  | minimumForContext > numberOfArguments && not isPatternApplication && contextIsUnifiable ->
                       case typesZippedWithHoles of

                          [is] | not isBinary 
                              -> let hint = fixHint ("insert a "++prettyAndList (map (ordinal True . (+1)) is)++" argument")
                                 in return (Just (4, [hint], ("not enough arguments are given"++show is)))

                          _   -> let hint = becauseHint "not enough arguments are given"
                                 in return (Just (2, [hint], "not enough arguments are given"))                       

                where unifiableTypeLists :: Tps -> Tps -> Bool
                      unifiableTypeLists xs ys = unifiable synonyms (tupleType xs) (tupleType ys)   

                      -- number of arguments for this function application
                      numberOfArguments = length tuplesForArguments         
                                
                      -- (->) spines for function type and expected type for the given number of arguments
                      (functionArguments, functionResult) = functionSpineOfLength numberOfArguments functionType
                      (expectedArguments, expectedResult) = functionSpineOfLength numberOfArguments expectedType

                      -- (->) spines for function type and expected type ignoring the given number of arguments                      
                      (allFunctionArgs, allFunctionRes) = functionSpine functionType
                      (allExpectedArgs, allExpectedRes) = functionSpine expectedType
                      
                      -- maximum number of arguments for the function type (result type should not be polymorphic!)
                      --   e.g.: (a -> b) -> [a] -> [b]             yields (Just 2)
                      --         (a -> b -> b) -> b -> [a] -> b     yields Nothing
                      maximumForFunction = case functionSpine functionType of
                                              (_, TVar _) -> Nothing
                                              (tps, _   ) -> Just (length tps)
                      
                      -- minimum number of arguments that should be applied to the function to meet the expected context type
                      minimumForContext = length allFunctionArgs + numberOfArguments - length allExpectedArgs
                      
                      -- is the context unifiable?
                      contextIsUnifiable    = unifiable synonyms expectedResult (snd (functionSpineOfLength minimumForContext functionType))

                      -- is there one argument in particular that is incorrect?                                  
                      incorrectArguments = [ i 
                                           | length functionArguments == length expectedArguments 
                                           , i <- [0..numberOfArguments-1]
                                           , not (unifiable synonyms (functionArguments !! i) (expectedArguments !! i))
                                           , unifiableTypeLists (functionResult : deleteIndex i functionArguments) 
                                                                (expectedResult : deleteIndex i expectedArguments)
                                           ]

                      -- is there a permutation of the arguments that resolves the type inconsistency?
                      argumentPermutations = [ p 
                                             | length functionArguments == length expectedArguments 
                                             , p <- take heuristics_MAX (permutationsForLength numberOfArguments)
                                             , unifiableTypeLists (functionResult : functionArguments) 
                                                                  (expectedResult : permute p expectedArguments) 
                                             ]         ;                                                                

                      -- at which locations should an extra argument be inserted?
                      typesZippedWithHoles  = [ is 
                                              | (is,zl) <- take heuristics_MAX (zipWithHoles allFunctionArgs allExpectedArgs)
                                              , let (as,bs) = unzip zl
                                              , unifiableTypeLists (allFunctionRes : as) 
                                                                   (allExpectedRes : bs)
                                              ]                     

               _ -> return Nothing
                                                       
tupleEdge :: (IsTypeGraph m info, MonadState (SolveState m info a) m, IsSolver m info) => RepairHeuristic m info
tupleEdge edge@(EdgeID v1 v2) info
   | not (isTupleEdge info) = return Nothing
   | otherwise              =
   
   doWithoutEdge (edge,info) $ 
   
      do synonyms <- getTypeSynonyms                         
         (mTupleTp, mExpectedTp) <- getSubstitutedTypes info
         
         case (fmap leftSpine mTupleTp,fmap leftSpine mExpectedTp) of 

          (Just (TCon s,tupleTps),Just (TCon t,expectedTps)) | isTupleConstructor s && isTupleConstructor t ->
            case compare (length tupleTps) (length expectedTps) of
            
               EQ -> -- try if a permutation can make the tuple types equivalent
                     case [ p 
                          | p <- take heuristics_MAX (permutationsForLength (length tupleTps))
                          , unifiable synonyms (tupleType tupleTps) (tupleType (permute p expectedTps))
                          ] of
                       p:_  ->  -- a permutation possible!
                               let hint = fixHint "re-order elements of tuple"
                               in return (Just (4, [hint], ("tuple: permute with "++show p)))
                       _    -> return Nothing                       
            
               compare -> case [ is 
                               | (is,zl) <- take heuristics_MAX (zipWithHoles tupleTps expectedTps)
                               , let (xs, ys) = unzip zl in unifiable synonyms (tupleType xs) (tupleType ys)
                               ] of
                       [is] -> case compare of
                                 LT -> let hint = fixHint ("insert a "++prettyAndList (map (ordinal True. (+1)) is)++" element to the tuple")
                                       in return (Just (4, [hint], ("tuple:insert "++show is)))
                                 GT -> let hint = fixHint ("remove "++prettyAndList (map (ordinal True . (+1)) is)++" element of tuple")
                                       in return (Just (4, [hint], ("tuple:remove "++show is)))
                       _    -> let hint = becauseHint ("a "++show (length tupleTps)++"-tuple does not match a "++show (length expectedTps)++"-tuple")
                               in return (Just (2, [hint], "different sizes of tuple"))
          _ -> return Nothing                  
          
fbHasTooManyArguments :: IsTypeGraph (TypeGraph info) info => RepairHeuristic (TypeGraph info) info
fbHasTooManyArguments edge info 
   | not (isExplicitTypedBinding info) = return Nothing
   | otherwise                         =

      do synonyms <- getTypeSynonyms
         let (t1,t2)         = getTwoTypes info
             maximumExplicit = arityOfTp (expandType (snd synonyms) t1)
             tvar            = head (ftv t2)
         eqgroup <- equivalenceGroupOf tvar             
         let edgeinfos       = [ info | (EdgeID v1 v2,info) <- edges eqgroup, (v1==tvar || v2==tvar) ]                      
             maybeNumberOfPatterns = case [ i | Just i <- map maybeFunctionBinding edgeinfos] of 
                                        [i] -> Just i
                                        _   -> Nothing
         case maybeNumberOfPatterns of
            Just n | n > maximumExplicit -> let msg = "the function binding has "++prettyPat n++", but its type signature "++prettyArg maximumExplicit
                                                prettyPat i = if i == 1 then "1 pattern" else show i++" patterns"
                                                prettyArg 0 = "does not allow patterns"
                                                prettyArg n = "allows at most "++show n
                                                hint = becauseHint msg
                                            in return (Just (8, [hint], "function binding has too many arguments"))
            _                            -> return Nothing

variableFunction :: IsTypeGraph (TypeGraph info) info => RepairHeuristic (TypeGraph info) info
variableFunction edge info
   | not (isExprVariable info)
        = return Nothing
   | otherwise 
        = doWithoutEdge (edge,info) $ 
            
           do synonyms   <- getTypeSynonyms
              (mt1, mt2) <- getSubstitutedTypes info
              
              -- is this variable involved in an application?
              let EdgeID v1 v2 = edge
              edges1 <- getAdjacentEdges v1
              edges2 <- getAdjacentEdges v2
              let f (EdgeID v1 v2) = [v1,v2]
              let special = concatMap (f . fst) (filter (isEmptyInfixApplication . snd) (edges1 ++ edges2)) \\ [v1,v2]
              edges3 <- mapM getAdjacentEdges special
              let isApplicationEdge = isJust . maybeApplicationEdge
                  application = any (isApplicationEdge . snd) (edges1 ++ edges2 ++ concat edges3)                                                               
              
              case (mt1, mt2) of
                 (Just functionType, Just expectedType) | not application -> 
                    let maxArgumentsForFunction = length (fst (functionSpine functionType))
                        minArgumentsForContext  = maxArgumentsForFunction - length (fst (functionSpine expectedType)) 
                        contextIsUnifiable      = unifiable synonyms 
                                                     (snd $ functionSpineOfLength minArgumentsForContext functionType)
                                                     expectedType
                    in if minArgumentsForContext <= 0 || not contextIsUnifiable
                         then return Nothing
                         else let hint = fixHint ("insert "++showNumber minArgumentsForContext++" argument"++
                                              if minArgumentsForContext <= 1 then "" else "s")
                              in return (Just (4, [hint], ("insert arguments to function variable")))
                 _                       -> return Nothing                   

{-
considerUnifierVertices :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => 
                               [(EdgeID, info)] -> SolveState EquivalenceGroups info [(HeuristicResult, (EdgeID, info))]
considerUnifierVertices xs = 
   do let is = nub [ i | Just i <- map (maybeUnifier . snd) xs ]
      results <- mapM unifierVertex is
      return (concat results)

 where
  unifierVertex :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => 
                       Int -> SolveState EquivalenceGroups info [(HeuristicResult, (EdgeID, info))]
  unifierVertex unifier =
     do allEdgesAdjacentToUnifier <- getAdjacentEdges unifier
        doWithoutEdges allEdgesAdjacentToUnifier $

           do options     <- getSolverOptions
              let synonyms = getTypeSynonyms options
              
              allMaybePairs <- let f pair@((EdgeID v1 v2), _) = 
                                      do let tp | v1 == unifier = TVar v2
                                                | otherwise     = TVar v1
                                         mtp <- safeApplySubst tp
                                         return (mtp, pair) 
                               in mapM f allEdgesAdjacentToUnifier 
              if any (isNothing . fst) allMaybePairs                   
                then return []
                else let allPairs = [ (x, y) | (Just x, y) <- allMaybePairs ] 
                         (typeVariablePairs, rest) = partition (isTVar . fst) allPairs
                         allConstantGroupsSorted@(firstGroup : otherGroups) = 
                            let rec []     = []
                                rec (x:xs) = let (as,bs) = foldr op ([x],[]) xs
                                             in as : rec bs
                                op p (as,bs) 
                                   | unifiableTps synonyms (map fst (p:as)) = (p:as,bs)
                                   | otherwise                              = (as,p:bs)
                                comparer xs ys = length ys `compare` length xs -- reversed!
                            in sortBy comparer (rec rest)
                            
                         predicate = maybe False (unifier==) . maybeUnifier . snd . snd
                         majority  = not (null otherGroups) && length firstGroup > length (concat otherGroups)
                         result 
                          | null otherGroups
                               = []
                          | majority
                               = let (incorrectBranch, incorrectContext) = partition predicate (concat otherGroups)
                                 in case length incorrectBranch of
                                       0 -> []
                                       1 -> if null incorrectContext
                                              then [(ModifierHeuristic 100.0 "only branch incorrect in majority", snd $ head incorrectBranch)]
                                              else undefined
                                       n -> error "n"
                                     -- 0 branches (alleen contexten)
                                     -- alleen 1 branch
                                     -- > 1 branch (takeover)
                          | otherwise 
                               = error "there is no majority"
                                  
                         
                     in return result
-}             


showNumber :: Int -> String
showNumber i | i <= 10 && i >=0 = list !! i
             | otherwise        = show i
   where list = [ "zero", "one", "two", "three", "four", "five"
                , "six", "seven", "eight", "nine", "ten" ]      

getAdjacentEdges :: Int -> TypeGraph info [(EdgeID, info)]
getAdjacentEdges vertexID =   
   do eqc <- equivalenceGroupOf vertexID
      let predicate (EdgeID v1 v2) = v1 == vertexID || v2 == vertexID
      return (filter (predicate . fst) (edges eqc))

heuristics_MAX        =    120 :: Int

zipWithHoles :: [a] -> [b] -> [ ( [Int] , [(a,b)] ) ] 
zipWithHoles = rec 0 where

   rec i [] bs = [ (take (length bs) [i..] , []) ]
   rec i as [] = [ (take (length as) [i..] , []) ]
   rec i (a:as) (b:bs) = case compare (length as) (length bs) of
         LT -> [ (  is,(a,b):zl) | (is,zl) <- rec (i+1) as     bs ]
            ++ [ (i:is,      zl) | (is,zl) <- rec (i+1) (a:as) bs ]
         EQ -> [ ([],zip (a:as) (b:bs)) ] 
         GT -> [ (  is,(a,b):zl) | (is,zl) <- rec (i+1) as bs     ]
            ++ [ (i:is,      zl) | (is,zl) <- rec (i+1) as (b:bs) ]

  


becauseHint, fixHint :: String -> HeuristicAction
becauseHint = SetHint . TypeErrorHint "because"     . MessageString
fixHint     = SetHint . TypeErrorHint "probable fix". MessageString

type Permutation = [Int]

permutationsForLength :: Int -> [Permutation]
permutationsForLength 0     = [ [] ]
permutationsForLength (i+1) = [ ys | xs <- permutationsForLength i, ys <- insertSomewhere i xs ]

   where insertSomewhere i []     = [ [i] ]
         insertSomewhere i (x:xs) = (i:x:xs) : map (x:) (insertSomewhere i xs)
         
permute :: Permutation -> [a] -> [a]
permute is as = map (as !!) is

deleteIndex :: Int -> [a] -> [a]
deleteIndex _ []     = []
deleteIndex 0 (a:as) = as
deleteIndex i (a:as) = a : deleteIndex (i-1) as
