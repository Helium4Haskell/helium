-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypeGraphHeuristics.hs : Heuristics to make a type graph consistent.
--    !!! CLEAN UP THIS CODE !!!
--
-------------------------------------------------------------------------------

module TypeGraphHeuristics (heuristics) where

import EquivalenceGroup
import SolveEquivalenceGroups
import SolveTypeGraph
import TypeGraphConstraintInfo
import SolveConstraints
import SolveState
import Messages
import TypeErrors
import Types
import List
import ConstraintInfo
import SolverOptions        ( getTypeSynonyms, getTypeSignatures )
import Utils                ( internalError )
import SimilarFunctionTable ( similarFunctionTable )
import UHA_Utils            ( nameFromString )
import UHA_Syntax           ( Literal(..), Range(..), Position(..) )
import Monad                ( unless, when, filterM )
import Int                  ( fromInt )
import Maybe                ( catMaybes, isJust )
import InfiniteTypeHeuristic  -- (infiniteTypeHeuristic, safeMaximumBy, safeMinimumBy)
 
import IOExts -- for debugging

heuristics_MAX        =    120 :: Int
upperbound_GOODPATHS  =     50 :: Int
upperbound_ERRORPATHS =     50 :: Int
testMode              = False  :: Bool

heuristics :: (TypeGraph EquivalenceGroups info, TypeGraphConstraintInfo info, Show info) => 
              SolveState EquivalenceGroups info ([EdgeID], [info])
heuristics = do conflicts <- getConflicts
                let clashes   = [ i | (ConstantClash, i) <- conflicts ]
                    infinites = [ i | (InfiniteType , i) <- conflicts ]
                if null infinites
                  then heuristicsConstantClash clashes
                  else infiniteTypeHeuristic infinites
                        
heuristicsConstantClash :: (TypeGraph EquivalenceGroups info, TypeGraphConstraintInfo info, Show info) => 
                           [Int] -> SolveState EquivalenceGroups info ([EdgeID], [info])
heuristicsConstantClash is = 

   do pathsWithInfo    <- findPathsInTypeGraph is
      let edgeInfoTable = makeEdgeInfoTable pathsWithInfo
          allEdges      = map fst edgeInfoTable
          
      addDebug . putStrLn  . unlines $ 
         ("*** Error Paths in Type Graph ***\n") : 
         zipWith (\i p -> "Path #"++show i++"\n"++replicate 25 '='++"\n"++showPath p) [1..] [ p | (p, (_, _, False)) <- pathsWithInfo ]    

      maxPhaseEdges          <- applyEdgesFilter constraintPhaseFilter allEdges  
      maybeUserConstraint    <- applyEdgesFilter (maybeUserConstraintFilter pathsWithInfo) maxPhaseEdges      
      maxDifferentGroupEdges <- applyEdgesFilter (differentGroupsFilter edgeInfoTable) maybeUserConstraint                           
          
      let applyHeuristicsToEdge (edge, info) = 
             do xs <- mapM (\heuristic -> heuristic edge info) (errorAndGoodPaths edgeInfoTable : edgeheuristics)
                return (foldr combineHeuristicResult NotApplicableHeuristic xs)
      
      bestForEachEdge <- mapM (\t -> do r <- applyHeuristicsToEdge t ; return (r,t) ) maxDifferentGroupEdges
      let sortedList = sortBy (\x y -> fst x `compare` fst y) bestForEachEdge

      addDebug . putStrLn . unlines $ 
         ("*** Best heuristics for each edge ***\n") : 
         (map (\(r,t) -> take 15 (show (fst t)++repeat ' ')++show r) sortedList)               
         
      let (hresult,(edge,info))     | null sortedList = internalError "TypeGraphHeurisitics" "heuristicsConstantClash" "empty list(2)" 
                                    | otherwise       = last sortedList
      
      standardEdges <- moreEdgesFromUser info edge                                    
      
      let standard                  = (info,standardEdges)
          (typeError,edgesToRemove) = case hresult of 
             ConcreteHeuristic _ as _ -> let op action (te,es) = case action of 
                                                                    SetHint h      -> (setNewHint h te,es)
                                                                    SetTypeError t -> (setNewTypeError t te,es)
                                                                    RemoveEdge e   -> (te,e:es)
                                         in foldr op standard as
             _                        -> standard
          
      return (edgesToRemove, [typeError])

data HeuristicResult = ConcreteHeuristic Int [HeuristicAction] String
                     | ModifierHeuristic Float String
                     | NotApplicableHeuristic

data HeuristicAction = SetHint      TypeErrorInfo
                     | SetTypeError TypeError
                     | RemoveEdge   EdgeID

fixHint :: String -> TypeErrorInfo
fixHint = TypeErrorHint "Probable fix". MessageString

becauseHint :: String -> TypeErrorInfo
becauseHint = TypeErrorHint "Because" . MessageString

instance Show HeuristicResult where
   show (ConcreteHeuristic i h s) = "trust="++show i++"   ("++s++")"
   show (ModifierHeuristic f s)   = "modifier="++show f++"   ("++s++")"
   show (NotApplicableHeuristic)  = "not applicable" 

instance Eq HeuristicResult where
   ConcreteHeuristic i _ _ == ConcreteHeuristic j _ _ = i == j       
   ModifierHeuristic _ _   == ModifierHeuristic _ _   = True
   NotApplicableHeuristic  == NotApplicableHeuristic  = True
   _                       == _                       = False       
   
instance Ord HeuristicResult where     
   NotApplicableHeuristic  `compare` NotApplicableHeuristic  = EQ
   NotApplicableHeuristic  `compare` _                       = LT
   _                       `compare` NotApplicableHeuristic  = GT
   ConcreteHeuristic i _ _ `compare` ConcreteHeuristic j _ _ = i `compare` j 
   ConcreteHeuristic i _ _ `compare` ModifierHeuristic _ _   = GT
   ModifierHeuristic _ _   `compare` ConcreteHeuristic j _ _ = LT  
   ModifierHeuristic x _   `compare` ModifierHeuristic y _   = x `compare` y

combineHeuristicResult :: HeuristicResult -> HeuristicResult -> HeuristicResult
combineHeuristicResult hr1 hr2 =
   case (hr1, hr2) of
      (ModifierHeuristic f1 s1, ModifierHeuristic f2 s2) -> ModifierHeuristic (f1 * f2) (s1++";"++s2)
      _                                                  -> hr1 `max` hr2
                     
-------------------------------------------------------------------------------
-- Edge Heuristics

type EdgeHeuristic info = EdgeID -> info -> SolveState EquivalenceGroups info HeuristicResult

edgeheuristics :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => [EdgeHeuristic info]
edgeheuristics = [ orderOfUnification 
                 , minimizeSizeOfExpression
                 , trustFactorOfConstraint
                 , isFolkloreEdge
                 , edgeIsPartOfCycle
                 , fbHasTooManyArguments                                  
                 , similarLiterals
                 , similarNegation
                 , tupleEdge
                 , similarFunctions                 
                 , applicationEdge
                 ]

orderOfUnification :: TypeGraphConstraintInfo info => EdgeHeuristic info
orderOfUnification edge info =
   case getPosition info of
      Nothing       -> return NotApplicableHeuristic
      Just position -> let modifier = 1 + fromInt position / 10000
                       in return (ModifierHeuristic modifier ("position="++show position))

minimizeSizeOfExpression :: TypeGraphConstraintInfo info => EdgeHeuristic info
minimizeSizeOfExpression edge info = 
   case getSize info of
      Nothing   -> return NotApplicableHeuristic
      Just size -> let modifier = 0.95 ^ size
                   in return (ModifierHeuristic modifier ("size="++show size))
  
trustFactorOfConstraint :: TypeGraphConstraintInfo info => EdgeHeuristic info
trustFactorOfConstraint edge info = 
   case getTrustFactor info of
      Nothing    -> return NotApplicableHeuristic
      Just trust -> let modifier = 1 / fromInt trust
                    in return (ModifierHeuristic modifier ("trustfactor="++show trust))

isFolkloreEdge :: TypeGraphConstraintInfo info => EdgeHeuristic info
isFolkloreEdge edge info 
   | isFolkloreConstraint info = return (ModifierHeuristic 0.5 "folklore")
   | otherwise                 = return NotApplicableHeuristic

-- not a complete definition!!! An implied edge can also be a part of a cycle. In this
-- case the initial edges should also be considered as cyclic.
edgeIsPartOfCycle :: TypeGraphConstraintInfo info => EdgeHeuristic info
edgeIsPartOfCycle edge@(EdgeID v1 v2) info = 
   useSolver 
      (\groups -> do eqc <- equivalenceGroupOf v1 groups
                     if length (splitGroup (removeEdge edge eqc)) < 2
                       then return (ModifierHeuristic 0.2 "part of a cycle")
                       else return NotApplicableHeuristic)

similarFunctions :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => EdgeHeuristic info
similarFunctions edge@(EdgeID v1 v2) info = 
   case maybeImportedFunction info of 
      Nothing   -> return NotApplicableHeuristic
      Just name -> 
      
         let (t1,t2)   = getTwoTypes info 
             string    = show name
             functions = filter (string /=)
                       . concat 
                       . filter (string `elem`) 
                       $ similarFunctionTable
         in if null functions 
              then return NotApplicableHeuristic
              else do options <- getSolverOptions 
                      let tryFunctions = map (\s -> (s, lookup s importedFunctions)) functions  
                          importedFunctions = getTypeSignatures options 
                          synonyms = getTypeSynonyms options
                                                                 
                      doWithoutEdge (edge,info) $ 
                      
                         do unique   <- getUnique
                            mtp      <- safeApplySubst t2
                            
                            case mtp of 
                               Nothing -> return NotApplicableHeuristic
                               Just tp -> case [ ConcreteHeuristic 10 [SetHint (fixHint ("use "++s++" instead"))] (show string++" is similar to "++show s)
                                               | (s,Just scheme) <- tryFunctions                                                   
                                               , unifiable synonyms tp (unsafeInstantiate scheme) 
                                               ] of
                                            []  -> return NotApplicableHeuristic
                                            t:_ -> return t   

similarLiterals :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => EdgeHeuristic info
similarLiterals edge@(EdgeID v1 v2) info = 
   case maybeLiteral info of 
      Nothing      -> return NotApplicableHeuristic
      Just literal -> 
         
         doWithoutEdge (edge,info) $
         
            do options  <- getSolverOptions
               let (t1,t2)   = getTwoTypes info                                         
                   synonyms  = getTypeSynonyms options
               unique   <- getUnique
               mtp      <- safeApplySubst t2
               
               case (literal,mtp) of 

                  (Literal_Int    _ s,Just (TCon "Float"))  
                       -> let hint = SetHint (fixHint "use a float literal instead")
                          in return $ ConcreteHeuristic 5 [hint] "int literal should be a float"

                  (Literal_Float  _ s,Just (TCon "Int"  ))  
                       -> let hint = SetHint (fixHint "use an int literal instead")
                          in return $ ConcreteHeuristic 5 [hint] "float literal should be an int"

                  (Literal_Char   _ s,Just (TApp (TCon "[]") (TCon "Char"))) 
                       -> let hint = SetHint (fixHint "use a string literal instead")
                          in return $ ConcreteHeuristic 5 [hint] "char literal should be a string"

                  (Literal_String _ s,Just (TCon "Char"))   
                       -> let hint = SetHint (fixHint "use a char literal instead")
                          in return $ ConcreteHeuristic 5 [hint] "string literal should be a char"

                  _ -> return NotApplicableHeuristic

similarNegation :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => EdgeHeuristic info
similarNegation edge@(EdgeID v1 v2) info = 
   case maybeNegation info of 
      Nothing   -> return NotApplicableHeuristic
      Just beta -> 
      
         do xs <- useSolver 
                    (\groups -> do eqc <- equivalenceGroupOf beta groups
                                   return [ (edge,info) 
                                          | (edge@(EdgeID a b),info) <- edges eqc 
                                          , (a == beta || b == beta)
                                          , isNegationResult info
                                          ])
            case xs of 
               [(edge',info')] -> 
                  
                  doWithoutEdges [(edge,info),(edge',info')] $
                  
                  do options  <- getSolverOptions
                     let (t1,t2)   = getTwoTypes info                
                         synonyms  = getTypeSynonyms options
                     unique   <- getUnique
                     mt1      <- safeApplySubst t1
                     mt2      <- safeApplySubst (TVar beta)

                     case (mt1,mt2) of
                     
                          (Just t1,Just t2) 
                             | intNegation && not floatNegation -> let hint = SetHint (fixHint "use int negation (-) instead")
                                                                   in return $ ConcreteHeuristic 6 [RemoveEdge edge',hint] "int negation should be used"       
                             | floatNegation && not intNegation -> let hint = SetHint (fixHint "use float negation (-.) instead")
                                                                   in return $ ConcreteHeuristic 6 [RemoveEdge edge',hint] "float negation should be used"     
                             | otherwise                        -> return $ NotApplicableHeuristic
                               where intNegation   = unifiable synonyms t1 intType   && unifiable synonyms t2 intType
                                     floatNegation = unifiable synonyms t1 floatType && unifiable synonyms t2 floatType
                          _ -> return $ NotApplicableHeuristic
                  
               _ -> return NotApplicableHeuristic
            
applicationEdge :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => EdgeHeuristic info
applicationEdge edge@(EdgeID v1 v2) info = 
   case maybeApplicationEdge info of
      Nothing                            -> return NotApplicableHeuristic
      Just (isBinary,tuplesForArguments) -> 
      
       doWithoutEdge (edge,info) $      
       
          do options     <- getSolverOptions 
             let (t1,t2)  = getTwoTypes info                           
                 synonyms = getTypeSynonyms options
             mFunctionTp <- safeApplySubst t1    
             mExpectedTp <- safeApplySubst t2    
          
             case (mFunctionTp,mExpectedTp) of 
               
               (Nothing        ,_              ) -> return NotApplicableHeuristic
               (_              ,Nothing        ) -> return NotApplicableHeuristic
               (Just functionTp,Just expectedTp) -> 
 
                  let [(ftps,resFunction), (etps,resExpected)] = spineOfFunctionTypesWithSameLength [functionTp,expectedTp]           
                      predicate = uncurry (unifiable synonyms)
                                . applyBoth tupleType
                                . unzip
                               . ((resFunction,resExpected):)
                      onlyArgumentsMatch = unifiable synonyms (tupleType ftps) (tupleType etps)
                  in case compare (length ftps) (length etps) of 
 
                        LT | null ftps && not isBinary -> -- the expression to which arguments are given does not have a function type                            
                                let hint = SetHint (becauseHint "it is not a function")
                                in return (ConcreteHeuristic 6 [hint] "no function")
 
                           | length ftps < 2 && isBinary -> --function used as infix that expects < 2 arguments
                                let hint = SetHint (becauseHint "it is not a binary function")
                                in return (ConcreteHeuristic 6 [hint] "no binary function")
  
                        EQ | onlyArgumentsMatch && length ftps >= length tuplesForArguments -> -- error in result 
                                return (ModifierHeuristic 0.000001 "application: only result is incorrect")
                                
                           | not onlyArgumentsMatch -> -- test if there is one argument in particular that is incorrect                          
                           case ([ p
                                 | p <- take heuristics_MAX (permutationsForLength (length ftps))
                                 , predicate (zip ftps (permute p etps))
                                 ]
                                 ,[ i 
                                 | i <- [0..length ftps-1]
                                 , predicate (deleteIndex i (zip ftps etps)) 
                                 , not (unifiable synonyms (ftps !! i) (etps !! i)) 
                                 ]) of 
                            
                             ([p],_) 
                                 | p==[1,0] && isBinary -> let hint = SetHint (fixHint "swap the two arguments")
                                                           in return (ConcreteHeuristic 3 [hint] "swap the two arguments")
                                 | otherwise            -> let hint = SetHint (fixHint "re-order arguments")
                                                           in return (ConcreteHeuristic 1 [hint] ("application: permute with "++show p))
                         
                             (_,[i]) | i < length tuplesForArguments
                                  -> do expfulltp <- applySubst t1                                   
                                        let (oneLiner,tp) = tuplesForArguments !! i
                                            typeError     = makeTypeErrorForTerm oneLiner (tp,expargtp) info
                                            expargtp      = fst (functionSpine expfulltp) !! i
                                        return (ConcreteHeuristic 3 [SetTypeError typeError] ("incorrect argument of application="++show i))
                             _   -> return NotApplicableHeuristic
 
                        ordering -> -- the number of arguments is incorrect. (LT -> too many ; GT -> not enough)                           
                           case ( [ is | (is,zl) <- take heuristics_MAX (zipWithHoles ftps etps), predicate zl ] , ordering ) of 
                       
                             ([is],LT) | not isBinary && maximum is < length tuplesForArguments
                                -> let hint = SetHint (fixHint ("remove "++prettyAndList (map (ordinal . (+1)) is)++" argument"))
                                   in return (ConcreteHeuristic 4 [hint] ("too many arguments are given: "++show is))
 
                             (_:_ ,LT) 
                                -> let hint = SetHint (becauseHint "too many arguments are given")
                                   in return (ConcreteHeuristic 2 [hint] "too many arguments are given")
 
                             ([is],GT) | not isBinary
                                -> let hint = SetHint (fixHint ("insert a "++prettyAndList (map (ordinal . (+1)) is)++" argument"))
                                   in return (ConcreteHeuristic 4 [hint] ("not enough arguments are given"++show is)) 
 
                             (_:_ ,GT)
                                -> let hint = SetHint (becauseHint "not enough arguments are given")
                                   in return (ConcreteHeuristic 2 [hint] "not enough arguments are given")
 
                             _         -> return NotApplicableHeuristic
                                                       
tupleEdge :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => EdgeHeuristic info
tupleEdge edge@(EdgeID v1 v2) info
   | not (isTupleEdge info) = return NotApplicableHeuristic
   | otherwise              = 
   
   doWithoutEdge (edge,info) $ 
   
      do options     <- getSolverOptions
         let (t1,t2)  = getTwoTypes info                            
             synonyms = getTypeSynonyms options
         mTupleTp    <- safeApplySubst t1    
         mExpectedTp <- safeApplySubst t2
         case (fmap leftSpine mTupleTp,fmap leftSpine mExpectedTp) of 
             
          (Just (TCon s,tupleTps),Just (TCon t,expectedTps)) | isTupleConstructor s && isTupleConstructor t -> 
            case compare (length tupleTps) (length expectedTps) of
            
               EQ -> -- try if a permutation can make the tuple types equivalent
                     case [ p 
                          | p <- take heuristics_MAX (permutationsForLength (length tupleTps))
                          , unifiable synonyms (tupleType tupleTps) (tupleType (permute p expectedTps))
                          ] of
                       p:_  ->  -- a permutation possible!
                               let hint = SetHint (fixHint "re-order elements of tuple")
                               in return (ConcreteHeuristic 4 [hint] ("tuple: permute with "++show p)) 
                       _    -> return NotApplicableHeuristic                       
            
               compare -> case [ is 
                               | (is,zl) <- take heuristics_MAX (zipWithHoles tupleTps expectedTps)
                               , uncurry (unifiable synonyms) . applyBoth tupleType . unzip $ zl
                               ] of
                       [is] -> case compare of
                                 LT -> let hint = SetHint (fixHint ("insert a "++prettyAndList (map (ordinal . (+1)) is)++" element to the tuple"))
                                       in return (ConcreteHeuristic 4 [hint] ("tuple:insert "++show is)) 
                                 GT -> let hint = SetHint (fixHint ("remove "++prettyAndList (map (ordinal . (+1)) is)++" element of tuple"))
                                       in return (ConcreteHeuristic 4 [hint] ("tuple:remove "++show is))
                       _    -> let hint = SetHint (becauseHint ("a "++show (length tupleTps)++"-tuple does not match a "++show (length expectedTps)++"-tuple"))
                               in return (ConcreteHeuristic 2 [hint] "different sizes of tuple")
          _ -> return NotApplicableHeuristic

fbHasTooManyArguments :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => EdgeHeuristic info
fbHasTooManyArguments edge info 
   | not (isExplicitTypedBinding info) = return NotApplicableHeuristic
   | otherwise                         = 

      do options <- getSolverOptions
         let (t1,t2)         = getTwoTypes info
             maximumExplicit = arityOfTp (expandType (snd synonyms) t1)
             synonyms        = getTypeSynonyms options
         maybeNumberOfPatterns <- useSolver 
            (\groups -> do let tvar = head (ftv t2)
                           eqgroup <- equivalenceGroupOf tvar groups
                           let edgeinfos = [ info | (EdgeID v1 v2,info) <- edges eqgroup, (v1==tvar || v2==tvar) ] 
                           case [ i | Just i <- map maybeFunctionBinding edgeinfos] of 
                             [i] -> return (Just i)                            
                             _   -> return Nothing)
         case maybeNumberOfPatterns of
            Just n | n > maximumExplicit -> let msg = "the function binding has "++prettyPat n++", but its type signature "++prettyArg maximumExplicit
                                                prettyPat i = if i == 1 then "1 pattern" else show i++" patterns"
                                                prettyArg 0 = "does not allow patterns"
                                                prettyArg n = "allows at most "++show n
                                                hint = SetHint (becauseHint msg)
                                            in return (ConcreteHeuristic 8 [hint] "function binding has too many arguments")
            _                            -> return NotApplicableHeuristic

spineOfFunctionTypesWithSameLength :: Tps -> [(Tps,Tp)]
spineOfFunctionTypesWithSameLength = rec . map ((\(xs,x) -> xs ++ [x]) . functionSpine)
    
    where rec :: [Tps] -> [(Tps,Tp)]
          rec tpsList = if any ((==1) . length) tpsList 
                          then if allTheSame (map length (filter (not . isTVar) tpsList)) 
                                  then map (\tps -> ([],foldr1 (.->.) tps)) tpsList
                                  else map initAndLast tpsList
                          else zipWith zipf (map head tpsList) (rec $ map tail tpsList)
          
          isTVar [TVar _] = True
          isTVar _        = False
          
          zipf t1 (tps,t2) = (t1:tps,t2)

          allTheSame []     = True
          allTheSame (x:xs) = all (x==) xs
                        
applyBoth :: (a -> b) -> (a,a) -> (b,b)
applyBoth f (a,b) = (f a,f b)

deleteIndex :: Int -> [a] -> [a]
deleteIndex _ []     = []
deleteIndex 0 (a:as) = as
deleteIndex i (a:as) = a : deleteIndex (i-1) as

-- from old Helium-compiler....move to Utils or SAMessages?
ordinal :: Int -> String                                                                   
ordinal i                                                                                        
    | i >= 1 && i <= 10 = table !! (i - 1)                                                       
    | i > 10 = show i ++ extension i                                                             
    | otherwise = internalError "TypeGraphHeuristics.hs" "ordinal" "can't show numbers smaller than 1" 
    where                                                                                      
        table =                                                                                  
            [ "first", "second", "third", "fourth", "fifth", "sixth","seventh"                                                                                        
            , "eighth", "ninth", "tenth"                                                         
            ]                                                                                 
        extension i                                                                              
            | i < 20 = "th"                                                                      
            | i `mod` 10 == 1 = "st"                                                             
            | i `mod` 10 == 2 = "nd"                                                             
            | i `mod` 10 == 3 = "rd"                                                             
            | otherwise       = "th"

initAndLast :: [a] -> ([a],a)
initAndLast []    = internalError "TypeGraphHeuristics.hs" "initAndLast" "unexpected empty list"
initAndLast [t]   = ([],t)
initAndLast (h:t) = let (xs,x) = initAndLast t
                    in (h:xs,x)

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

doWithoutEdge :: TypeGraph EquivalenceGroups info => (EdgeID,info)
                                                  -> SolveState EquivalenceGroups info result
                                                  -> SolveState EquivalenceGroups info result
doWithoutEdge (edge@(EdgeID v1 v2),info) computation =
   do 
      testmax <- getUnique
      copy1 <- if testMode
                 then let f i = do useSolver (\g -> do e <- equivalenceGroupOf i g ; return e)
                      in mapM f [0..testmax - 1]
                 else return []
                 
      deleteEdge edge
      result <- computation 
      propagateEquality [v1,v2]
      addEdge edge (Initial info)

      copy2 <- if testMode
                 then let f i = do useSolver (\g -> do e <- equivalenceGroupOf i g ; return e)
                      in mapM f [0..testmax - 1]
                 else return []
      
      when (testMode) $
         let list = concat (zipWith (\a b -> if a==b then [] else [a,b]) copy1 copy2)                 
         in unless (null list) $ 
              internalError "TypeGraphHeuristics.hs" "doWithoutEdge" "security test failed"
    
      return result
                                             
doWithoutEdges :: TypeGraph EquivalenceGroups info => [(EdgeID,info)]
                                                   -> SolveState EquivalenceGroups info result
                                                   -> SolveState EquivalenceGroups info result
doWithoutEdges []     = id        
doWithoutEdges (x:xs) = doWithoutEdge x . doWithoutEdges xs            
                                           
safeApplySubst :: TypeGraph EquivalenceGroups info => Tp -> SolveState EquivalenceGroups info (Maybe Tp)
safeApplySubst tp = case tp of 
   TVar i     -> do vertices  <- getVerticesInGroup i
                    constants <- getConstantsInGroup i
                    children  <- getChildrenInGroup i
                    tps       <- case children of
                                    []       -> return [] 
                                    (_,is):_ -> mapM safeApplySubst (map TVar is)
                    let tp = case constants of 
                                []  -> Just . TVar . fst . head $ vertices
                                [s] -> Just (TCon s)
                                _   ->  Nothing
                    let tapp t1 t2 = case (t1,t2) of 
                                       (Just t1',Just t2') -> Just (TApp t1' t2')
                                       _                   -> Nothing
                    return (foldl tapp tp tps)
   TCon s     -> return (Just tp)
   TApp t1 t2 -> do mt1 <- safeApplySubst t1
                    mt2 <- safeApplySubst t2
                    case (mt1,mt2) of 
                      (Just t1',Just t2') -> return (Just $ TApp t1' t2')
                      _                   -> return Nothing
                      
fst4 (a,_,_,_) = a

type Permutation = [Int]

permutationsForLength :: Int -> [Permutation]
permutationsForLength 0     = [ [] ]
permutationsForLength (i+1) = [ ys | xs <- permutationsForLength i, ys <- insertSomewhere i xs ]

   where insertSomewhere i []     = [ [i] ]
         insertSomewhere i (x:xs) = (i:x:xs) : map (x:) (insertSomewhere i xs)
         
permute :: Permutation -> [a] -> [a]
permute is as = map (as !!) is

-- ook in SolveTypeGraph
combinations :: [a] -> [(a,a)]
combinations []     = []
combinations (a:as) = zip (repeat a) as ++ combinations as

-----------------------------------------------------------

type PathInfo            = ( (Int, Int)  -- (fromVertex, toVertex)
                           , Int         -- equivalence group of clash
                           , Bool        -- correct path?
                           )
type PathInfos           = [PathInfo]
type PathWithInfo cinfo  = (Path cinfo, PathInfo)
type PathsWithInfo cinfo = [PathWithInfo cinfo]
type EdgeInfoTable cinfo = [((EdgeID, cinfo), PathInfos)]

findPathsInTypeGraph :: TypeGraph solver cinfo => [Int] -> SolveState solver cinfo (PathsWithInfo cinfo)
findPathsInTypeGraph is = 
   let 
       rec (gp,ep) []          = return []
       rec (gp,ep) (i:is)      
          | gp <= 0 && ep <= 0 = return []
          | otherwise          = do (rgp1,rep1) <- recGroup (gp,ep) i 
                                    recPaths    <- rec (gp - length rgp1,ep - length rep1) is
                                    return (recPaths++rgp1++rep1)                
                                    
       recGroup tuple i =
          do vertices <- getVerticesInGroup i
          
             let f (gp,ep) []                       = return ([],[])
                 f (gp,ep) (((i1,s1),(i2,s2)):rest) 
                    | gp <= 0  && ep <= 0           = return ([],[])  
                    | s1 == s2 && gp <= 0           = f (gp,ep) rest
                    | s1 /= s2 && ep <= 0           = f (gp,ep) rest
                    | otherwise                     = 

                         do paths <- getPathsFrom i1 [i2]
                            if s1 == s2 
                              then do (r1,r2) <- f (gp - length paths,ep) rest
                                      return ([ (path, ((i1,i2),i,True)) | path <- paths ] ++ r1,r2)
                              else do (r1,r2) <- f (gp,ep - length paths) rest
                                      return (r1,[ (path, ((i1,i2),i,False)) | path <- paths ] ++ r2)
                    
             f tuple (combinations [ (i,s) | (i,(Just s,_,_)) <- vertices ] )                                                                
   in 
      rec (upperbound_GOODPATHS,upperbound_ERRORPATHS) is

makeEdgeInfoTable :: PathsWithInfo cinfo -> EdgeInfoTable cinfo
makeEdgeInfoTable xs = map (\(e:_, ys) -> (e,ys))
                     . map unzip
                     . groupBy (\x y -> fst (fst x)    ==     fst (fst y))
                     . sortBy  (\x y -> fst (fst x) `compare` fst (fst y))
                     $ [ ((edge,info), pathInfo) | (path, pathInfo) <- xs, (edge,Initial info) <- path ]

         
-----------------------------------------------------------

type EdgesFilter monad cinfo = [(EdgeID, cinfo)] -> monad [(EdgeID, cinfo)]
type EdgeFilter  monad cinfo = EdgeID -> cinfo   -> monad Bool

-- Note: Do not filter away all edges
applyEdgesFilter :: Monad monad => EdgesFilter monad cinfo -> [(EdgeID, cinfo)] -> monad [(EdgeID, cinfo)]
applyEdgesFilter edgesFilter edges = 
   do result <- edgesFilter edges
      return (if null result then edges else result)
   
-- Note: Do not filter away all edges      
applyEdgeFilter :: Monad monad =>  EdgeFilter monad cinfo -> [(EdgeID, cinfo)] -> monad [(EdgeID, cinfo)]
applyEdgeFilter edgeFilter edges = 
   do result <- filterM (uncurry edgeFilter) edges
      return (if null result then edges else result)

maximalEdgeFilter :: (Monad monad, Ord result) => (EdgeID -> cinfo -> monad result) -> EdgesFilter monad cinfo
maximalEdgeFilter function edges = 
   do tupledList <- let f tuple@(edgeID, cinfo) = do result <- function edgeID cinfo
                                                     return (result, tuple)
                    in mapM f edges
      let maximumResult = maximum (map fst tupledList)
      return (map snd (filter ((maximumResult ==) . fst) tupledList))
      
constraintPhaseFilter :: (Monad monad, TypeGraphConstraintInfo cinfo) => EdgesFilter monad cinfo
constraintPhaseFilter = maximalEdgeFilter (const (return . maybe 0 id . getConstraintPhaseNumber))

differentGroupsFilter :: Monad monad => EdgeInfoTable cinfo -> EdgesFilter monad cinfo
differentGroupsFilter edgeInfoTable = maximalEdgeFilter f 
   where f edgeID cinfo = return $
            case find ((edgeID==) . fst . fst) edgeInfoTable of 
               Nothing            -> 0
               Just (_,pathInfos) -> length $ nub $ [ grp | (_, grp, False) <- pathInfos ]
               
errorAndGoodPaths :: EdgeInfoTable cinfo -> EdgeHeuristic info
errorAndGoodPaths edgeInfoTable edgeID cinfo = 
   return $ case find ((edgeID==) . fst . fst) edgeInfoTable of 
      Nothing            -> NotApplicableHeuristic
      Just (_,pathInfos) -> 
         let inGoodPaths     = length $ nub $ [ reorder src | (src, _, True ) <- pathInfos ]
             inErrorPaths    = length $ nub $ [ reorder src | (src, _, False) <- pathInfos ]
             reorder (a,b)   = if a <= b then (a,b) else (b,a)
         in ModifierHeuristic (0.1 ^ inGoodPaths * 5.0 ^ inErrorPaths) ("[good="++show inGoodPaths ++",error="++show inErrorPaths++"]")
         
maybeUserConstraintFilter :: (Monad monad, TypeGraphConstraintInfo cinfo) => PathsWithInfo cinfo -> EdgesFilter monad cinfo
maybeUserConstraintFilter pathsWithInfo edges = 
   let errorPaths = [ path | (path, (_, _, False)) <- pathsWithInfo ]
       filterForPath path =  [ (edge, info) 
                             | (edge, Initial info) <- path
                             , edge `elem` map fst edges 
                             , isJust (maybeUserConstraint info)
                             ]
       cmp (_, info1) (_, info2) = 
          compare (getPosition info1) (getPosition info2)
   in return 
    . maybe [] (:[]) 
    . safeMinimumBy cmp 
    . catMaybes 
    . map (safeMaximumBy cmp . filterForPath) 
    $ errorPaths
