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
import SolverOptions        ( getTypeSynonyms, getTypeSignatures, getExtraSiblings )
import Utils                ( internalError, fst4 )
import SimilarFunctionTable ( similarFunctionTable )
import UHA_Utils            ( nameFromString )
import UHA_Syntax           ( Literal(..), Range(..), Position(..) )
import Monad                ( unless, when, filterM )
import Maybe                ( catMaybes, isJust, isNothing )
import InfiniteTypeHeuristic  -- (infiniteTypeHeuristic, safeMaximumBy, safeMinimumBy)

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
fixHint = TypeErrorHint "probable fix". MessageString

becauseHint :: String -> TypeErrorInfo
becauseHint = TypeErrorHint "because" . MessageString

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
                 , trustFactorOfConstraint
                 , isFolkloreEdge
                 , edgeIsPartOfCycle
                 , fbHasTooManyArguments                                  
                 , similarLiterals
                 , similarNegation
                 , tupleEdge
                 , similarFunctions                 
                 , applicationEdge
                 , variableFunction                 
                 ]

orderOfUnification :: TypeGraphConstraintInfo info => EdgeHeuristic info
orderOfUnification edge info =
   case getPosition info of
      Nothing       -> return NotApplicableHeuristic
      Just position -> let modifier = 1 + fromIntegral position / 10000
                       in return (ModifierHeuristic modifier ("position="++show position))

trustFactorOfConstraint :: TypeGraphConstraintInfo info => EdgeHeuristic info
trustFactorOfConstraint edge info =
   case getTrustFactor info of
      Nothing    -> return NotApplicableHeuristic
      Just trust -> let modifier = 1 / fromIntegral trust
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
      
         do options <- getSolverOptions
            let (t1,t2)   = getTwoTypes info
                string    = show name
                extras    = getExtraSiblings options
                functions = filter (string /=)
                          . concat
                          . filter (string `elem`) 
                          $ extras ++ similarFunctionTable 
            if null functions 
              then return NotApplicableHeuristic
              else let tryFunctions = map (\s -> (s, lookup s importedFunctions)) functions  
                       importedFunctions = getTypeSignatures options 
                       synonyms = getTypeSynonyms options
                                                              
                   in doWithoutEdge (edge,info) $ 

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
      Nothing            -> return NotApplicableHeuristic
      Just isIntNegation ->

         doWithoutEdge (edge,info) $

            do options  <- getSolverOptions
               let (t1,t2)   = getTwoTypes info
                   synonyms  = getTypeSynonyms options
               unique   <- getUnique
               mtp      <- safeApplySubst t2
               case mtp of
                  Just tp
                     | intNegation && not floatNegation && floatNegationEdge
                        -> let hint = SetHint (fixHint "use int negation (-) instead")
                           in return $ ConcreteHeuristic 6 [hint] "int negation should be used"

                     | not intNegation && floatNegation && intNegationEdge
                        -> let hint = SetHint (fixHint "use float negation (-.) instead")
                           in return $ ConcreteHeuristic 6 [hint] "float negation should be used"
                     
                     | errorInResult  
                        -> return (ModifierHeuristic 0.000001 "negation: only result is incorrect")
                     
                    where intNegation       = unifiable synonyms tp (intType .->. intType)
                          floatNegation     = unifiable synonyms tp (floatType .->. floatType)
                          intNegationEdge   = isIntNegation
                          floatNegationEdge = not isIntNegation
                          errorInResult     = let newtvar = TVar (maximum (0 : ftv tp) + 1)
                                                  testtp = (if isIntNegation then intType else floatType) .->. newtvar
                                              in unifiable synonyms tp testtp                                              

                  _ -> return NotApplicableHeuristic

applicationEdge :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => EdgeHeuristic info
applicationEdge edge@(EdgeID v1 v2) info =
   case maybeApplicationEdge info of
      Nothing                            -> return NotApplicableHeuristic
      Just (isBinary,tuplesForArguments) ->

       doWithoutEdge (edge,info) $

          do options                 <- getSolverOptions
             let (t1,t2)              = getTwoTypes info
                 synonyms             = getTypeSynonyms options
                 isPatternApplication = isPattern info 
             maybeFunctionType       <- safeApplySubst t1
             maybeExpectedType       <- safeApplySubst t2
             
             case (maybeFunctionType,maybeExpectedType) of

               (Just functionType,Just expectedType) 

                  -- the expression to which arguments are given does not have a function type
                  | maybe False (<= 0) maximumForFunction && not isBinary && not isPatternApplication ->                       
                       let hint = SetHint (becauseHint "it is not a function")
                       in return (ConcreteHeuristic 6 [hint] "no function")
                  
                  -- function used as infix that expects < 2 arguments
                  | maybe False (<= 1) maximumForFunction && isBinary && not isPatternApplication ->
                       let hint = SetHint (becauseHint "it is not a binary function")
                       in return (ConcreteHeuristic 6 [hint] "no binary function")

                  -- can a permutation of the arguments resolve the type inconsistency
                  | length argumentPermutations == 1 -> 
                       let p = head argumentPermutations
                       in 
                         if p==[1,0] && isBinary
                            then 
                                 let hint = SetHint (fixHint "swap the two arguments")
                                 in return (ConcreteHeuristic 3 [hint] "swap the two arguments")
                            else                                       
                                  let hint = SetHint (fixHint "re-order arguments")
                                  in return (ConcreteHeuristic 1 [hint] ("application: permute with "++show p))
                                
                  -- is there one particular argument that is inconsistent
                  | length incorrectArguments == 1  ->
                       do let i = head incorrectArguments
                          expfulltp <- applySubst t1
                          let (oneLiner,tp,range) = tuplesForArguments !! i
                              typeError     = makeTypeErrorForTerm (isBinary,isPatternApplication) i oneLiner (tp,expargtp) range info
                              expargtp      = fst (functionSpine expfulltp) !! i
                          return (ConcreteHeuristic 3 [SetTypeError typeError] ("incorrect argument of application="++show i))                          
                  
                  -- too many arguments are given
                  | maybe False (< numberOfArguments) maximumForFunction && not isPatternApplication ->
                       case typesZippedWithHoles of

                          -- there is only one possible set to remove arguments 
                          [is] | not isBinary
                              -> let hint = SetHint (fixHint ("remove "++prettyAndList (map (ordinal True . (+1)) is)++" argument"))
                                 in return (ConcreteHeuristic 4 [hint] ("too many arguments are given: "++show is))

                          -- more than one or no possible set of arguments to be removed
                          _   -> let hint = SetHint (becauseHint "too many arguments are given")
                                 in return (ConcreteHeuristic 2 [hint] "too many arguments are given")
                                          
                  -- not enough arguments are given
                  | minimumForContext > numberOfArguments && not isPatternApplication && contextIsUnifiable ->
                       case typesZippedWithHoles of

                          [is] | not isBinary 
                              -> let hint = SetHint (fixHint ("insert a "++prettyAndList (map (ordinal True . (+1)) is)++" argument"))
                                 in return (ConcreteHeuristic 4 [hint] ("not enough arguments are given"++show is))

                          _   -> let hint = SetHint (becauseHint "not enough arguments are given")
                                 in return (ConcreteHeuristic 2 [hint] "not enough arguments are given")
                  
                  -- only the result type is incorrect
                  | argumentsAreUnifiable ->
                      return (ModifierHeuristic 0.000001 "application: only result is incorrect")                        

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
                      
                      -- are the arguments or the context unifiable?
                      argumentsAreUnifiable = unifiableTypeLists functionArguments expectedArguments
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
                                             ]                                                                         

                      -- at which locations should an extra argument be inserted?
                      typesZippedWithHoles  = [ is 
                                              | (is,zl) <- take heuristics_MAX (zipWithHoles allFunctionArgs allExpectedArgs)
                                              , let (as,bs) = unzip zl
                                              , unifiableTypeLists (allFunctionRes : as) 
                                                                   (allExpectedRes : bs)
                                              ]                     

               _ -> return NotApplicableHeuristic
                                                       
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
                               , let (xs, ys) = unzip zl in unifiable synonyms (tupleType xs) (tupleType ys)
                               ] of
                       [is] -> case compare of
                                 LT -> let hint = SetHint (fixHint ("insert a "++prettyAndList (map (ordinal True. (+1)) is)++" element to the tuple"))
                                       in return (ConcreteHeuristic 4 [hint] ("tuple:insert "++show is)) 
                                 GT -> let hint = SetHint (fixHint ("remove "++prettyAndList (map (ordinal True . (+1)) is)++" element of tuple"))
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

variableFunction :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => EdgeHeuristic info
variableFunction edge info
   | (nt, alt) /= (NTBindingGroup, AltBindingGroup) && (nt, alt) /= (NTBody, AltBody) 
        = return NotApplicableHeuristic
   | otherwise 
        = doWithoutEdge (edge,info) $ 
            
           do options     <- getSolverOptions
              let (t1,t2)  = getTwoTypes info
                  synonyms = getTypeSynonyms options
              
              -- is this variable involved in an application?
              let EdgeID v1 v2 = edge
              edges1 <- getAdjacentEdges v1
              edges2 <- getAdjacentEdges v2
              let predicate x = 
                     let (a,b,c,_) = getInfoSource x -- Empty InfixApplication 
                     in (a,b,c) == (NTExpression, AltInfixApplication, 4)
                  f (EdgeID v1 v2) = [v1,v2]
              let special = concatMap (f . fst) (filter (predicate . snd) (edges1 ++ edges2)) \\ [v1,v2]
              edges3 <- mapM getAdjacentEdges special
              let isApplicationEdge = isJust . maybeApplicationEdge
                  application = any (isApplicationEdge . snd) (edges1 ++ edges2 ++ concat edges3)                 
                                
              mt1         <- safeApplySubst t1
              mt2         <- safeApplySubst t2
              case (mt1, mt2) of
                 (Just functionType, Just expectedType) | not application -> 
                    let maxArgumentsForFunction = length (fst (functionSpine functionType))
                        minArgumentsForContext  = maxArgumentsForFunction - length (fst (functionSpine expectedType)) 
                        contextIsUnifiable      = unifiable synonyms 
                                                     (snd $ functionSpineOfLength minArgumentsForContext functionType)
                                                     expectedType
                    in if minArgumentsForContext <= 0 || not contextIsUnifiable
                         then return NotApplicableHeuristic
                         else let hint = SetHint (fixHint ("insert "++showNumber minArgumentsForContext++" argument"++
                                              if minArgumentsForContext <= 1 then "" else "s"))
                              in return (ConcreteHeuristic 4 [hint] ("insert arguments to function variable"))                     
                 _                       -> return NotApplicableHeuristic                   

  where (nt, alt, _, _) = getInfoSource info

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

unifiableTps :: OrderedTypeSynonyms -> Tps -> Bool
unifiableTps ots = either (const False) (const True) . mguForTps ots

mguForTps :: OrderedTypeSynonyms -> Tps -> Either UnificationError (Bool,FiniteMapSubstitution)
mguForTps orderedTypeSynonyms tps = 
   let e  = Right (False, emptySubst)
       op t1 t2 result = case result of
          Left uError   -> result
          Right (b,sub) -> let t1' = sub |-> t1
                               t2' = sub |-> t2
                               res = mguWithTypeSynonyms orderedTypeSynonyms t1' t2'
                               combine (b', sub') = Right (b' || b, sub' @@ sub)
                           in either Left combine res                              
   in case tps of
         []     -> e
         tp:tps -> foldr (op tp) e tps

getAdjacentEdges :: Int -> SolveState EquivalenceGroups info [(EdgeID, info)]
getAdjacentEdges vertexID =
   useSolver
      (\groups -> do eqc <- equivalenceGroupOf vertexID groups
                     let predicate (EdgeID v1 v2) = v1 == vertexID || v2 == vertexID
                     return (filter (predicate . fst) (edges eqc)))
         

-- see TypesToAllignedDocs      
isTVar :: Tp -> Bool
isTVar (TVar _) = True
isTVar _        = False
                     

showNumber :: Int -> String
showNumber i | i <= 10 && i >=0 = list !! i
             | otherwise        = show i
   where list = [ "zero", "one", "two", "three", "four", "five"
                , "six", "seven", "eight", "nine", "ten" ]            

functionSpineOfLength :: Int -> Tp -> (Tps, Tp)
functionSpineOfLength i tp = 
   let (as, a ) = functionSpine tp
       (bs, cs) = splitAt i as
   in (bs, foldr (.->.) a cs)

deleteIndex :: Int -> [a] -> [a]
deleteIndex _ []     = []
deleteIndex 0 (a:as) = as
deleteIndex i (a:as) = a : deleteIndex (i-1) as

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

{- keep a history to avoid non-termination (for type-graphs that contain an infinite type) -}                                           
safeApplySubst :: TypeGraph EquivalenceGroups info => Tp -> SolveState EquivalenceGroups info (Maybe Tp)
safeApplySubst = rec [] where 

  rec history tp = case tp of 
    TVar i | i `elem` history 
               -> return Nothing
           | otherwise 
               -> do vertices  <- getVerticesInGroup i
                     constants <- getConstantsInGroup i
                     children  <- getChildrenInGroup i
                     tps       <- case children of
                                     []       -> return [] 
                                     (_,is):_ -> mapM (rec (i : history)) (map TVar is)
                     let tp = case constants of 
                                 []  -> Just . TVar . fst . head $ vertices
                                 [s] -> Just (TCon s)
                                 _   ->  Nothing
                     let tapp t1 t2 = case (t1,t2) of 
                                        (Just t1',Just t2') -> Just (TApp t1' t2')
                                        _                   -> Nothing                                      
                     return (foldl tapp tp tps)
    TCon s     -> return (Just tp)
    TApp t1 t2 -> do mt1 <- rec history t1
                     mt2 <- rec history t2
                     case (mt1,mt2) of 
                       (Just t1',Just t2') -> return (Just $ TApp t1' t2')
                       _                   -> return Nothing
                       
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
