

-- UUAGC 0.9.7 (TypeInferencing.ag)
module TypeInferencing where


-- types
import Top.Types
import TypeConversion

-- error messages and warnings
import Messages
import TypeErrors
import Warnings
import ConstraintInfo
import DoublyLinkedTree
import UHA_Source

-- constraints and constraint trees
import TypeConstraints
import Top.Ordering.Tree

-- constraint solving
import SelectConstraintSolver (selectConstraintSolver)
import Top.Solver (SolveResult(..), LogEntries)
import HeuristicsInfo (makeUnifier, skip_UHA_FB_RHS)
import BindingGroupAnalysis

-- UHA syntax
import UHA_Syntax
import UHA_Range                 
import UHA_Utils                 (showNameAsOperator, intUnaryMinusName, NameWithRange(..), nameFromString)
         
-- other
import Utils                     (internalError)
import DerivingShow              (typeOfShowFunction, nameOfShowFunction)
import ImportEnvironment  hiding (setTypeSynonyms)
import DictionaryEnvironment
import Args

-- standard
import qualified Data.Map as M
import Data.Maybe 
import Data.List


import List
import Matchers
import TS_Apply (applyTypingStrategy, matchInformation)
import TS_CoreSyntax
import TS_Attributes


import UHA_Utils

typeInferencing :: [Option] -> ImportEnvironment -> Module
                      -> (IO (), DictionaryEnvironment, TypeEnvironment, TypeErrors, Warnings)
typeInferencing options importEnv module_ =
   let (_, dictionaryEnv, _, logEntries, _, solveResult, toplevelTypes, typeErrors, warnings) =
            TypeInferencing.sem_Module module_ importEnv options
       debugIO = putStrLn (show logEntries)
   in (debugIO, dictionaryEnv, toplevelTypes, typeErrors, warnings)

proximaTypeInferencing :: [Option] -> ImportEnvironment -> Module
                      -> (TypeErrors, Warnings, TypeEnvironment, [(Range, TpScheme)])  
proximaTypeInferencing options importEnv module_ =
   let (_, _, infoTree, _, _, solveResult, toplevelTypes, typeErrors, warnings) =
            TypeInferencing.sem_Module module_ importEnv options
       localTypeSchemes = typeSchemesInInfoTree (substitutionFromResult solveResult)
                                                (qualifiersFromResult solveResult) 
                                                infoTree
   in (typeErrors, warnings, toplevelTypes, localTypeSchemes)

         
getRequiredDictionaries :: OrderedTypeSynonyms -> Tp -> TpScheme -> Predicates
getRequiredDictionaries synonyms useType defType =
   expandPredicates synonyms (matchTypeWithScheme synonyms useType defType)

matchTypeWithScheme :: OrderedTypeSynonyms -> Tp -> TpScheme -> Predicates
matchTypeWithScheme synonyms tp scheme =
   let (ips, itp) = split . snd . instantiate 0 . freezeFTV $ scheme
   in case mguWithTypeSynonyms synonyms itp (freezeVariablesInType tp) of
         Left _ -> internalError "TypeInferenceOverloading.ag" "matchTypeWithScheme" "no unification"
         Right (_, sub) -> 
            let f (Predicate s tp) = Predicate s (unfreezeVariablesInType $ sub |-> tp)
            in map f ips
            
resolveOverloading :: ClassEnvironment -> Name -> Predicates -> Predicates ->
                         DictionaryEnvironment -> DictionaryEnvironment
resolveOverloading classEnv name availablePredicates predicates dEnv = 
   let maybeTrees = map (makeDictionaryTree classEnv availablePredicates) predicates
   in if all isJust maybeTrees
        then addForVariable name (map fromJust maybeTrees) dEnv
        else internalError "TypeInferenceOverloading.ag" "resolveOverloading" ("cannot resolve overloading (" ++ show name ++ ")")
   
expandPredicates :: OrderedTypeSynonyms -> Predicates -> Predicates
expandPredicates synonyms = map (expandPredicate synonyms)

expandPredicate :: OrderedTypeSynonyms -> Predicate -> Predicate
expandPredicate (_, synonyms) (Predicate className tp) = Predicate className (expandType synonyms tp)


findInferredTypes :: M.Map Int (Scheme Predicates) -> M.Map Name (Sigma Predicates) -> TypeEnvironment
findInferredTypes typeschemeMap =
   let err = internalError "TypeInferenceCollect.ag" "findInferredTypes" "could not find type scheme variable"
       f :: Sigma Predicates -> TpScheme
       f (SigmaVar i)     = M.findWithDefault err i typeschemeMap
       f (SigmaScheme ts) = ts
   in M.map f
   
missingTypeSignature :: Bool -> Names -> TypeEnvironment -> Warnings
missingTypeSignature topLevel simplePats = 
   let -- for the moment, only missing type signature for top-level functions are reported (unless monomorphic).
      makeWarning (name, scheme) =
         let fromSimple = name `elem` simplePats && isOverloaded scheme
         in [ NoTypeDef name scheme topLevel fromSimple | null (ftv scheme) && (topLevel || fromSimple)  ]
   in concatMap makeWarning . M.assocs
   
restrictedNameErrors :: TypeEnvironment -> Names -> TypeErrors
restrictedNameErrors env = 
   let f name = case M.lookup name env of
                   Just scheme -> [ makeRestrictedButOverloadedError name scheme | isOverloaded scheme ]
                   Nothing     -> []
   in concatMap f



makeLocalTypeEnv :: TypeEnvironment -> BindingGroups -> M.Map NameWithRange TpScheme
makeLocalTypeEnv local groups =
   let (environment, _, _) = concatBindingGroups groups
       names = M.keys environment
       f x   = maybe err id (find (==x) names) 
       err   = internalError "TypeInferenceCollect.ag" "makeLocalTypeEnv" "could not find name"
   in M.fromList [ (NameWithRange (f name), scheme) | (name, scheme) <- M.assocs local ]


isSimplePattern :: Pattern -> Bool
isSimplePattern pattern =
   case pattern of
      Pattern_Variable _ _ -> True
      Pattern_Parenthesized  _ p -> isSimplePattern p
      _ -> False


globalInfoError :: a
globalInfoError = internalError "GlobalInfo.ag" "n/a" "global info not available"

                  
type ScopeInfo = ( [Names]          -- duplicated variables
                 , [Name]           -- unused variables
                 , [(Name, Name)]   -- shadowed variables
                 )

changeOfScope :: Names -> Names -> Names -> (Names, Names, ScopeInfo)
changeOfScope names unboundNames namesInScope = 
   let (uniqueNames, duplicatedNames) = uniqueAppearance names
       unusedNames   = uniqueNames \\ unboundNames
       shadowedNames = let f n = [ (n, n') | n' <- namesInScope, n == n' ]
                       in concatMap f uniqueNames
   in ( uniqueNames ++ map head duplicatedNames ++ (namesInScope \\ names)
      , unboundNames \\ names
      , (duplicatedNames, unusedNames, shadowedNames)
      )
      
uniqueAppearance :: Ord a => [a] -> ([a],[[a]])
uniqueAppearance = foldr insert ([],[]) . group . sort
   where insert [x] (as,bs) = (x:as,bs)
         insert xs  (as,bs) = (as,xs:bs)


matchConverter0 :: [([String],())] -> ()
matchConverter0 = const ()

matchConverter1 :: [([String],a)] -> [(a,[String])]
matchConverter1 = map (\(a,b) -> (b,a))  
                  
matchConverter2 :: [([String],(a,b))] -> ([(a,[String])],[(b,[String])])
matchConverter2 = let insert (metas,(a,b)) (as,bs) = ((a,metas):as,(b,metas):bs)
                  in foldr insert ([],[])                  

matchConverter3 :: [([String],(a,b,c))] -> ([(a,[String])],[(b,[String])],[(c,[String])])
matchConverter3 = let insert (metas,(a,b,c)) (as,bs,cs) = ((a,metas):as,(b,metas):bs,(c,metas):cs)
                  in foldr insert ([],[],[]) 

allMatch :: [Maybe [a]] -> Maybe [a]
allMatch = rec []
  where rec xs []             = Just xs
        rec xs (Nothing:_)    = Nothing
        rec xs (Just ys:rest) = rec (ys ++ xs) rest

data Match a = NoMatch | NonTerminalMatch a | MetaVariableMatch String

instance Show (Match a) where
  show (NoMatch) = "NoMatch"
  show (NonTerminalMatch a) = "NonTerminal ??"
  show (MetaVariableMatch s) = "MetaVariableMatch "++show s

expressionVariableMatcher :: Expression -> Maybe String
expressionVariableMatcher expr =
   case expr of
      Expression_Variable _ name -> Just (show name)
      _                          -> Nothing

match0 = generalMatch expressionVariableMatcher matchConverter0
match1 = generalMatch expressionVariableMatcher matchConverter1
match2 = generalMatch expressionVariableMatcher matchConverter2
match3 = generalMatch expressionVariableMatcher matchConverter3

match0' = generalMatch noMatch matchConverter0 noMetaVariableInfo 0
match1' = generalMatch noMatch matchConverter1 noMetaVariableInfo 0
match2' = generalMatch noMatch matchConverter2 noMetaVariableInfo 0

matchOnlyVariable infoTuple tryPats = 
       let ((),matches,_,_,_,_) = match0 infoTuple 0 noMatch tryPats [] []
   in matches

noMatch :: a -> Maybe b
noMatch = const Nothing

noMetaVariableInfo = internalError "PatternMatching.ag" "noMetaVariableInfo" ""

generalMatch :: (nonTerminal -> Maybe String) 
             -> ([([String], childrenTuple)] -> childrenResult)
             -> MetaVariableInfo
             -> Int
             -> (nonTerminal -> Maybe childrenTuple) 
             -> [(nonTerminal, [String])] 
             -> [((nonTerminal, [String]), Core_TypingStrategy)] 
             -> [[Maybe MetaVariableTable]] 
             -> ( childrenResult
                , [Maybe MetaVariableTable]
                , ConstraintSet
                , Assumptions
                , Int
                , IO ()
                )

generalMatch exprVarMatcher converter metaInfo unique matcher tryPats allPats childrenResults =
   let match (expr,metas) = 
          case exprVarMatcher expr of
             Just s | s `elem` metas -> MetaVariableMatch s
             _ -> case matcher expr of
                     Just x  -> NonTerminalMatch (metas,x)
                     Nothing -> NoMatch
           
       (allPatterns, allStrategies) = unzip allPats
       matchListTry = map match tryPats
       matchListNew = map match allPatterns
       
       matchNTTry  = [ x | NonTerminalMatch x <- matchListTry ]
       matchNTNew  = [ x | NonTerminalMatch x <- matchListNew ]
       forChildren = converter (matchNTTry ++ matchNTNew)
       
       numberOfTry = length matchNTTry
       (resultTry,resultNew) = unzip . map (splitAt numberOfTry) $ 
                               if null childrenResults
                                 then [repeat (Just [])]
                                 else childrenResults
       inspectMatch m (res, nts) =
          case m of
             NoMatch             -> (Nothing:res, nts)
             NonTerminalMatch _  -> (allMatch (head nts):res, tail nts)
             MetaVariableMatch s -> (Just [(s, metaInfo)]:res, nts) --  !!!
       
       result   = fst (foldr inspectMatch ([],reverse $ transpose resultTry) matchListTry)       
       complete = let (list,_) = foldr inspectMatch ([],reverse $ transpose resultNew) matchListNew
                  in [ (x, y) | (Just x, y) <- zip list allStrategies ]

       (assumptions, constraintSet, debugIO, newUnique) = 
          case complete of
          
             [] -> (getAssumptions metaInfo, getConstraintSet metaInfo, return (), unique)
             
             (childrenInfo, typingStrategy):_ 
                -> applyTypingStrategy typingStrategy metaInfo childrenInfo unique            
   in (forChildren, result, constraintSet, assumptions, newUnique, debugIO)


pmError = internalError "PatternMatchWarnings"


expandTypeFromImportEnvironment :: ImportEnvironment -> Tp -> Tp
expandTypeFromImportEnvironment env = expandType (snd $ getOrderedTypeSynonyms env)

patternMatchWarnings :: Substitution substitution
                     => ImportEnvironment          -- the importenvironment
                     -> substitution               -- substitution that contains the real types
                     -> Tp                         -- type of the patterns, unsubstituted
                     -> (Tp -> Tps)                -- how should the type be interpreted?
                     -> [([PatternElement], Bool)] -- the patterns to be processed
                     -> Range                      -- range for the missing-warnings
                     -> Maybe Name                 -- maybe the name of the function
                     -> Bool                       -- should there be parentheses around the patterns?
                     -> [Warning]                  -- list of overlap-warnings for all of the patterns  
                     -> String                     -- description of the place where the patterns are
                     -> String                     -- symbol after the patterns
                     -> [Warning]                  -- returns: list of warnings
patternMatchWarnings impenv sub tp strip elementss rng name parens unrwars place sym
  = unreachablewarnings ++ missingwarnings
    where
      env                 = importEnvironmentToEnv impenv
      exprtype            = expandTypeFromImportEnvironment impenv $ sub |-> tp
      types               = strip exprtype
      unreachables        = unreachable impenv types $ map (\((a, b), c) -> (a, c)) $ filter (not.snd.fst) $ zip elementss [0..]
      missing             = complement  impenv types $ map fst elementss
      unreachablewarnings = map (unrwars !!) unreachables
      missingwarnings
        | null $ unMissing missing = []
        | otherwise                = [MissingPatterns rng name exprtype (map (nicePattern parens env) $ missingList missing) place sym]



----------
-- misc --
----------

-- lifted or
(|^|) :: (a -> Bool) -> (a -> Bool) -> a -> Bool
(|^|) f g x = f x || g x

----------------------------------------------
--- environments and substitution of types ---
----------------------------------------------

-- environment of constructors [(type, (constructorname, arguments))]
type Env = [(Tp, (Name, [Tp]))]
importEnvironmentToEnv = map rearrange . M.assocs . valueConstructors

-- return the number of arguments of a constructor
-- tuples ar not in the Env so they require special treatment
nrOfArguments :: Env -> String -> Int
nrOfArguments env con | isTupleConstructor con = length con - 1
                      | otherwise = case lookup (nameFromString con) $ map snd env
                                    of Just args -> length args
                                       Nothing   -> 0

-- convert constructor to fit in an Env
rearrange :: (Name, TpScheme) -> (Tp, (Name, [Tp]))
rearrange (name, tpscheme) = let (args, res) = functionSpine $ unqualify $ unquantify tpscheme
                             in (res, (name, args))

-- get the constructors of a given type out of an Env
-- tuples ar not in the Env so they require special treatment
constructors :: ImportEnvironment -> Tp -> [(Name, [Tp])]
constructors _ (TVar _) = []
constructors impenv tp | isTupleConstructor name = [tupleconstructor]
                       | otherwise               = map expand $ concatMap (substitute tp) $ importEnvironmentToEnv impenv
  where
    name :: String
    name = unTCon $ fst $ leftSpine tp
    tupleconstructor :: (Name, [Tp])
    tupleconstructor = (nameFromString name, snd $ leftSpine tp)
    unTCon :: Tp -> String
    unTCon (TCon c) = c
    unTCon tp = pmError "unTCon" $ "type " ++ show tp ++ " is not a TCon"
    expand :: (Name, [Tp]) -> (Name, [Tp])
    expand (n, ts) = (n, map (expandTypeFromImportEnvironment impenv) ts)

-- check of an entry in an Env is a constructor for the given type
-- if so, return this constructor, but with variables substituted for whatever is in the given type
-- the list returns zero or one elements
-- for example: substitute (Maybe Int) (Maybe a, (Just, [a])) will return [(Just, [Int])]
substitute :: Tp -> (Tp, (Name, [Tp])) -> [(Name, [Tp])]
substitute t1 (t2, (con, args)) = let (c1, ts1) = leftSpine t1
                                      (c2, ts2) = leftSpine t2
                                      sub = listToSubstitution $ zip (map unTVar ts2) ts1
                                  in if c1 == c2
                                     then [(con, map (sub |->) args)]
                                     else []
  where
    unTVar :: Tp -> Int
    unTVar (TVar v) = v
    unTVar _ = pmError "unTVar" "type is not a TVar"

---------------------------------------------------------------
--- datastructures and functions for the solution structure ---
---------------------------------------------------------------

-- a pattern is a list of patternelements
data PatternElement = WildcardElement | InfiniteElement String | FiniteElement String deriving Eq
isInfiniteElement :: PatternElement -> Bool
isInfiniteElement (InfiniteElement _) = True
isInfiniteElement _                   = False
elementString :: PatternElement -> String
elementString (InfiniteElement s) = s
elementString (  FiniteElement s) = s
elementString _                   = []

-- needed for Pattern_List and Literal_String occurences
listPat :: [[PatternElement]] -> [PatternElement]
listPat [] = [FiniteElement "[]"]
listPat (ps:pss) = FiniteElement ":" : ps ++ listPat pss

stringPat :: String -> [PatternElement]
stringPat [] = [FiniteElement "[]"]
stringPat (c:cs) = FiniteElement ":" : InfiniteElement [c] : stringPat cs

-- tree of missing patterns
data PatternsMissing = PatternsMissing [(PatternElement, PatternsMissing)]
unMissing :: PatternsMissing -> [(PatternElement, PatternsMissing)]
unMissing (PatternsMissing l) = l

-- create a branch consisting of only wildcards
wildMissing :: Int -> PatternsMissing
wildMissing 0 = PatternsMissing []
wildMissing n = PatternsMissing [(WildcardElement, wildMissing $ n - 1)]

-- convert a missing patterns tree to a list of seperated missing patterns
missingList :: PatternsMissing -> [[PatternElement]]
missingList (PatternsMissing []) = [[]]
missingList (PatternsMissing [(d,t)]) = map (d:) $ missingList t
missingList (PatternsMissing (d:ds)) = (missingList $ PatternsMissing [d]) ++ (missingList $ PatternsMissing ds)

-------------------------------------------------------------------
--- functions to create a UHA_Pattern out of a [PatternElement] ---
-------------------------------------------------------------------

-- nice creates the actual pattern without parentheses
-- [Just, True, True, (,), Just, Nothing, False] -> [Just True, True, (Just Nothing, False)]
nicePattern :: Bool -> Env -> [PatternElement] -> [Pattern]
nicePattern b env = map (parensPattern b) . nice
  where
    nice :: [PatternElement] -> [Pattern]
    nice []             = []
    nice (WildcardElement    :ps) = Pattern_Wildcard noRange : nice ps
    nice (InfiniteElement _  :ps) = pmError "nicePattern" "InfiniteElement in pattern!"
    nice (FiniteElement con:ps) =
      let rest = nice ps
          name = nameFromString con
          n    = nrOfArguments env con
      in case name 
         of Name_Identifier _ _ _                          -> Pattern_Constructor noRange name (take n rest) : drop n rest -- !!!Name
            Name_Operator   _ _ _ | con == ":"             -> case head $ tail rest -- !!!Name
                                                              of Pattern_List _ ps -> Pattern_List noRange (head rest:ps) : (tail $ tail rest)
                                                                 _ -> Pattern_InfixConstructor noRange (head rest) name (head $ tail rest) : (tail $ tail rest)
                                  | otherwise              -> Pattern_InfixConstructor noRange (head rest) name (head $ tail rest) : (tail $ tail rest)
            Name_Special    _ _ _ | isTupleConstructor con -> Pattern_Tuple noRange (take n rest) : drop n rest -- !!!Name
                                  | con == "[]"            -> Pattern_List  noRange [] : rest
                                  | otherwise              -> Pattern_Constructor noRange name (take n rest) : drop n rest

-- add parentheses to a pattern in the correct places
-- bool means: if needed, should there be parenthesis around the complete pattern?
parensPattern :: Bool -> Pattern -> Pattern
parensPattern b = if b then rap . par else fst . par
  where
    par :: Pattern -> (Pattern, Bool) -- Bool means: are parentheses needed around this pattern, shoud it be used in a more complex pattern
    par p@(Pattern_Literal          _ _    ) = (p, False)
    par p@(Pattern_Variable         _ _    ) = (p, False)
    par   (Pattern_Constructor      r n ps ) = (Pattern_Constructor r n $ map (rap.par) ps, length ps > 0)
    par   (Pattern_Parenthesized    _ p    ) = par p
    par   (Pattern_InfixConstructor r l n k) = (Pattern_InfixConstructor r (rap $ par l) n (rap $ par k), True)
    par   (Pattern_List             r ps   ) = (Pattern_List r $ map (fst.par) ps, False)
    par   (Pattern_Tuple            r ps   ) = (Pattern_Tuple r $ map (fst.par) ps, False)
    par   (Pattern_Record           _ _ _  ) = pmError "parensPattern" "Records are not supported" 
    par p@(Pattern_Negate           _ _    ) = (p, True)
    par p@(Pattern_NegateFloat      _ _    ) = (p, True)
    par   (Pattern_As               r n p  ) = (Pattern_As r n (rap $ par p), False)
    par p@(Pattern_Wildcard         _      ) = (p, False)
    par   (Pattern_Irrefutable      _ _    ) = pmError "parensPattern" "Irrefutable patterns are not supported"  
    par   (Pattern_Successor        _ _ _  ) = pmError "parensPattern" "Successors are not supported" 
    rap :: (Pattern, Bool) -> Pattern
    rap (p, False) = p
    rap (p, True ) = Pattern_Parenthesized noRange p

--------------------------------------
--- finally, the algorithm itself! ---
--------------------------------------

-- returns the tree of missing patterns for a given list of patterns    
complement :: ImportEnvironment -> [Tp] -> [[PatternElement]] -> PatternsMissing
complement _   []       _      = PatternsMissing []
complement _   _        ([]:_) = PatternsMissing []
complement env (tp:tps) pss    | null $ unMissing anyComplement                              = PatternsMissing []
                               | all (((== WildcardElement) |^| isInfiniteElement).head) pss = anyComplement
                               | otherwise                                                   = finComplement
  where
    patComplement :: [[PatternElement]] -> PatternElement -> [Tp] -> PatternsMissing
    patComplement []  current tps = PatternsMissing [(current, wildMissing $ length tps)]
    patComplement pss current tps = case unMissing $ complement env tps $ map tail $ pss
                                    of []   -> PatternsMissing []
                                       tegs -> PatternsMissing [(current, PatternsMissing tegs)]
    anyComplement :: PatternsMissing
    anyComplement = patComplement (filter ((== WildcardElement).head) pss) WildcardElement tps
    conComplement :: (Name, [Tp]) -> PatternsMissing
    conComplement (con, args) = patComplement (  filter ((== FiniteElement (getNameName con)).head) pss
                                              ++ map (\ps -> FiniteElement (getNameName con) : replicate (length args) WildcardElement ++ tail ps)
                                                     (filter ((== WildcardElement).head) pss)
                                              )
                                              (FiniteElement (getNameName con)) (args ++ tps)
    finComplement :: PatternsMissing
    finComplement = case constructors env tp
                    of []   -> wildMissing $ 1 + length tps
                       cons -> PatternsMissing $ concatMap (unMissing.conComplement) cons

----------------------------
--- unreachable patterns ---
----------------------------

-- complements the list of reachable patterns
unreachable :: ImportEnvironment -> [Tp] -> [([PatternElement], Int)] -> [Int]
unreachable env tps ps = let reach = reachable env tps ps
                         in  filter (not . flip elem reach) (map snd ps)

-- determines which patterns are reachable
-- possibly multiple occurances of indices
reachable :: ImportEnvironment -> [Tp] -> [([PatternElement], Int)] -> [Int]
reachable _   []       _  = pmError "reachable" "empty type list!"
reachable env (tp:tps) ps 
  | all ((== WildcardElement).head.fst) ps = conReachable ps
  | otherwise                              = concat $ map (conReachable.conPats) $ stop cons
  where
    cons :: [PatternElement]
    cons = thin $ map (head.fst) ps
    conPats :: PatternElement -> [([PatternElement], Int)]
    conPats con = map (\(es, i) -> (fill con es, i)) $ filter (((== con) |^| (== WildcardElement)).head.fst) ps
    fill :: PatternElement -> [PatternElement] -> [PatternElement]
    fill e@(FiniteElement c) (WildcardElement : es) = e : replicate (nrOfArguments (importEnvironmentToEnv env) c) WildcardElement ++ es
    fill e                   (_               : es) = e : es
    stop :: [PatternElement] -> [PatternElement]
    stop es | length (constructors env tp) > length es = FiniteElement "[*]" : es
            | length (constructors env tp) == 0        = FiniteElement "[*]" : es
            | otherwise                                = es
    conReachable :: [([PatternElement], Int)] -> [Int]
    conReachable [] = []
    conReachable pats 
      | null.tail.fst.head $ pats = [snd.head $ pats]
      | otherwise                 = reachable env (arguments (elementString.head.fst.head $ pats) ++ tps) 
                                            $ map (\(es, i) -> (tail es, i)) pats
    arguments :: String -> [Tp]
    arguments c = maybe [] id $ lookup c $ map (\(n, tps) -> (getNameName n, tps)) $ constructors env tp

-- remove double occurances and wildcards
thin :: [PatternElement] -> [PatternElement]
thin []                     = []
thin (WildcardElement : es) = thin es
thin (e               : es) | elem e thines =     thines
                            | otherwise     = e : thines
  where thines = thin es                            
                       
-- Alternative -------------------------------------------------
-- cata
sem_Alternative :: Alternative  ->
                   T_Alternative 
sem_Alternative (Alternative_Alternative _range _pattern _righthandside )  =
    (sem_Alternative_Alternative (sem_Range _range ) (sem_Pattern _pattern ) (sem_RightHandSide _righthandside ) )
sem_Alternative (Alternative_Empty _range )  =
    (sem_Alternative_Empty (sem_Range _range ) )
-- semantic domain
type T_Alternative  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                      (M.Map NameWithRange TpScheme) ->
                      Predicates ->
                      Tp ->
                      Tp ->
                      Int ->
                      ClassEnvironment ->
                      TypeErrors ->
                      Warnings ->
                      Int ->
                      DictionaryEnvironment ->
                      ImportEnvironment ->
                      (IO ()) ->
                      Monos ->
                      Names ->
                      OrderedTypeSynonyms ->
                      InfoTree ->
                      ([Warning]) ->
                      FixpointSubstitution ->
                      (M.Map Int (Scheme Predicates)) ->
                      Int ->
                      ( Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,DictionaryEnvironment,( ([PatternElement], Bool) ),InfoTrees,(IO ()),([Warning]),Alternative,Names,Int,Warning)
sem_Alternative_Alternative :: T_Range  ->
                               T_Pattern  ->
                               T_RightHandSide  ->
                               T_Alternative 
sem_Alternative_Alternative range_ pattern_ righthandside_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaLeft
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _righthandsideOmonos :: Monos
              _lhsOassumptions :: Assumptions
              _lhsOinfoTrees :: InfoTrees
              _lhsOunboundNames :: Names
              _lhsOelements :: ( ([PatternElement], Bool) )
              _lhsOunrwar :: Warning
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Alternative
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _patternObetaUnique :: Int
              _patternOimportEnvironment :: ImportEnvironment
              _patternOmonos :: Monos
              _patternOnamesInScope :: Names
              _patternOparentTree :: InfoTree
              _patternOpatternMatchWarnings :: ([Warning])
              _righthandsideOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _righthandsideOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _righthandsideOavailablePredicates :: Predicates
              _righthandsideObetaRight :: Tp
              _righthandsideObetaUnique :: Int
              _righthandsideOclassEnvironment :: ClassEnvironment
              _righthandsideOcollectErrors :: TypeErrors
              _righthandsideOcollectWarnings :: Warnings
              _righthandsideOcurrentChunk :: Int
              _righthandsideOdictionaryEnvironment :: DictionaryEnvironment
              _righthandsideOimportEnvironment :: ImportEnvironment
              _righthandsideOmatchIO :: (IO ())
              _righthandsideOnamesInScope :: Names
              _righthandsideOorderedTypeSynonyms :: OrderedTypeSynonyms
              _righthandsideOparentTree :: InfoTree
              _righthandsideOpatternMatchWarnings :: ([Warning])
              _righthandsideOsubstitution :: FixpointSubstitution
              _righthandsideOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _righthandsideOuniqueChunk :: Int
              _rangeIself :: Range
              _patternIbeta :: Tp
              _patternIbetaUnique :: Int
              _patternIconstraints :: ConstraintSet
              _patternIelements :: (  [PatternElement]        )
              _patternIenvironment :: PatternAssumptions
              _patternIinfoTree :: InfoTree
              _patternIpatVarNames :: Names
              _patternIpatternMatchWarnings :: ([Warning])
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _righthandsideIassumptions :: Assumptions
              _righthandsideIbetaUnique :: Int
              _righthandsideIcollectErrors :: TypeErrors
              _righthandsideIcollectInstances :: ([(Name, Instance)])
              _righthandsideIcollectWarnings :: Warnings
              _righthandsideIconstraints :: ConstraintSet
              _righthandsideIdictionaryEnvironment :: DictionaryEnvironment
              _righthandsideIfallthrough :: Bool
              _righthandsideIinfoTree :: InfoTree
              _righthandsideImatchIO :: (IO ())
              _righthandsideIpatternMatchWarnings :: ([Warning])
              _righthandsideIself :: RightHandSide
              _righthandsideIunboundNames :: Names
              _righthandsideIuniqueChunk :: Int
              _righthandsideOmonos =
                  M.elems _patternIenvironment ++ getMonos _csetBinds ++ _lhsImonos
              _constraints =
                  _csetBinds .>>.
                  Node [ _conLeft  .<. _patternIconstraints
                       , _righthandsideIconstraints
                       ]
              _conLeft =
                  [ (_patternIbeta .==. _lhsIbetaLeft) _cinfoLeft ]
              __tup1 =
                  (_patternIenvironment .===. _righthandsideIassumptions) _cinfoBind
              (_csetBinds,_) =
                  __tup1
              (_,_lhsOassumptions) =
                  __tup1
              _cinfoLeft =
                  resultConstraint "case pattern" _patternIinfoTree
                     [ Unifier (head (ftv _lhsIbetaLeft)) ("case patterns", attribute _lhsIparentTree, "case pattern") ]
              _cinfoBind =
                  \name -> variableConstraint "variable" (nameToUHA_Expr name)
                     [ FolkloreConstraint
                     , makeUnifier name "case alternative" _patternIenvironment _lhsIparentTree
                     ]
              _lhsOinfoTrees =
                  [_patternIinfoTree, _righthandsideIinfoTree]
              __tup2 =
                  changeOfScope _patternIpatVarNames _righthandsideIunboundNames _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup2
              (_,_unboundNames,_) =
                  __tup2
              (_,_,_scopeInfo) =
                  __tup2
              _lhsOunboundNames =
                  _unboundNames
              _lhsOelements =
                  (_patternIelements, _righthandsideIfallthrough)
              _lhsOunrwar =
                  UnreachablePatternCase _rangeIself _patternIself
              _lhsOcollectInstances =
                  _righthandsideIcollectInstances
              _self =
                  Alternative_Alternative _rangeIself _patternIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _righthandsideIbetaUnique
              _lhsOcollectErrors =
                  _righthandsideIcollectErrors
              _lhsOcollectWarnings =
                  _righthandsideIcollectWarnings
              _lhsOconstraints =
                  _constraints
              _lhsOdictionaryEnvironment =
                  _righthandsideIdictionaryEnvironment
              _lhsOmatchIO =
                  _righthandsideImatchIO
              _lhsOpatternMatchWarnings =
                  _righthandsideIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _righthandsideIuniqueChunk
              _patternObetaUnique =
                  _lhsIbetaUnique
              _patternOimportEnvironment =
                  _lhsIimportEnvironment
              _patternOmonos =
                  _lhsImonos
              _patternOnamesInScope =
                  _namesInScope
              _patternOparentTree =
                  _lhsIparentTree
              _patternOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _righthandsideOallPatterns =
                  _lhsIallPatterns
              _righthandsideOallTypeSchemes =
                  _lhsIallTypeSchemes
              _righthandsideOavailablePredicates =
                  _lhsIavailablePredicates
              _righthandsideObetaRight =
                  _lhsIbetaRight
              _righthandsideObetaUnique =
                  _patternIbetaUnique
              _righthandsideOclassEnvironment =
                  _lhsIclassEnvironment
              _righthandsideOcollectErrors =
                  _lhsIcollectErrors
              _righthandsideOcollectWarnings =
                  _lhsIcollectWarnings
              _righthandsideOcurrentChunk =
                  _lhsIcurrentChunk
              _righthandsideOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _righthandsideOimportEnvironment =
                  _lhsIimportEnvironment
              _righthandsideOmatchIO =
                  _lhsImatchIO
              _righthandsideOnamesInScope =
                  _namesInScope
              _righthandsideOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _righthandsideOparentTree =
                  _lhsIparentTree
              _righthandsideOpatternMatchWarnings =
                  _patternIpatternMatchWarnings
              _righthandsideOsubstitution =
                  _lhsIsubstitution
              _righthandsideOtypeschemeMap =
                  _lhsItypeschemeMap
              _righthandsideOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _patternIbeta,_patternIbetaUnique,_patternIconstraints,_patternIelements,_patternIenvironment,_patternIinfoTree,_patternIpatVarNames,_patternIpatternMatchWarnings,_patternIself,_patternIunboundNames) =
                  (pattern_ _patternObetaUnique _patternOimportEnvironment _patternOmonos _patternOnamesInScope _patternOparentTree _patternOpatternMatchWarnings )
              ( _righthandsideIassumptions,_righthandsideIbetaUnique,_righthandsideIcollectErrors,_righthandsideIcollectInstances,_righthandsideIcollectWarnings,_righthandsideIconstraints,_righthandsideIdictionaryEnvironment,_righthandsideIfallthrough,_righthandsideIinfoTree,_righthandsideImatchIO,_righthandsideIpatternMatchWarnings,_righthandsideIself,_righthandsideIunboundNames,_righthandsideIuniqueChunk) =
                  (righthandside_ _righthandsideOallPatterns _righthandsideOallTypeSchemes _righthandsideOavailablePredicates _righthandsideObetaRight _righthandsideObetaUnique _righthandsideOclassEnvironment _righthandsideOcollectErrors _righthandsideOcollectWarnings _righthandsideOcurrentChunk _righthandsideOdictionaryEnvironment _righthandsideOimportEnvironment _righthandsideOmatchIO _righthandsideOmonos _righthandsideOnamesInScope _righthandsideOorderedTypeSynonyms _righthandsideOparentTree _righthandsideOpatternMatchWarnings _righthandsideOsubstitution _righthandsideOtypeschemeMap _righthandsideOuniqueChunk )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOelements,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOunrwar)))
sem_Alternative_Empty :: T_Range  ->
                         T_Alternative 
sem_Alternative_Empty range_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaLeft
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOassumptions :: Assumptions
              _lhsOinfoTrees :: InfoTrees
              _lhsOelements :: ( ([PatternElement], Bool) )
              _lhsOunrwar :: Warning
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Alternative
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _rangeIself :: Range
              _lhsOassumptions =
                  noAssumptions
              _constraints =
                  emptyTree
              _lhsOinfoTrees =
                  []
              _lhsOelements =
                  ([], False)
              _lhsOunrwar =
                  pmError "Alternative_Empty.unrwar" "empty alternative"
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Alternative_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOconstraints =
                  _constraints
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOelements,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOunrwar)))
-- Alternatives ------------------------------------------------
-- cata
sem_Alternatives :: Alternatives  ->
                    T_Alternatives 
sem_Alternatives list  =
    (Prelude.foldr sem_Alternatives_Cons sem_Alternatives_Nil (Prelude.map sem_Alternative list) )
-- semantic domain
type T_Alternatives  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                       (M.Map NameWithRange TpScheme) ->
                       Predicates ->
                       Tp ->
                       Tp ->
                       Int ->
                       ClassEnvironment ->
                       TypeErrors ->
                       Warnings ->
                       Int ->
                       DictionaryEnvironment ->
                       ImportEnvironment ->
                       (IO ()) ->
                       Monos ->
                       Names ->
                       OrderedTypeSynonyms ->
                       InfoTree ->
                       ([Warning]) ->
                       FixpointSubstitution ->
                       (M.Map Int (Scheme Predicates)) ->
                       Int ->
                       ( Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSets,DictionaryEnvironment,([([PatternElement], Bool)]),InfoTrees,(IO ()),([Warning]),Alternatives,Names,Int,([Warning]))
sem_Alternatives_Cons :: T_Alternative  ->
                         T_Alternatives  ->
                         T_Alternatives 
sem_Alternatives_Cons hd_ tl_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaLeft
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraintslist :: ConstraintSets
              _lhsOinfoTrees :: InfoTrees
              _lhsOelementss :: ([([PatternElement], Bool)])
              _lhsOunrwars :: ([Warning])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Alternatives
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _hdOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _hdOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _hdOavailablePredicates :: Predicates
              _hdObetaLeft :: Tp
              _hdObetaRight :: Tp
              _hdObetaUnique :: Int
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectErrors :: TypeErrors
              _hdOcollectWarnings :: Warnings
              _hdOcurrentChunk :: Int
              _hdOdictionaryEnvironment :: DictionaryEnvironment
              _hdOimportEnvironment :: ImportEnvironment
              _hdOmatchIO :: (IO ())
              _hdOmonos :: Monos
              _hdOnamesInScope :: Names
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOparentTree :: InfoTree
              _hdOpatternMatchWarnings :: ([Warning])
              _hdOsubstitution :: FixpointSubstitution
              _hdOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _hdOuniqueChunk :: Int
              _tlOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _tlOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _tlOavailablePredicates :: Predicates
              _tlObetaLeft :: Tp
              _tlObetaRight :: Tp
              _tlObetaUnique :: Int
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectErrors :: TypeErrors
              _tlOcollectWarnings :: Warnings
              _tlOcurrentChunk :: Int
              _tlOdictionaryEnvironment :: DictionaryEnvironment
              _tlOimportEnvironment :: ImportEnvironment
              _tlOmatchIO :: (IO ())
              _tlOmonos :: Monos
              _tlOnamesInScope :: Names
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOparentTree :: InfoTree
              _tlOpatternMatchWarnings :: ([Warning])
              _tlOsubstitution :: FixpointSubstitution
              _tlOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _tlOuniqueChunk :: Int
              _hdIassumptions :: Assumptions
              _hdIbetaUnique :: Int
              _hdIcollectErrors :: TypeErrors
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectWarnings :: Warnings
              _hdIconstraints :: ConstraintSet
              _hdIdictionaryEnvironment :: DictionaryEnvironment
              _hdIelements :: ( ([PatternElement], Bool) )
              _hdIinfoTrees :: InfoTrees
              _hdImatchIO :: (IO ())
              _hdIpatternMatchWarnings :: ([Warning])
              _hdIself :: Alternative
              _hdIunboundNames :: Names
              _hdIuniqueChunk :: Int
              _hdIunrwar :: Warning
              _tlIassumptions :: Assumptions
              _tlIbetaUnique :: Int
              _tlIcollectErrors :: TypeErrors
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectWarnings :: Warnings
              _tlIconstraintslist :: ConstraintSets
              _tlIdictionaryEnvironment :: DictionaryEnvironment
              _tlIelementss :: ([([PatternElement], Bool)])
              _tlIinfoTrees :: InfoTrees
              _tlImatchIO :: (IO ())
              _tlIpatternMatchWarnings :: ([Warning])
              _tlIself :: Alternatives
              _tlIunboundNames :: Names
              _tlIuniqueChunk :: Int
              _tlIunrwars :: ([Warning])
              _lhsOassumptions =
                  _hdIassumptions `combine` _tlIassumptions
              _lhsOconstraintslist =
                  _hdIconstraints : _tlIconstraintslist
              _lhsOinfoTrees =
                  _hdIinfoTrees ++ _tlIinfoTrees
              _lhsOelementss =
                  _hdIelements : _tlIelementss
              _lhsOunrwars =
                  _hdIunrwar   : _tlIunrwars
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _tlIbetaUnique
              _lhsOcollectErrors =
                  _tlIcollectErrors
              _lhsOcollectWarnings =
                  _tlIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _tlIdictionaryEnvironment
              _lhsOmatchIO =
                  _tlImatchIO
              _lhsOpatternMatchWarnings =
                  _tlIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _tlIuniqueChunk
              _hdOallPatterns =
                  _lhsIallPatterns
              _hdOallTypeSchemes =
                  _lhsIallTypeSchemes
              _hdOavailablePredicates =
                  _lhsIavailablePredicates
              _hdObetaLeft =
                  _lhsIbetaLeft
              _hdObetaRight =
                  _lhsIbetaRight
              _hdObetaUnique =
                  _lhsIbetaUnique
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectErrors =
                  _lhsIcollectErrors
              _hdOcollectWarnings =
                  _lhsIcollectWarnings
              _hdOcurrentChunk =
                  _lhsIcurrentChunk
              _hdOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _hdOimportEnvironment =
                  _lhsIimportEnvironment
              _hdOmatchIO =
                  _lhsImatchIO
              _hdOmonos =
                  _lhsImonos
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOparentTree =
                  _lhsIparentTree
              _hdOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _hdOsubstitution =
                  _lhsIsubstitution
              _hdOtypeschemeMap =
                  _lhsItypeschemeMap
              _hdOuniqueChunk =
                  _lhsIuniqueChunk
              _tlOallPatterns =
                  _lhsIallPatterns
              _tlOallTypeSchemes =
                  _lhsIallTypeSchemes
              _tlOavailablePredicates =
                  _lhsIavailablePredicates
              _tlObetaLeft =
                  _lhsIbetaLeft
              _tlObetaRight =
                  _lhsIbetaRight
              _tlObetaUnique =
                  _hdIbetaUnique
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectErrors =
                  _hdIcollectErrors
              _tlOcollectWarnings =
                  _hdIcollectWarnings
              _tlOcurrentChunk =
                  _lhsIcurrentChunk
              _tlOdictionaryEnvironment =
                  _hdIdictionaryEnvironment
              _tlOimportEnvironment =
                  _lhsIimportEnvironment
              _tlOmatchIO =
                  _hdImatchIO
              _tlOmonos =
                  _lhsImonos
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOparentTree =
                  _lhsIparentTree
              _tlOpatternMatchWarnings =
                  _hdIpatternMatchWarnings
              _tlOsubstitution =
                  _lhsIsubstitution
              _tlOtypeschemeMap =
                  _lhsItypeschemeMap
              _tlOuniqueChunk =
                  _hdIuniqueChunk
              ( _hdIassumptions,_hdIbetaUnique,_hdIcollectErrors,_hdIcollectInstances,_hdIcollectWarnings,_hdIconstraints,_hdIdictionaryEnvironment,_hdIelements,_hdIinfoTrees,_hdImatchIO,_hdIpatternMatchWarnings,_hdIself,_hdIunboundNames,_hdIuniqueChunk,_hdIunrwar) =
                  (hd_ _hdOallPatterns _hdOallTypeSchemes _hdOavailablePredicates _hdObetaLeft _hdObetaRight _hdObetaUnique _hdOclassEnvironment _hdOcollectErrors _hdOcollectWarnings _hdOcurrentChunk _hdOdictionaryEnvironment _hdOimportEnvironment _hdOmatchIO _hdOmonos _hdOnamesInScope _hdOorderedTypeSynonyms _hdOparentTree _hdOpatternMatchWarnings _hdOsubstitution _hdOtypeschemeMap _hdOuniqueChunk )
              ( _tlIassumptions,_tlIbetaUnique,_tlIcollectErrors,_tlIcollectInstances,_tlIcollectWarnings,_tlIconstraintslist,_tlIdictionaryEnvironment,_tlIelementss,_tlIinfoTrees,_tlImatchIO,_tlIpatternMatchWarnings,_tlIself,_tlIunboundNames,_tlIuniqueChunk,_tlIunrwars) =
                  (tl_ _tlOallPatterns _tlOallTypeSchemes _tlOavailablePredicates _tlObetaLeft _tlObetaRight _tlObetaUnique _tlOclassEnvironment _tlOcollectErrors _tlOcollectWarnings _tlOcurrentChunk _tlOdictionaryEnvironment _tlOimportEnvironment _tlOmatchIO _tlOmonos _tlOnamesInScope _tlOorderedTypeSynonyms _tlOparentTree _tlOpatternMatchWarnings _tlOsubstitution _tlOtypeschemeMap _tlOuniqueChunk )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraintslist,_lhsOdictionaryEnvironment,_lhsOelementss,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOunrwars)))
sem_Alternatives_Nil :: T_Alternatives 
sem_Alternatives_Nil  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaLeft
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraintslist :: ConstraintSets
              _lhsOinfoTrees :: InfoTrees
              _lhsOelementss :: ([([PatternElement], Bool)])
              _lhsOunrwars :: ([Warning])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Alternatives
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOassumptions =
                  noAssumptions
              _lhsOconstraintslist =
                  []
              _lhsOinfoTrees =
                  []
              _lhsOelementss =
                  []
              _lhsOunrwars =
                  []
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraintslist,_lhsOdictionaryEnvironment,_lhsOelementss,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOunrwars)))
-- AnnotatedType -----------------------------------------------
-- cata
sem_AnnotatedType :: AnnotatedType  ->
                     T_AnnotatedType 
sem_AnnotatedType (AnnotatedType_AnnotatedType _range _strict _type )  =
    (sem_AnnotatedType_AnnotatedType (sem_Range _range ) _strict (sem_Type _type ) )
-- semantic domain
type T_AnnotatedType  = Names ->
                        ( AnnotatedType,Names)
sem_AnnotatedType_AnnotatedType :: T_Range  ->
                                   Bool ->
                                   T_Type  ->
                                   T_AnnotatedType 
sem_AnnotatedType_AnnotatedType range_ strict_ type_  =
    (\ _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: AnnotatedType
              _rangeIself :: Range
              _typeIself :: Type
              _lhsOunboundNames =
                  []
              _self =
                  AnnotatedType_AnnotatedType _rangeIself strict_ _typeIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  (range_ )
              ( _typeIself) =
                  (type_ )
          in  ( _lhsOself,_lhsOunboundNames)))
-- AnnotatedTypes ----------------------------------------------
-- cata
sem_AnnotatedTypes :: AnnotatedTypes  ->
                      T_AnnotatedTypes 
sem_AnnotatedTypes list  =
    (Prelude.foldr sem_AnnotatedTypes_Cons sem_AnnotatedTypes_Nil (Prelude.map sem_AnnotatedType list) )
-- semantic domain
type T_AnnotatedTypes  = Names ->
                         ( AnnotatedTypes,Names)
sem_AnnotatedTypes_Cons :: T_AnnotatedType  ->
                           T_AnnotatedTypes  ->
                           T_AnnotatedTypes 
sem_AnnotatedTypes_Cons hd_ tl_  =
    (\ _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: AnnotatedTypes
              _hdOnamesInScope :: Names
              _tlOnamesInScope :: Names
              _hdIself :: AnnotatedType
              _hdIunboundNames :: Names
              _tlIself :: AnnotatedTypes
              _tlIunboundNames :: Names
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOnamesInScope =
                  _lhsInamesInScope
              _tlOnamesInScope =
                  _lhsInamesInScope
              ( _hdIself,_hdIunboundNames) =
                  (hd_ _hdOnamesInScope )
              ( _tlIself,_tlIunboundNames) =
                  (tl_ _tlOnamesInScope )
          in  ( _lhsOself,_lhsOunboundNames)))
sem_AnnotatedTypes_Nil :: T_AnnotatedTypes 
sem_AnnotatedTypes_Nil  =
    (\ _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: AnnotatedTypes
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOself,_lhsOunboundNames)))
-- Body --------------------------------------------------------
-- cata
sem_Body :: Body  ->
            T_Body 
sem_Body (Body_Body _range _importdeclarations _declarations )  =
    (sem_Body_Body (sem_Range _range ) (sem_ImportDeclarations _importdeclarations ) (sem_Declarations _declarations ) )
-- semantic domain
type T_Body  = ([((Expression, [String]), Core_TypingStrategy)]) ->
               (M.Map NameWithRange TpScheme) ->
               Predicates ->
               Int ->
               ClassEnvironment ->
               TypeErrors ->
               Warnings ->
               Int ->
               DictionaryEnvironment ->
               ImportEnvironment ->
               (IO ()) ->
               Monos ->
               Names ->
               OrderedTypeSynonyms ->
               ([Warning]) ->
               FixpointSubstitution ->
               (M.Map Int (Scheme Predicates)) ->
               Int ->
               ( Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,Names,DictionaryEnvironment,InfoTree,(IO ()),([Warning]),Body,TypeEnvironment,Names,Int)
sem_Body_Body :: T_Range  ->
                 T_ImportDeclarations  ->
                 T_Declarations  ->
                 T_Body 
sem_Body_Body range_ importdeclarations_ declarations_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _declarationsObindingGroups :: BindingGroups
              _lhsOassumptions :: Assumptions
              _lhsObetaUnique :: Int
              _lhsOcollectWarnings :: Warnings
              _lhsOcollectErrors :: TypeErrors
              _lhsOtoplevelTypes :: TypeEnvironment
              _declarationsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _lhsOinfoTree :: InfoTree
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Body
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _declarationsOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _declarationsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _declarationsOavailablePredicates :: Predicates
              _declarationsObetaUnique :: Int
              _declarationsOclassEnvironment :: ClassEnvironment
              _declarationsOcollectErrors :: TypeErrors
              _declarationsOcollectWarnings :: Warnings
              _declarationsOcurrentChunk :: Int
              _declarationsOdictionaryEnvironment :: DictionaryEnvironment
              _declarationsOimportEnvironment :: ImportEnvironment
              _declarationsOinheritedBDG :: InheritedBDG
              _declarationsOmatchIO :: (IO ())
              _declarationsOmonos :: Monos
              _declarationsOnamesInScope :: Names
              _declarationsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _declarationsOparentTree :: InfoTree
              _declarationsOpatternMatchWarnings :: ([Warning])
              _declarationsOsubstitution :: FixpointSubstitution
              _declarationsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _declarationsOuniqueChunk :: Int
              _rangeIself :: Range
              _importdeclarationsIself :: ImportDeclarations
              _declarationsIbetaUnique :: Int
              _declarationsIbindingGroups :: BindingGroups
              _declarationsIcollectErrors :: TypeErrors
              _declarationsIcollectInstances :: ([(Name, Instance)])
              _declarationsIcollectWarnings :: Warnings
              _declarationsIdeclVarNames :: Names
              _declarationsIdictionaryEnvironment :: DictionaryEnvironment
              _declarationsIinfoTrees :: InfoTrees
              _declarationsImatchIO :: (IO ())
              _declarationsIpatternMatchWarnings :: ([Warning])
              _declarationsIrestrictedNames :: Names
              _declarationsIself :: Declarations
              _declarationsIsimplePatNames :: Names
              _declarationsItypeSignatures :: TypeEnvironment
              _declarationsIunboundNames :: Names
              _declarationsIuniqueChunk :: Int
              _declarationsObindingGroups =
                  []
              __tup3 =
                  (typeEnvironment _lhsIimportEnvironment .:::. _aset) _cinfo
              (_csetBinds,_) =
                  __tup3
              (_,_lhsOassumptions) =
                  __tup3
              _constraints =
                  _csetBinds .>>. _cset
              __tup4 =
                  let inputBDG = (True, _lhsIcurrentChunk, _declarationsIuniqueChunk, _lhsImonos, _declarationsItypeSignatures, Nothing, _declarationsIbetaUnique)
                  in performBindingGroup inputBDG _declarationsIbindingGroups
              (_aset,_,_,_,_,_) =
                  __tup4
              (_,_cset,_,_,_,_) =
                  __tup4
              (_,_,_inheritedBDG,_,_,_) =
                  __tup4
              (_,_,_,_chunkNr,_,_) =
                  __tup4
              (_,_,_,_,_lhsObetaUnique,_) =
                  __tup4
              (_,_,_,_,_,_implicitsFM) =
                  __tup4
              _inferredTypes =
                  findInferredTypes _lhsItypeschemeMap _implicitsFM
              _lhsOcollectWarnings =
                  missingTypeSignature True _declarationsIsimplePatNames _inferredTypes
                  ++ _declarationsIcollectWarnings
              _lhsOcollectErrors =
                  restrictedNameErrors _inferredTypes _declarationsIrestrictedNames
                  ++ _declarationsIcollectErrors
              _lhsOtoplevelTypes =
                  _declarationsItypeSignatures `M.union` _inferredTypes
              _allTypeSchemes =
                  _localTypes `M.union` _lhsIallTypeSchemes
              _localTypes =
                  makeLocalTypeEnv (_declarationsItypeSignatures `M.union` _inferredTypes) _declarationsIbindingGroups
              _declarationsOtypeSignatures =
                  M.empty
              _lhsOuniqueChunk =
                  _chunkNr
              _cinfo =
                  \name -> variableConstraint "variable" (nameToUHA_Expr name)
                     [ FolkloreConstraint, HasTrustFactor 10.0, IsImported name ]
              _declInfo =
                  LocalInfo { self = UHA_Decls _declarationsIself
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  root _declInfo _declarationsIinfoTrees
              _lhsOinfoTree =
                  _parentTree
              _lhsOcollectInstances =
                  _declarationsIcollectInstances
              _lhsOdeclVarNames =
                  _declarationsIdeclVarNames
              _lhsOunboundNames =
                  _declarationsIunboundNames
              _self =
                  Body_Body _rangeIself _importdeclarationsIself _declarationsIself
              _lhsOself =
                  _self
              _lhsOconstraints =
                  _constraints
              _lhsOdictionaryEnvironment =
                  _declarationsIdictionaryEnvironment
              _lhsOmatchIO =
                  _declarationsImatchIO
              _lhsOpatternMatchWarnings =
                  _declarationsIpatternMatchWarnings
              _declarationsOallPatterns =
                  _lhsIallPatterns
              _declarationsOallTypeSchemes =
                  _allTypeSchemes
              _declarationsOavailablePredicates =
                  _lhsIavailablePredicates
              _declarationsObetaUnique =
                  _lhsIbetaUnique
              _declarationsOclassEnvironment =
                  _lhsIclassEnvironment
              _declarationsOcollectErrors =
                  _lhsIcollectErrors
              _declarationsOcollectWarnings =
                  _lhsIcollectWarnings
              _declarationsOcurrentChunk =
                  _lhsIcurrentChunk
              _declarationsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _declarationsOimportEnvironment =
                  _lhsIimportEnvironment
              _declarationsOinheritedBDG =
                  _inheritedBDG
              _declarationsOmatchIO =
                  _lhsImatchIO
              _declarationsOmonos =
                  _lhsImonos
              _declarationsOnamesInScope =
                  _lhsInamesInScope
              _declarationsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _declarationsOparentTree =
                  _parentTree
              _declarationsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _declarationsOsubstitution =
                  _lhsIsubstitution
              _declarationsOtypeschemeMap =
                  _lhsItypeschemeMap
              _declarationsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _importdeclarationsIself) =
                  (importdeclarations_ )
              ( _declarationsIbetaUnique,_declarationsIbindingGroups,_declarationsIcollectErrors,_declarationsIcollectInstances,_declarationsIcollectWarnings,_declarationsIdeclVarNames,_declarationsIdictionaryEnvironment,_declarationsIinfoTrees,_declarationsImatchIO,_declarationsIpatternMatchWarnings,_declarationsIrestrictedNames,_declarationsIself,_declarationsIsimplePatNames,_declarationsItypeSignatures,_declarationsIunboundNames,_declarationsIuniqueChunk) =
                  (declarations_ _declarationsOallPatterns _declarationsOallTypeSchemes _declarationsOavailablePredicates _declarationsObetaUnique _declarationsObindingGroups _declarationsOclassEnvironment _declarationsOcollectErrors _declarationsOcollectWarnings _declarationsOcurrentChunk _declarationsOdictionaryEnvironment _declarationsOimportEnvironment _declarationsOinheritedBDG _declarationsOmatchIO _declarationsOmonos _declarationsOnamesInScope _declarationsOorderedTypeSynonyms _declarationsOparentTree _declarationsOpatternMatchWarnings _declarationsOsubstitution _declarationsOtypeSignatures _declarationsOtypeschemeMap _declarationsOuniqueChunk )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOself,_lhsOtoplevelTypes,_lhsOunboundNames,_lhsOuniqueChunk)))
-- Constructor -------------------------------------------------
-- cata
sem_Constructor :: Constructor  ->
                   T_Constructor 
sem_Constructor (Constructor_Constructor _range _constructor _types )  =
    (sem_Constructor_Constructor (sem_Range _range ) (sem_Name _constructor ) (sem_AnnotatedTypes _types ) )
sem_Constructor (Constructor_Infix _range _leftType _constructorOperator _rightType )  =
    (sem_Constructor_Infix (sem_Range _range ) (sem_AnnotatedType _leftType ) (sem_Name _constructorOperator ) (sem_AnnotatedType _rightType ) )
sem_Constructor (Constructor_Record _range _constructor _fieldDeclarations )  =
    (sem_Constructor_Record (sem_Range _range ) (sem_Name _constructor ) (sem_FieldDeclarations _fieldDeclarations ) )
-- semantic domain
type T_Constructor  = Names ->
                      ( Constructor,Names)
sem_Constructor_Constructor :: T_Range  ->
                               T_Name  ->
                               T_AnnotatedTypes  ->
                               T_Constructor 
sem_Constructor_Constructor range_ constructor_ types_  =
    (\ _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: Constructor
              _typesOnamesInScope :: Names
              _rangeIself :: Range
              _constructorIself :: Name
              _typesIself :: AnnotatedTypes
              _typesIunboundNames :: Names
              _lhsOunboundNames =
                  _typesIunboundNames
              _self =
                  Constructor_Constructor _rangeIself _constructorIself _typesIself
              _lhsOself =
                  _self
              _typesOnamesInScope =
                  _lhsInamesInScope
              ( _rangeIself) =
                  (range_ )
              ( _constructorIself) =
                  (constructor_ )
              ( _typesIself,_typesIunboundNames) =
                  (types_ _typesOnamesInScope )
          in  ( _lhsOself,_lhsOunboundNames)))
sem_Constructor_Infix :: T_Range  ->
                         T_AnnotatedType  ->
                         T_Name  ->
                         T_AnnotatedType  ->
                         T_Constructor 
sem_Constructor_Infix range_ leftType_ constructorOperator_ rightType_  =
    (\ _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: Constructor
              _leftTypeOnamesInScope :: Names
              _rightTypeOnamesInScope :: Names
              _rangeIself :: Range
              _leftTypeIself :: AnnotatedType
              _leftTypeIunboundNames :: Names
              _constructorOperatorIself :: Name
              _rightTypeIself :: AnnotatedType
              _rightTypeIunboundNames :: Names
              _lhsOunboundNames =
                  _leftTypeIunboundNames ++ _rightTypeIunboundNames
              _self =
                  Constructor_Infix _rangeIself _leftTypeIself _constructorOperatorIself _rightTypeIself
              _lhsOself =
                  _self
              _leftTypeOnamesInScope =
                  _lhsInamesInScope
              _rightTypeOnamesInScope =
                  _lhsInamesInScope
              ( _rangeIself) =
                  (range_ )
              ( _leftTypeIself,_leftTypeIunboundNames) =
                  (leftType_ _leftTypeOnamesInScope )
              ( _constructorOperatorIself) =
                  (constructorOperator_ )
              ( _rightTypeIself,_rightTypeIunboundNames) =
                  (rightType_ _rightTypeOnamesInScope )
          in  ( _lhsOself,_lhsOunboundNames)))
sem_Constructor_Record :: T_Range  ->
                          T_Name  ->
                          T_FieldDeclarations  ->
                          T_Constructor 
sem_Constructor_Record range_ constructor_ fieldDeclarations_  =
    (\ _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: Constructor
              _fieldDeclarationsOnamesInScope :: Names
              _rangeIself :: Range
              _constructorIself :: Name
              _fieldDeclarationsIself :: FieldDeclarations
              _fieldDeclarationsIunboundNames :: Names
              _lhsOunboundNames =
                  _fieldDeclarationsIunboundNames
              _self =
                  Constructor_Record _rangeIself _constructorIself _fieldDeclarationsIself
              _lhsOself =
                  _self
              _fieldDeclarationsOnamesInScope =
                  _lhsInamesInScope
              ( _rangeIself) =
                  (range_ )
              ( _constructorIself) =
                  (constructor_ )
              ( _fieldDeclarationsIself,_fieldDeclarationsIunboundNames) =
                  (fieldDeclarations_ _fieldDeclarationsOnamesInScope )
          in  ( _lhsOself,_lhsOunboundNames)))
-- Constructors ------------------------------------------------
-- cata
sem_Constructors :: Constructors  ->
                    T_Constructors 
sem_Constructors list  =
    (Prelude.foldr sem_Constructors_Cons sem_Constructors_Nil (Prelude.map sem_Constructor list) )
-- semantic domain
type T_Constructors  = Names ->
                       ( Constructors,Names)
sem_Constructors_Cons :: T_Constructor  ->
                         T_Constructors  ->
                         T_Constructors 
sem_Constructors_Cons hd_ tl_  =
    (\ _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: Constructors
              _hdOnamesInScope :: Names
              _tlOnamesInScope :: Names
              _hdIself :: Constructor
              _hdIunboundNames :: Names
              _tlIself :: Constructors
              _tlIunboundNames :: Names
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOnamesInScope =
                  _lhsInamesInScope
              _tlOnamesInScope =
                  _lhsInamesInScope
              ( _hdIself,_hdIunboundNames) =
                  (hd_ _hdOnamesInScope )
              ( _tlIself,_tlIunboundNames) =
                  (tl_ _tlOnamesInScope )
          in  ( _lhsOself,_lhsOunboundNames)))
sem_Constructors_Nil :: T_Constructors 
sem_Constructors_Nil  =
    (\ _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: Constructors
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOself,_lhsOunboundNames)))
-- ContextItem -------------------------------------------------
-- cata
sem_ContextItem :: ContextItem  ->
                   T_ContextItem 
sem_ContextItem (ContextItem_ContextItem _range _name _types )  =
    (sem_ContextItem_ContextItem (sem_Range _range ) (sem_Name _name ) (sem_Types _types ) )
-- semantic domain
type T_ContextItem  = ( ContextItem)
sem_ContextItem_ContextItem :: T_Range  ->
                               T_Name  ->
                               T_Types  ->
                               T_ContextItem 
sem_ContextItem_ContextItem range_ name_ types_  =
    (let _lhsOself :: ContextItem
         _rangeIself :: Range
         _nameIself :: Name
         _typesIself :: Types
         _tyconEnv =
             internalError "PartialSyntax.ag" "n/a" "ContextItem.ContextItem"
         _self =
             ContextItem_ContextItem _rangeIself _nameIself _typesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _typesIself) =
             (types_ )
     in  ( _lhsOself))
-- ContextItems ------------------------------------------------
-- cata
sem_ContextItems :: ContextItems  ->
                    T_ContextItems 
sem_ContextItems list  =
    (Prelude.foldr sem_ContextItems_Cons sem_ContextItems_Nil (Prelude.map sem_ContextItem list) )
-- semantic domain
type T_ContextItems  = ( ContextItems)
sem_ContextItems_Cons :: T_ContextItem  ->
                         T_ContextItems  ->
                         T_ContextItems 
sem_ContextItems_Cons hd_ tl_  =
    (let _lhsOself :: ContextItems
         _hdIself :: ContextItem
         _tlIself :: ContextItems
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_ContextItems_Nil :: T_ContextItems 
sem_ContextItems_Nil  =
    (let _lhsOself :: ContextItems
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Declaration -------------------------------------------------
-- cata
sem_Declaration :: Declaration  ->
                   T_Declaration 
sem_Declaration (Declaration_Class _range _context _simpletype _where )  =
    (sem_Declaration_Class (sem_Range _range ) (sem_ContextItems _context ) (sem_SimpleType _simpletype ) (sem_MaybeDeclarations _where ) )
sem_Declaration (Declaration_Data _range _context _simpletype _constructors _derivings )  =
    (sem_Declaration_Data (sem_Range _range ) (sem_ContextItems _context ) (sem_SimpleType _simpletype ) (sem_Constructors _constructors ) (sem_Names _derivings ) )
sem_Declaration (Declaration_Default _range _types )  =
    (sem_Declaration_Default (sem_Range _range ) (sem_Types _types ) )
sem_Declaration (Declaration_Empty _range )  =
    (sem_Declaration_Empty (sem_Range _range ) )
sem_Declaration (Declaration_Fixity _range _fixity _priority _operators )  =
    (sem_Declaration_Fixity (sem_Range _range ) (sem_Fixity _fixity ) (sem_MaybeInt _priority ) (sem_Names _operators ) )
sem_Declaration (Declaration_FunctionBindings _range _bindings )  =
    (sem_Declaration_FunctionBindings (sem_Range _range ) (sem_FunctionBindings _bindings ) )
sem_Declaration (Declaration_Instance _range _context _name _types _where )  =
    (sem_Declaration_Instance (sem_Range _range ) (sem_ContextItems _context ) (sem_Name _name ) (sem_Types _types ) (sem_MaybeDeclarations _where ) )
sem_Declaration (Declaration_Newtype _range _context _simpletype _constructor _derivings )  =
    (sem_Declaration_Newtype (sem_Range _range ) (sem_ContextItems _context ) (sem_SimpleType _simpletype ) (sem_Constructor _constructor ) (sem_Names _derivings ) )
sem_Declaration (Declaration_PatternBinding _range _pattern _righthandside )  =
    (sem_Declaration_PatternBinding (sem_Range _range ) (sem_Pattern _pattern ) (sem_RightHandSide _righthandside ) )
sem_Declaration (Declaration_Type _range _simpletype _type )  =
    (sem_Declaration_Type (sem_Range _range ) (sem_SimpleType _simpletype ) (sem_Type _type ) )
sem_Declaration (Declaration_TypeSignature _range _names _type )  =
    (sem_Declaration_TypeSignature (sem_Range _range ) (sem_Names _names ) (sem_Type _type ) )
-- semantic domain
type T_Declaration  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                      (M.Map NameWithRange TpScheme) ->
                      Predicates ->
                      Int ->
                      BindingGroups ->
                      ClassEnvironment ->
                      TypeErrors ->
                      Warnings ->
                      Int ->
                      DictionaryEnvironment ->
                      ImportEnvironment ->
                      InheritedBDG ->
                      (IO ()) ->
                      Monos ->
                      Names ->
                      OrderedTypeSynonyms ->
                      InfoTree ->
                      ([Warning]) ->
                      FixpointSubstitution ->
                      TypeEnvironment ->
                      (M.Map Int (Scheme Predicates)) ->
                      Int ->
                      ( Int,BindingGroups,TypeErrors,([(Name, Instance)]),Warnings,Names,DictionaryEnvironment,InfoTrees,(IO ()),([Warning]),Names,Declaration,Names,TypeEnvironment,Names,Int)
sem_Declaration_Class :: T_Range  ->
                         T_ContextItems  ->
                         T_SimpleType  ->
                         T_MaybeDeclarations  ->
                         T_Declaration 
sem_Declaration_Class range_ context_ simpletype_ where_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _whereOunboundNames :: Names
              _lhsOdeclVarNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsObetaUnique :: Int
              _lhsObindingGroups :: BindingGroups
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOinfoTrees :: InfoTrees
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _whereOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _whereOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _whereOassumptions :: Assumptions
              _whereOavailablePredicates :: Predicates
              _whereObetaUnique :: Int
              _whereOclassEnvironment :: ClassEnvironment
              _whereOcollectErrors :: TypeErrors
              _whereOcollectWarnings :: Warnings
              _whereOconstraints :: ConstraintSet
              _whereOcurrentChunk :: Int
              _whereOdictionaryEnvironment :: DictionaryEnvironment
              _whereOimportEnvironment :: ImportEnvironment
              _whereOmatchIO :: (IO ())
              _whereOmonos :: Monos
              _whereOnamesInScope :: Names
              _whereOorderedTypeSynonyms :: OrderedTypeSynonyms
              _whereOparentTree :: InfoTree
              _whereOpatternMatchWarnings :: ([Warning])
              _whereOsubstitution :: FixpointSubstitution
              _whereOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _whereOuniqueChunk :: Int
              _rangeIself :: Range
              _contextIself :: ContextItems
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _whereIassumptions :: Assumptions
              _whereIbetaUnique :: Int
              _whereIcollectErrors :: TypeErrors
              _whereIcollectInstances :: ([(Name, Instance)])
              _whereIcollectWarnings :: Warnings
              _whereIconstraints :: ConstraintSet
              _whereIdeclVarNames :: Names
              _whereIdictionaryEnvironment :: DictionaryEnvironment
              _whereIinfoTrees :: InfoTrees
              _whereIlocalTypes :: (M.Map NameWithRange TpScheme)
              _whereImatchIO :: (IO ())
              _whereInamesInScope :: Names
              _whereIpatternMatchWarnings :: ([Warning])
              _whereIself :: MaybeDeclarations
              _whereIunboundNames :: Names
              _whereIuniqueChunk :: Int
              _whereOunboundNames =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOcollectInstances =
                  _whereIcollectInstances
              _lhsOrestrictedNames =
                  []
              _lhsOsimplePatNames =
                  []
              _lhsOunboundNames =
                  _whereIunboundNames
              _self =
                  Declaration_Class _rangeIself _contextIself _simpletypeIself _whereIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _whereIbetaUnique
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOcollectErrors =
                  _whereIcollectErrors
              _lhsOcollectWarnings =
                  _whereIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _whereIdictionaryEnvironment
              _lhsOinfoTrees =
                  _whereIinfoTrees
              _lhsOmatchIO =
                  _whereImatchIO
              _lhsOpatternMatchWarnings =
                  _whereIpatternMatchWarnings
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOuniqueChunk =
                  _whereIuniqueChunk
              _whereOallPatterns =
                  _lhsIallPatterns
              _whereOallTypeSchemes =
                  _lhsIallTypeSchemes
              _whereOassumptions =
                  error "missing rule: Declaration.Class.where.assumptions"
              _whereOavailablePredicates =
                  _lhsIavailablePredicates
              _whereObetaUnique =
                  _lhsIbetaUnique
              _whereOclassEnvironment =
                  _lhsIclassEnvironment
              _whereOcollectErrors =
                  _lhsIcollectErrors
              _whereOcollectWarnings =
                  _lhsIcollectWarnings
              _whereOconstraints =
                  error "missing rule: Declaration.Class.where.constraints"
              _whereOcurrentChunk =
                  _lhsIcurrentChunk
              _whereOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _whereOimportEnvironment =
                  _lhsIimportEnvironment
              _whereOmatchIO =
                  _lhsImatchIO
              _whereOmonos =
                  _lhsImonos
              _whereOnamesInScope =
                  _lhsInamesInScope
              _whereOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _whereOparentTree =
                  _lhsIparentTree
              _whereOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _whereOsubstitution =
                  _lhsIsubstitution
              _whereOtypeschemeMap =
                  _lhsItypeschemeMap
              _whereOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _whereIassumptions,_whereIbetaUnique,_whereIcollectErrors,_whereIcollectInstances,_whereIcollectWarnings,_whereIconstraints,_whereIdeclVarNames,_whereIdictionaryEnvironment,_whereIinfoTrees,_whereIlocalTypes,_whereImatchIO,_whereInamesInScope,_whereIpatternMatchWarnings,_whereIself,_whereIunboundNames,_whereIuniqueChunk) =
                  (where_ _whereOallPatterns _whereOallTypeSchemes _whereOassumptions _whereOavailablePredicates _whereObetaUnique _whereOclassEnvironment _whereOcollectErrors _whereOcollectWarnings _whereOconstraints _whereOcurrentChunk _whereOdictionaryEnvironment _whereOimportEnvironment _whereOmatchIO _whereOmonos _whereOnamesInScope _whereOorderedTypeSynonyms _whereOparentTree _whereOpatternMatchWarnings _whereOsubstitution _whereOtypeschemeMap _whereOunboundNames _whereOuniqueChunk )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_Declaration_Data :: T_Range  ->
                        T_ContextItems  ->
                        T_SimpleType  ->
                        T_Constructors  ->
                        T_Names  ->
                        T_Declaration 
sem_Declaration_Data range_ context_ simpletype_ constructors_ derivings_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOinfoTrees :: InfoTrees
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsObetaUnique :: Int
              _lhsObindingGroups :: BindingGroups
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _constructorsOnamesInScope :: Names
              _rangeIself :: Range
              _contextIself :: ContextItems
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _constructorsIself :: Constructors
              _constructorsIunboundNames :: Names
              _derivingsIself :: Names
              _lhsOcollectInstances =
                  [ (cl, makeInstance (show cl) (length _simpletypeItypevariables) (show _simpletypeIname) )
                  | cl <- _derivingsIself
                  ]
              _lhsOinfoTrees =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOsimplePatNames =
                  []
              _lhsOunboundNames =
                  _constructorsIunboundNames
              _self =
                  Declaration_Data _rangeIself _contextIself _simpletypeIself _constructorsIself _derivingsIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              _constructorsOnamesInScope =
                  _lhsInamesInScope
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _constructorsIself,_constructorsIunboundNames) =
                  (constructors_ _constructorsOnamesInScope )
              ( _derivingsIself) =
                  (derivings_ )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_Declaration_Default :: T_Range  ->
                           T_Types  ->
                           T_Declaration 
sem_Declaration_Default range_ types_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsObetaUnique :: Int
              _lhsObindingGroups :: BindingGroups
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOinfoTrees :: InfoTrees
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _rangeIself :: Range
              _typesIself :: Types
              _infoTrees =
                  globalInfoError
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOsimplePatNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Declaration_Default _rangeIself _typesIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOinfoTrees =
                  _infoTrees
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _typesIself) =
                  (types_ )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_Declaration_Empty :: T_Range  ->
                         T_Declaration 
sem_Declaration_Empty range_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOinfoTrees :: InfoTrees
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsObetaUnique :: Int
              _lhsObindingGroups :: BindingGroups
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _rangeIself :: Range
              _lhsOinfoTrees =
                  []
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOsimplePatNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Declaration_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_Declaration_Fixity :: T_Range  ->
                          T_Fixity  ->
                          T_MaybeInt  ->
                          T_Names  ->
                          T_Declaration 
sem_Declaration_Fixity range_ fixity_ priority_ operators_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOinfoTrees :: InfoTrees
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsObetaUnique :: Int
              _lhsObindingGroups :: BindingGroups
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _rangeIself :: Range
              _fixityIself :: Fixity
              _priorityIself :: MaybeInt
              _operatorsIself :: Names
              _lhsOinfoTrees =
                  []
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOsimplePatNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Declaration_Fixity _rangeIself _fixityIself _priorityIself _operatorsIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _fixityIself) =
                  (fixity_ )
              ( _priorityIself) =
                  (priority_ )
              ( _operatorsIself) =
                  (operators_ )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_Declaration_FunctionBindings :: T_Range  ->
                                    T_FunctionBindings  ->
                                    T_Declaration 
sem_Declaration_FunctionBindings range_ bindings_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsObindingGroups :: BindingGroups
              _bindingsObetaUnique :: Int
              _bindingsOmonos :: Monos
              _bindingsOavailablePredicates :: Predicates
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _bindingsOcurrentChunk :: Int
              _lhsOinfoTrees :: InfoTrees
              _lhsOdeclVarNames :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOmatchIO :: (IO ())
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _bindingsOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _bindingsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _bindingsObetaRight :: Tp
              _bindingsObetasLeft :: Tps
              _bindingsOclassEnvironment :: ClassEnvironment
              _bindingsOcollectErrors :: TypeErrors
              _bindingsOcollectWarnings :: Warnings
              _bindingsOdictionaryEnvironment :: DictionaryEnvironment
              _bindingsOimportEnvironment :: ImportEnvironment
              _bindingsOmatchIO :: (IO ())
              _bindingsOnamesInScope :: Names
              _bindingsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _bindingsOparentTree :: InfoTree
              _bindingsOpatternMatchWarnings :: ([Warning])
              _bindingsOsubstitution :: FixpointSubstitution
              _bindingsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _bindingsOuniqueChunk :: Int
              _rangeIself :: Range
              _bindingsIargcount :: Int
              _bindingsIassumptions :: Assumptions
              _bindingsIbetaUnique :: Int
              _bindingsIcollectErrors :: TypeErrors
              _bindingsIcollectInstances :: ([(Name, Instance)])
              _bindingsIcollectWarnings :: Warnings
              _bindingsIconstraintslist :: ConstraintSets
              _bindingsIdictionaryEnvironment :: DictionaryEnvironment
              _bindingsIelementss :: ([([PatternElement], Bool)])
              _bindingsIinfoTrees :: InfoTrees
              _bindingsImatchIO :: (IO ())
              _bindingsIname :: Name
              _bindingsInumberOfPatterns :: Int
              _bindingsIpatternMatchWarnings :: ([Warning])
              _bindingsIself :: FunctionBindings
              _bindingsIunboundNames :: Names
              _bindingsIuniqueChunk :: Int
              _bindingsIunrwars :: ([Warning])
              _lhsObindingGroups =
                  _mybdggrp : _lhsIbindingGroups
              _bindingsObetaUnique =
                  _lhsIbetaUnique + 2 + _bindingsInumberOfPatterns
              _bindingsOmonos =
                  findMono _bindingsIname _lhsIinheritedBDG ++ _lhsImonos
              _beta =
                  TVar _lhsIbetaUnique
              _betaRight =
                  TVar (_lhsIbetaUnique + 1)
              _betasLeft =
                  take _bindingsInumberOfPatterns (map TVar [_lhsIbetaUnique + 2..])
              _newcon =
                  (_beta .==. foldr (.->.) _betaRight _betasLeft) _cinfo
              _mybdggrp =
                  ( M.singleton _bindingsIname _beta
                  , _bindingsIassumptions
                  , [ Node [ Phase (-1) [_newcon]
                           , Receive _lhsIbetaUnique
                           , Node _bindingsIconstraintslist
                           ]
                    ]
                  )
              _declPredicates =
                  let scheme     = M.findWithDefault err (NameWithRange _bindingsIname) _lhsIallTypeSchemes
                      predicates = matchTypeWithScheme _lhsIorderedTypeSynonyms
                                      (_lhsIsubstitution |-> _beta)
                                      (_lhsIsubstitution |-> scheme)
                      err = internalError "TypeInferenceOverloading.ag" "n/a" "could not find type for function binding"
                  in expandPredicates _lhsIorderedTypeSynonyms predicates
              _bindingsOavailablePredicates =
                  _declPredicates ++ _lhsIavailablePredicates
              _lhsOdictionaryEnvironment =
                  addForDeclaration _bindingsIname _declPredicates _bindingsIdictionaryEnvironment
              _bindingsOcurrentChunk =
                  findCurrentChunk _bindingsIname _lhsIinheritedBDG
              _cinfo =
                  resultConstraint "function bindings (INTERNAL ERROR)" _parentTree
                     [ FolkloreConstraint, highlyTrusted, FuntionBindingEdge _bindingsInumberOfPatterns ]
              _localInfo =
                  LocalInfo { self = UHA_Decl _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo _bindingsIinfoTrees
              _lhsOinfoTrees =
                  [_parentTree]
              _lhsOdeclVarNames =
                  [_bindingsIname]
              _lhsOpatternMatchWarnings =
                  patternMatchWarnings _lhsIimportEnvironment
                                       _lhsIsubstitution
                                       _beta
                                       (take _bindingsIargcount . fst . functionSpine)
                                       _bindingsIelementss
                                       _rangeIself
                                       (Just _bindingsIname)
                                       True
                                       _bindingsIunrwars
                                       "function bindings"
                                       "="
                  ++ _bindingsIpatternMatchWarnings
              _lhsOcollectInstances =
                  _bindingsIcollectInstances
              _lhsOrestrictedNames =
                  []
              _lhsOsimplePatNames =
                  []
              _lhsOunboundNames =
                  _bindingsIunboundNames
              _self =
                  Declaration_FunctionBindings _rangeIself _bindingsIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _bindingsIbetaUnique
              _lhsOcollectErrors =
                  _bindingsIcollectErrors
              _lhsOcollectWarnings =
                  _bindingsIcollectWarnings
              _lhsOmatchIO =
                  _bindingsImatchIO
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOuniqueChunk =
                  _bindingsIuniqueChunk
              _bindingsOallPatterns =
                  _lhsIallPatterns
              _bindingsOallTypeSchemes =
                  _lhsIallTypeSchemes
              _bindingsObetaRight =
                  _betaRight
              _bindingsObetasLeft =
                  _betasLeft
              _bindingsOclassEnvironment =
                  _lhsIclassEnvironment
              _bindingsOcollectErrors =
                  _lhsIcollectErrors
              _bindingsOcollectWarnings =
                  _lhsIcollectWarnings
              _bindingsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _bindingsOimportEnvironment =
                  _lhsIimportEnvironment
              _bindingsOmatchIO =
                  _lhsImatchIO
              _bindingsOnamesInScope =
                  _lhsInamesInScope
              _bindingsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _bindingsOparentTree =
                  _parentTree
              _bindingsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _bindingsOsubstitution =
                  _lhsIsubstitution
              _bindingsOtypeschemeMap =
                  _lhsItypeschemeMap
              _bindingsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _bindingsIargcount,_bindingsIassumptions,_bindingsIbetaUnique,_bindingsIcollectErrors,_bindingsIcollectInstances,_bindingsIcollectWarnings,_bindingsIconstraintslist,_bindingsIdictionaryEnvironment,_bindingsIelementss,_bindingsIinfoTrees,_bindingsImatchIO,_bindingsIname,_bindingsInumberOfPatterns,_bindingsIpatternMatchWarnings,_bindingsIself,_bindingsIunboundNames,_bindingsIuniqueChunk,_bindingsIunrwars) =
                  (bindings_ _bindingsOallPatterns _bindingsOallTypeSchemes _bindingsOavailablePredicates _bindingsObetaRight _bindingsObetaUnique _bindingsObetasLeft _bindingsOclassEnvironment _bindingsOcollectErrors _bindingsOcollectWarnings _bindingsOcurrentChunk _bindingsOdictionaryEnvironment _bindingsOimportEnvironment _bindingsOmatchIO _bindingsOmonos _bindingsOnamesInScope _bindingsOorderedTypeSynonyms _bindingsOparentTree _bindingsOpatternMatchWarnings _bindingsOsubstitution _bindingsOtypeschemeMap _bindingsOuniqueChunk )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_Declaration_Instance :: T_Range  ->
                            T_ContextItems  ->
                            T_Name  ->
                            T_Types  ->
                            T_MaybeDeclarations  ->
                            T_Declaration 
sem_Declaration_Instance range_ context_ name_ types_ where_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _whereOunboundNames :: Names
              _lhsOdeclVarNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsObetaUnique :: Int
              _lhsObindingGroups :: BindingGroups
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOinfoTrees :: InfoTrees
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _whereOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _whereOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _whereOassumptions :: Assumptions
              _whereOavailablePredicates :: Predicates
              _whereObetaUnique :: Int
              _whereOclassEnvironment :: ClassEnvironment
              _whereOcollectErrors :: TypeErrors
              _whereOcollectWarnings :: Warnings
              _whereOconstraints :: ConstraintSet
              _whereOcurrentChunk :: Int
              _whereOdictionaryEnvironment :: DictionaryEnvironment
              _whereOimportEnvironment :: ImportEnvironment
              _whereOmatchIO :: (IO ())
              _whereOmonos :: Monos
              _whereOnamesInScope :: Names
              _whereOorderedTypeSynonyms :: OrderedTypeSynonyms
              _whereOparentTree :: InfoTree
              _whereOpatternMatchWarnings :: ([Warning])
              _whereOsubstitution :: FixpointSubstitution
              _whereOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _whereOuniqueChunk :: Int
              _rangeIself :: Range
              _contextIself :: ContextItems
              _nameIself :: Name
              _typesIself :: Types
              _whereIassumptions :: Assumptions
              _whereIbetaUnique :: Int
              _whereIcollectErrors :: TypeErrors
              _whereIcollectInstances :: ([(Name, Instance)])
              _whereIcollectWarnings :: Warnings
              _whereIconstraints :: ConstraintSet
              _whereIdeclVarNames :: Names
              _whereIdictionaryEnvironment :: DictionaryEnvironment
              _whereIinfoTrees :: InfoTrees
              _whereIlocalTypes :: (M.Map NameWithRange TpScheme)
              _whereImatchIO :: (IO ())
              _whereInamesInScope :: Names
              _whereIpatternMatchWarnings :: ([Warning])
              _whereIself :: MaybeDeclarations
              _whereIunboundNames :: Names
              _whereIuniqueChunk :: Int
              _whereOunboundNames =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOcollectInstances =
                  _whereIcollectInstances
              _lhsOrestrictedNames =
                  []
              _lhsOsimplePatNames =
                  []
              _lhsOunboundNames =
                  _whereIunboundNames
              _self =
                  Declaration_Instance _rangeIself _contextIself _nameIself _typesIself _whereIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _whereIbetaUnique
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOcollectErrors =
                  _whereIcollectErrors
              _lhsOcollectWarnings =
                  _whereIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _whereIdictionaryEnvironment
              _lhsOinfoTrees =
                  _whereIinfoTrees
              _lhsOmatchIO =
                  _whereImatchIO
              _lhsOpatternMatchWarnings =
                  _whereIpatternMatchWarnings
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOuniqueChunk =
                  _whereIuniqueChunk
              _whereOallPatterns =
                  _lhsIallPatterns
              _whereOallTypeSchemes =
                  _lhsIallTypeSchemes
              _whereOassumptions =
                  error "missing rule: Declaration.Instance.where.assumptions"
              _whereOavailablePredicates =
                  _lhsIavailablePredicates
              _whereObetaUnique =
                  _lhsIbetaUnique
              _whereOclassEnvironment =
                  _lhsIclassEnvironment
              _whereOcollectErrors =
                  _lhsIcollectErrors
              _whereOcollectWarnings =
                  _lhsIcollectWarnings
              _whereOconstraints =
                  error "missing rule: Declaration.Instance.where.constraints"
              _whereOcurrentChunk =
                  _lhsIcurrentChunk
              _whereOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _whereOimportEnvironment =
                  _lhsIimportEnvironment
              _whereOmatchIO =
                  _lhsImatchIO
              _whereOmonos =
                  _lhsImonos
              _whereOnamesInScope =
                  _lhsInamesInScope
              _whereOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _whereOparentTree =
                  _lhsIparentTree
              _whereOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _whereOsubstitution =
                  _lhsIsubstitution
              _whereOtypeschemeMap =
                  _lhsItypeschemeMap
              _whereOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _nameIself) =
                  (name_ )
              ( _typesIself) =
                  (types_ )
              ( _whereIassumptions,_whereIbetaUnique,_whereIcollectErrors,_whereIcollectInstances,_whereIcollectWarnings,_whereIconstraints,_whereIdeclVarNames,_whereIdictionaryEnvironment,_whereIinfoTrees,_whereIlocalTypes,_whereImatchIO,_whereInamesInScope,_whereIpatternMatchWarnings,_whereIself,_whereIunboundNames,_whereIuniqueChunk) =
                  (where_ _whereOallPatterns _whereOallTypeSchemes _whereOassumptions _whereOavailablePredicates _whereObetaUnique _whereOclassEnvironment _whereOcollectErrors _whereOcollectWarnings _whereOconstraints _whereOcurrentChunk _whereOdictionaryEnvironment _whereOimportEnvironment _whereOmatchIO _whereOmonos _whereOnamesInScope _whereOorderedTypeSynonyms _whereOparentTree _whereOpatternMatchWarnings _whereOsubstitution _whereOtypeschemeMap _whereOunboundNames _whereOuniqueChunk )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_Declaration_Newtype :: T_Range  ->
                           T_ContextItems  ->
                           T_SimpleType  ->
                           T_Constructor  ->
                           T_Names  ->
                           T_Declaration 
sem_Declaration_Newtype range_ context_ simpletype_ constructor_ derivings_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsObetaUnique :: Int
              _lhsObindingGroups :: BindingGroups
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOinfoTrees :: InfoTrees
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _constructorOnamesInScope :: Names
              _rangeIself :: Range
              _contextIself :: ContextItems
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _constructorIself :: Constructor
              _constructorIunboundNames :: Names
              _derivingsIself :: Names
              _infoTrees =
                  globalInfoError
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOsimplePatNames =
                  []
              _lhsOunboundNames =
                  _constructorIunboundNames
              _self =
                  Declaration_Newtype _rangeIself _contextIself _simpletypeIself _constructorIself _derivingsIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOinfoTrees =
                  _infoTrees
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              _constructorOnamesInScope =
                  _lhsInamesInScope
              ( _rangeIself) =
                  (range_ )
              ( _contextIself) =
                  (context_ )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _constructorIself,_constructorIunboundNames) =
                  (constructor_ _constructorOnamesInScope )
              ( _derivingsIself) =
                  (derivings_ )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_Declaration_PatternBinding :: T_Range  ->
                                  T_Pattern  ->
                                  T_RightHandSide  ->
                                  T_Declaration 
sem_Declaration_PatternBinding range_ pattern_ righthandside_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsObindingGroups :: BindingGroups
              _patternObetaUnique :: Int
              _righthandsideOmonos :: Monos
              _righthandsideOavailablePredicates :: Predicates
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              __tup5 :: ((Names,Names))
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _righthandsideOcurrentChunk :: Int
              _lhsOinfoTrees :: InfoTrees
              _lhsOdeclVarNames :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOmatchIO :: (IO ())
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _patternOimportEnvironment :: ImportEnvironment
              _patternOmonos :: Monos
              _patternOnamesInScope :: Names
              _patternOparentTree :: InfoTree
              _patternOpatternMatchWarnings :: ([Warning])
              _righthandsideOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _righthandsideOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _righthandsideObetaRight :: Tp
              _righthandsideObetaUnique :: Int
              _righthandsideOclassEnvironment :: ClassEnvironment
              _righthandsideOcollectErrors :: TypeErrors
              _righthandsideOcollectWarnings :: Warnings
              _righthandsideOdictionaryEnvironment :: DictionaryEnvironment
              _righthandsideOimportEnvironment :: ImportEnvironment
              _righthandsideOmatchIO :: (IO ())
              _righthandsideOnamesInScope :: Names
              _righthandsideOorderedTypeSynonyms :: OrderedTypeSynonyms
              _righthandsideOparentTree :: InfoTree
              _righthandsideOpatternMatchWarnings :: ([Warning])
              _righthandsideOsubstitution :: FixpointSubstitution
              _righthandsideOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _righthandsideOuniqueChunk :: Int
              _rangeIself :: Range
              _patternIbeta :: Tp
              _patternIbetaUnique :: Int
              _patternIconstraints :: ConstraintSet
              _patternIelements :: (  [PatternElement]        )
              _patternIenvironment :: PatternAssumptions
              _patternIinfoTree :: InfoTree
              _patternIpatVarNames :: Names
              _patternIpatternMatchWarnings :: ([Warning])
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _righthandsideIassumptions :: Assumptions
              _righthandsideIbetaUnique :: Int
              _righthandsideIcollectErrors :: TypeErrors
              _righthandsideIcollectInstances :: ([(Name, Instance)])
              _righthandsideIcollectWarnings :: Warnings
              _righthandsideIconstraints :: ConstraintSet
              _righthandsideIdictionaryEnvironment :: DictionaryEnvironment
              _righthandsideIfallthrough :: Bool
              _righthandsideIinfoTree :: InfoTree
              _righthandsideImatchIO :: (IO ())
              _righthandsideIpatternMatchWarnings :: ([Warning])
              _righthandsideIself :: RightHandSide
              _righthandsideIunboundNames :: Names
              _righthandsideIuniqueChunk :: Int
              _lhsObindingGroups =
                  _mybdggrp : _lhsIbindingGroups
              _patternObetaUnique =
                  _lhsIbetaUnique + 1
              _righthandsideOmonos =
                  findMono (head (M.keys _patternIenvironment)) _lhsIinheritedBDG ++ _lhsImonos
              _betaRight =
                  TVar _lhsIbetaUnique
              _newcon =
                  [ (_betaRight .==. _patternIbeta) _cinfo ]
              _mybdggrp =
                  ( _patternIenvironment
                  , _righthandsideIassumptions
                  , [ _newcon .>.
                      Node [ _patternIconstraints
                           , _righthandsideIconstraints
                           ]
                    ]
                  )
              _declPredicates =
                  case _patternIself of
                    Pattern_Variable _ name ->
                       let scheme     = M.findWithDefault err (NameWithRange name) _lhsIallTypeSchemes
                           predicates = matchTypeWithScheme _lhsIorderedTypeSynonyms
                                           (_lhsIsubstitution |-> _betaRight)
                                           (_lhsIsubstitution |-> scheme)
                           err = internalError "TypeInferenceOverloading.ag" "n/a" ("could not find type for pattern binding "++show name)
                       in Just (name, expandPredicates _lhsIorderedTypeSynonyms predicates)
                    _ -> Nothing
              _righthandsideOavailablePredicates =
                  case _declPredicates of
                     Just (n, ps) -> ps ++ _lhsIavailablePredicates
                     Nothing      -> _lhsIavailablePredicates
              _lhsOdictionaryEnvironment =
                  case _declPredicates of
                     Just (n, ps) -> addForDeclaration n ps _righthandsideIdictionaryEnvironment
                     Nothing      -> _righthandsideIdictionaryEnvironment
              __tup5 =
                  if isSimplePattern _patternIself
                    then ([], _patternIpatVarNames)
                    else (_patternIpatVarNames, [])
              (_lhsOrestrictedNames,_) =
                  __tup5
              (_,_lhsOsimplePatNames) =
                  __tup5
              _righthandsideOcurrentChunk =
                  findCurrentChunk (head (M.keys _patternIenvironment)) _lhsIinheritedBDG
              _cinfo =
                  orphanConstraint 1 "right hand side" _parentTree
                     []
              _localInfo =
                  LocalInfo { self = UHA_Decl _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo [_patternIinfoTree, _righthandsideIinfoTree]
              _lhsOinfoTrees =
                  [_parentTree]
              _lhsOdeclVarNames =
                  _patternIpatVarNames
              _lhsOpatternMatchWarnings =
                  patternMatchWarnings _lhsIimportEnvironment
                                       _lhsIsubstitution
                                       _patternIbeta
                                       (:[])
                                       [(_patternIelements, _righthandsideIfallthrough)]
                                       _rangeIself
                                       Nothing
                                       False
                                       []
                                       "pattern binding"
                                       "="
                  ++ _righthandsideIpatternMatchWarnings
              _lhsOcollectInstances =
                  _righthandsideIcollectInstances
              _lhsOunboundNames =
                  _patternIunboundNames ++ _righthandsideIunboundNames
              _self =
                  Declaration_PatternBinding _rangeIself _patternIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _righthandsideIbetaUnique
              _lhsOcollectErrors =
                  _righthandsideIcollectErrors
              _lhsOcollectWarnings =
                  _righthandsideIcollectWarnings
              _lhsOmatchIO =
                  _righthandsideImatchIO
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOuniqueChunk =
                  _righthandsideIuniqueChunk
              _patternOimportEnvironment =
                  _lhsIimportEnvironment
              _patternOmonos =
                  _lhsImonos
              _patternOnamesInScope =
                  _lhsInamesInScope
              _patternOparentTree =
                  _parentTree
              _patternOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _righthandsideOallPatterns =
                  _lhsIallPatterns
              _righthandsideOallTypeSchemes =
                  _lhsIallTypeSchemes
              _righthandsideObetaRight =
                  _betaRight
              _righthandsideObetaUnique =
                  _patternIbetaUnique
              _righthandsideOclassEnvironment =
                  _lhsIclassEnvironment
              _righthandsideOcollectErrors =
                  _lhsIcollectErrors
              _righthandsideOcollectWarnings =
                  _lhsIcollectWarnings
              _righthandsideOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _righthandsideOimportEnvironment =
                  _lhsIimportEnvironment
              _righthandsideOmatchIO =
                  _lhsImatchIO
              _righthandsideOnamesInScope =
                  _lhsInamesInScope
              _righthandsideOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _righthandsideOparentTree =
                  _parentTree
              _righthandsideOpatternMatchWarnings =
                  _patternIpatternMatchWarnings
              _righthandsideOsubstitution =
                  _lhsIsubstitution
              _righthandsideOtypeschemeMap =
                  _lhsItypeschemeMap
              _righthandsideOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _patternIbeta,_patternIbetaUnique,_patternIconstraints,_patternIelements,_patternIenvironment,_patternIinfoTree,_patternIpatVarNames,_patternIpatternMatchWarnings,_patternIself,_patternIunboundNames) =
                  (pattern_ _patternObetaUnique _patternOimportEnvironment _patternOmonos _patternOnamesInScope _patternOparentTree _patternOpatternMatchWarnings )
              ( _righthandsideIassumptions,_righthandsideIbetaUnique,_righthandsideIcollectErrors,_righthandsideIcollectInstances,_righthandsideIcollectWarnings,_righthandsideIconstraints,_righthandsideIdictionaryEnvironment,_righthandsideIfallthrough,_righthandsideIinfoTree,_righthandsideImatchIO,_righthandsideIpatternMatchWarnings,_righthandsideIself,_righthandsideIunboundNames,_righthandsideIuniqueChunk) =
                  (righthandside_ _righthandsideOallPatterns _righthandsideOallTypeSchemes _righthandsideOavailablePredicates _righthandsideObetaRight _righthandsideObetaUnique _righthandsideOclassEnvironment _righthandsideOcollectErrors _righthandsideOcollectWarnings _righthandsideOcurrentChunk _righthandsideOdictionaryEnvironment _righthandsideOimportEnvironment _righthandsideOmatchIO _righthandsideOmonos _righthandsideOnamesInScope _righthandsideOorderedTypeSynonyms _righthandsideOparentTree _righthandsideOpatternMatchWarnings _righthandsideOsubstitution _righthandsideOtypeschemeMap _righthandsideOuniqueChunk )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_Declaration_Type :: T_Range  ->
                        T_SimpleType  ->
                        T_Type  ->
                        T_Declaration 
sem_Declaration_Type range_ simpletype_ type_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOinfoTrees :: InfoTrees
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsObetaUnique :: Int
              _lhsObindingGroups :: BindingGroups
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _rangeIself :: Range
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _typeIself :: Type
              _lhsOinfoTrees =
                  []
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOsimplePatNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Declaration_Type _rangeIself _simpletypeIself _typeIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _typeIself) =
                  (type_ )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_Declaration_TypeSignature :: T_Range  ->
                                 T_Names  ->
                                 T_Type  ->
                                 T_Declaration 
sem_Declaration_TypeSignature range_ names_ type_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOtypeSignatures :: TypeEnvironment
              _lhsOinfoTrees :: InfoTrees
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsObetaUnique :: Int
              _lhsObindingGroups :: BindingGroups
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _rangeIself :: Range
              _namesIself :: Names
              _typeIself :: Type
              _lhsOtypeSignatures =
                  _lhsItypeSignatures `M.union` (M.fromList [ (name, _typeScheme) | name <- _namesIself ])
              _typeScheme =
                  makeTpSchemeFromType _typeIself
              _lhsOinfoTrees =
                  []
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOsimplePatNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Declaration_TypeSignature _rangeIself _namesIself _typeIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _namesIself) =
                  (names_ )
              ( _typeIself) =
                  (type_ )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
-- Declarations ------------------------------------------------
-- cata
sem_Declarations :: Declarations  ->
                    T_Declarations 
sem_Declarations list  =
    (Prelude.foldr sem_Declarations_Cons sem_Declarations_Nil (Prelude.map sem_Declaration list) )
-- semantic domain
type T_Declarations  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                       (M.Map NameWithRange TpScheme) ->
                       Predicates ->
                       Int ->
                       BindingGroups ->
                       ClassEnvironment ->
                       TypeErrors ->
                       Warnings ->
                       Int ->
                       DictionaryEnvironment ->
                       ImportEnvironment ->
                       InheritedBDG ->
                       (IO ()) ->
                       Monos ->
                       Names ->
                       OrderedTypeSynonyms ->
                       InfoTree ->
                       ([Warning]) ->
                       FixpointSubstitution ->
                       TypeEnvironment ->
                       (M.Map Int (Scheme Predicates)) ->
                       Int ->
                       ( Int,BindingGroups,TypeErrors,([(Name, Instance)]),Warnings,Names,DictionaryEnvironment,InfoTrees,(IO ()),([Warning]),Names,Declarations,Names,TypeEnvironment,Names,Int)
sem_Declarations_Cons :: T_Declaration  ->
                         T_Declarations  ->
                         T_Declarations 
sem_Declarations_Cons hd_ tl_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOinfoTrees :: InfoTrees
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declarations
              _lhsObetaUnique :: Int
              _lhsObindingGroups :: BindingGroups
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _hdOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _hdOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _hdOavailablePredicates :: Predicates
              _hdObetaUnique :: Int
              _hdObindingGroups :: BindingGroups
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectErrors :: TypeErrors
              _hdOcollectWarnings :: Warnings
              _hdOcurrentChunk :: Int
              _hdOdictionaryEnvironment :: DictionaryEnvironment
              _hdOimportEnvironment :: ImportEnvironment
              _hdOinheritedBDG :: InheritedBDG
              _hdOmatchIO :: (IO ())
              _hdOmonos :: Monos
              _hdOnamesInScope :: Names
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOparentTree :: InfoTree
              _hdOpatternMatchWarnings :: ([Warning])
              _hdOsubstitution :: FixpointSubstitution
              _hdOtypeSignatures :: TypeEnvironment
              _hdOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _hdOuniqueChunk :: Int
              _tlOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _tlOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _tlOavailablePredicates :: Predicates
              _tlObetaUnique :: Int
              _tlObindingGroups :: BindingGroups
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectErrors :: TypeErrors
              _tlOcollectWarnings :: Warnings
              _tlOcurrentChunk :: Int
              _tlOdictionaryEnvironment :: DictionaryEnvironment
              _tlOimportEnvironment :: ImportEnvironment
              _tlOinheritedBDG :: InheritedBDG
              _tlOmatchIO :: (IO ())
              _tlOmonos :: Monos
              _tlOnamesInScope :: Names
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOparentTree :: InfoTree
              _tlOpatternMatchWarnings :: ([Warning])
              _tlOsubstitution :: FixpointSubstitution
              _tlOtypeSignatures :: TypeEnvironment
              _tlOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _tlOuniqueChunk :: Int
              _hdIbetaUnique :: Int
              _hdIbindingGroups :: BindingGroups
              _hdIcollectErrors :: TypeErrors
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectWarnings :: Warnings
              _hdIdeclVarNames :: Names
              _hdIdictionaryEnvironment :: DictionaryEnvironment
              _hdIinfoTrees :: InfoTrees
              _hdImatchIO :: (IO ())
              _hdIpatternMatchWarnings :: ([Warning])
              _hdIrestrictedNames :: Names
              _hdIself :: Declaration
              _hdIsimplePatNames :: Names
              _hdItypeSignatures :: TypeEnvironment
              _hdIunboundNames :: Names
              _hdIuniqueChunk :: Int
              _tlIbetaUnique :: Int
              _tlIbindingGroups :: BindingGroups
              _tlIcollectErrors :: TypeErrors
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectWarnings :: Warnings
              _tlIdeclVarNames :: Names
              _tlIdictionaryEnvironment :: DictionaryEnvironment
              _tlIinfoTrees :: InfoTrees
              _tlImatchIO :: (IO ())
              _tlIpatternMatchWarnings :: ([Warning])
              _tlIrestrictedNames :: Names
              _tlIself :: Declarations
              _tlIsimplePatNames :: Names
              _tlItypeSignatures :: TypeEnvironment
              _tlIunboundNames :: Names
              _tlIuniqueChunk :: Int
              _lhsOinfoTrees =
                  _hdIinfoTrees ++ _tlIinfoTrees
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOdeclVarNames =
                  _hdIdeclVarNames ++ _tlIdeclVarNames
              _lhsOrestrictedNames =
                  _hdIrestrictedNames  ++  _tlIrestrictedNames
              _lhsOsimplePatNames =
                  _hdIsimplePatNames  ++  _tlIsimplePatNames
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _tlIbetaUnique
              _lhsObindingGroups =
                  _tlIbindingGroups
              _lhsOcollectErrors =
                  _tlIcollectErrors
              _lhsOcollectWarnings =
                  _tlIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _tlIdictionaryEnvironment
              _lhsOmatchIO =
                  _tlImatchIO
              _lhsOpatternMatchWarnings =
                  _tlIpatternMatchWarnings
              _lhsOtypeSignatures =
                  _tlItypeSignatures
              _lhsOuniqueChunk =
                  _tlIuniqueChunk
              _hdOallPatterns =
                  _lhsIallPatterns
              _hdOallTypeSchemes =
                  _lhsIallTypeSchemes
              _hdOavailablePredicates =
                  _lhsIavailablePredicates
              _hdObetaUnique =
                  _lhsIbetaUnique
              _hdObindingGroups =
                  _lhsIbindingGroups
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectErrors =
                  _lhsIcollectErrors
              _hdOcollectWarnings =
                  _lhsIcollectWarnings
              _hdOcurrentChunk =
                  _lhsIcurrentChunk
              _hdOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _hdOimportEnvironment =
                  _lhsIimportEnvironment
              _hdOinheritedBDG =
                  _lhsIinheritedBDG
              _hdOmatchIO =
                  _lhsImatchIO
              _hdOmonos =
                  _lhsImonos
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOparentTree =
                  _lhsIparentTree
              _hdOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _hdOsubstitution =
                  _lhsIsubstitution
              _hdOtypeSignatures =
                  _lhsItypeSignatures
              _hdOtypeschemeMap =
                  _lhsItypeschemeMap
              _hdOuniqueChunk =
                  _lhsIuniqueChunk
              _tlOallPatterns =
                  _lhsIallPatterns
              _tlOallTypeSchemes =
                  _lhsIallTypeSchemes
              _tlOavailablePredicates =
                  _lhsIavailablePredicates
              _tlObetaUnique =
                  _hdIbetaUnique
              _tlObindingGroups =
                  _hdIbindingGroups
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectErrors =
                  _hdIcollectErrors
              _tlOcollectWarnings =
                  _hdIcollectWarnings
              _tlOcurrentChunk =
                  _lhsIcurrentChunk
              _tlOdictionaryEnvironment =
                  _hdIdictionaryEnvironment
              _tlOimportEnvironment =
                  _lhsIimportEnvironment
              _tlOinheritedBDG =
                  _lhsIinheritedBDG
              _tlOmatchIO =
                  _hdImatchIO
              _tlOmonos =
                  _lhsImonos
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOparentTree =
                  _lhsIparentTree
              _tlOpatternMatchWarnings =
                  _hdIpatternMatchWarnings
              _tlOsubstitution =
                  _lhsIsubstitution
              _tlOtypeSignatures =
                  _hdItypeSignatures
              _tlOtypeschemeMap =
                  _lhsItypeschemeMap
              _tlOuniqueChunk =
                  _hdIuniqueChunk
              ( _hdIbetaUnique,_hdIbindingGroups,_hdIcollectErrors,_hdIcollectInstances,_hdIcollectWarnings,_hdIdeclVarNames,_hdIdictionaryEnvironment,_hdIinfoTrees,_hdImatchIO,_hdIpatternMatchWarnings,_hdIrestrictedNames,_hdIself,_hdIsimplePatNames,_hdItypeSignatures,_hdIunboundNames,_hdIuniqueChunk) =
                  (hd_ _hdOallPatterns _hdOallTypeSchemes _hdOavailablePredicates _hdObetaUnique _hdObindingGroups _hdOclassEnvironment _hdOcollectErrors _hdOcollectWarnings _hdOcurrentChunk _hdOdictionaryEnvironment _hdOimportEnvironment _hdOinheritedBDG _hdOmatchIO _hdOmonos _hdOnamesInScope _hdOorderedTypeSynonyms _hdOparentTree _hdOpatternMatchWarnings _hdOsubstitution _hdOtypeSignatures _hdOtypeschemeMap _hdOuniqueChunk )
              ( _tlIbetaUnique,_tlIbindingGroups,_tlIcollectErrors,_tlIcollectInstances,_tlIcollectWarnings,_tlIdeclVarNames,_tlIdictionaryEnvironment,_tlIinfoTrees,_tlImatchIO,_tlIpatternMatchWarnings,_tlIrestrictedNames,_tlIself,_tlIsimplePatNames,_tlItypeSignatures,_tlIunboundNames,_tlIuniqueChunk) =
                  (tl_ _tlOallPatterns _tlOallTypeSchemes _tlOavailablePredicates _tlObetaUnique _tlObindingGroups _tlOclassEnvironment _tlOcollectErrors _tlOcollectWarnings _tlOcurrentChunk _tlOdictionaryEnvironment _tlOimportEnvironment _tlOinheritedBDG _tlOmatchIO _tlOmonos _tlOnamesInScope _tlOorderedTypeSynonyms _tlOparentTree _tlOpatternMatchWarnings _tlOsubstitution _tlOtypeSignatures _tlOtypeschemeMap _tlOuniqueChunk )
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_Declarations_Nil :: T_Declarations 
sem_Declarations_Nil  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIbindingGroups
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsIinheritedBDG
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeSignatures
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOinfoTrees :: InfoTrees
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOsimplePatNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declarations
              _lhsObetaUnique :: Int
              _lhsObindingGroups :: BindingGroups
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _lhsOinfoTrees =
                  []
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOsimplePatNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
          in  ( _lhsObetaUnique,_lhsObindingGroups,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrestrictedNames,_lhsOself,_lhsOsimplePatNames,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOuniqueChunk)))
-- Export ------------------------------------------------------
-- cata
sem_Export :: Export  ->
              T_Export 
sem_Export (Export_Module _range _name )  =
    (sem_Export_Module (sem_Range _range ) (sem_Name _name ) )
sem_Export (Export_TypeOrClass _range _name _names )  =
    (sem_Export_TypeOrClass (sem_Range _range ) (sem_Name _name ) (sem_MaybeNames _names ) )
sem_Export (Export_TypeOrClassComplete _range _name )  =
    (sem_Export_TypeOrClassComplete (sem_Range _range ) (sem_Name _name ) )
sem_Export (Export_Variable _range _name )  =
    (sem_Export_Variable (sem_Range _range ) (sem_Name _name ) )
-- semantic domain
type T_Export  = ( Export)
sem_Export_Module :: T_Range  ->
                     T_Name  ->
                     T_Export 
sem_Export_Module range_ name_  =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Export_Module _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_Export_TypeOrClass :: T_Range  ->
                          T_Name  ->
                          T_MaybeNames  ->
                          T_Export 
sem_Export_TypeOrClass range_ name_ names_  =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _namesIself :: MaybeNames
         _self =
             Export_TypeOrClass _rangeIself _nameIself _namesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _namesIself) =
             (names_ )
     in  ( _lhsOself))
sem_Export_TypeOrClassComplete :: T_Range  ->
                                  T_Name  ->
                                  T_Export 
sem_Export_TypeOrClassComplete range_ name_  =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Export_TypeOrClassComplete _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_Export_Variable :: T_Range  ->
                       T_Name  ->
                       T_Export 
sem_Export_Variable range_ name_  =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Export_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
-- Exports -----------------------------------------------------
-- cata
sem_Exports :: Exports  ->
               T_Exports 
sem_Exports list  =
    (Prelude.foldr sem_Exports_Cons sem_Exports_Nil (Prelude.map sem_Export list) )
-- semantic domain
type T_Exports  = ( Exports)
sem_Exports_Cons :: T_Export  ->
                    T_Exports  ->
                    T_Exports 
sem_Exports_Cons hd_ tl_  =
    (let _lhsOself :: Exports
         _hdIself :: Export
         _tlIself :: Exports
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Exports_Nil :: T_Exports 
sem_Exports_Nil  =
    (let _lhsOself :: Exports
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Expression --------------------------------------------------
-- cata
sem_Expression :: Expression  ->
                  T_Expression 
sem_Expression (Expression_Case _range _expression _alternatives )  =
    (sem_Expression_Case (sem_Range _range ) (sem_Expression _expression ) (sem_Alternatives _alternatives ) )
sem_Expression (Expression_Comprehension _range _expression _qualifiers )  =
    (sem_Expression_Comprehension (sem_Range _range ) (sem_Expression _expression ) (sem_Qualifiers _qualifiers ) )
sem_Expression (Expression_Constructor _range _name )  =
    (sem_Expression_Constructor (sem_Range _range ) (sem_Name _name ) )
sem_Expression (Expression_Do _range _statements )  =
    (sem_Expression_Do (sem_Range _range ) (sem_Statements _statements ) )
sem_Expression (Expression_Enum _range _from _then _to )  =
    (sem_Expression_Enum (sem_Range _range ) (sem_Expression _from ) (sem_MaybeExpression _then ) (sem_MaybeExpression _to ) )
sem_Expression (Expression_If _range _guardExpression _thenExpression _elseExpression )  =
    (sem_Expression_If (sem_Range _range ) (sem_Expression _guardExpression ) (sem_Expression _thenExpression ) (sem_Expression _elseExpression ) )
sem_Expression (Expression_InfixApplication _range _leftExpression _operator _rightExpression )  =
    (sem_Expression_InfixApplication (sem_Range _range ) (sem_MaybeExpression _leftExpression ) (sem_Expression _operator ) (sem_MaybeExpression _rightExpression ) )
sem_Expression (Expression_Lambda _range _patterns _expression )  =
    (sem_Expression_Lambda (sem_Range _range ) (sem_Patterns _patterns ) (sem_Expression _expression ) )
sem_Expression (Expression_Let _range _declarations _expression )  =
    (sem_Expression_Let (sem_Range _range ) (sem_Declarations _declarations ) (sem_Expression _expression ) )
sem_Expression (Expression_List _range _expressions )  =
    (sem_Expression_List (sem_Range _range ) (sem_Expressions _expressions ) )
sem_Expression (Expression_Literal _range _literal )  =
    (sem_Expression_Literal (sem_Range _range ) (sem_Literal _literal ) )
sem_Expression (Expression_Negate _range _expression )  =
    (sem_Expression_Negate (sem_Range _range ) (sem_Expression _expression ) )
sem_Expression (Expression_NegateFloat _range _expression )  =
    (sem_Expression_NegateFloat (sem_Range _range ) (sem_Expression _expression ) )
sem_Expression (Expression_NormalApplication _range _function _arguments )  =
    (sem_Expression_NormalApplication (sem_Range _range ) (sem_Expression _function ) (sem_Expressions _arguments ) )
sem_Expression (Expression_Parenthesized _range _expression )  =
    (sem_Expression_Parenthesized (sem_Range _range ) (sem_Expression _expression ) )
sem_Expression (Expression_RecordConstruction _range _name _recordExpressionBindings )  =
    (sem_Expression_RecordConstruction (sem_Range _range ) (sem_Name _name ) (sem_RecordExpressionBindings _recordExpressionBindings ) )
sem_Expression (Expression_RecordUpdate _range _expression _recordExpressionBindings )  =
    (sem_Expression_RecordUpdate (sem_Range _range ) (sem_Expression _expression ) (sem_RecordExpressionBindings _recordExpressionBindings ) )
sem_Expression (Expression_Tuple _range _expressions )  =
    (sem_Expression_Tuple (sem_Range _range ) (sem_Expressions _expressions ) )
sem_Expression (Expression_Typed _range _expression _type )  =
    (sem_Expression_Typed (sem_Range _range ) (sem_Expression _expression ) (sem_Type _type ) )
sem_Expression (Expression_Variable _range _name )  =
    (sem_Expression_Variable (sem_Range _range ) (sem_Name _name ) )
-- semantic domain
type T_Expression  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                     (M.Map NameWithRange TpScheme) ->
                     Predicates ->
                     Int ->
                     ClassEnvironment ->
                     TypeErrors ->
                     Warnings ->
                     Int ->
                     DictionaryEnvironment ->
                     ImportEnvironment ->
                     (IO ()) ->
                     Monos ->
                     Names ->
                     OrderedTypeSynonyms ->
                     InfoTree ->
                     ([Warning]) ->
                     FixpointSubstitution ->
                     ([(Expression     , [String])]) ->
                     (M.Map Int (Scheme Predicates)) ->
                     Int ->
                     Int ->
                     ( Assumptions,Tp,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,DictionaryEnvironment,InfoTree,(IO ()),([Maybe MetaVariableTable]),([Warning]),Expression,Names,Int,Int)
sem_Expression_Case :: T_Range  ->
                       T_Expression  ->
                       T_Alternatives  ->
                       T_Expression 
sem_Expression_Case range_ expression_ alternatives_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _expressionObetaUnique :: Int
              _alternativesObetaLeft :: Tp
              _alternativesObetaRight :: Tp
              _lhsOinfoTree :: InfoTree
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOassumptions :: Assumptions
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _alternativesOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _alternativesOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _alternativesOavailablePredicates :: Predicates
              _alternativesObetaUnique :: Int
              _alternativesOclassEnvironment :: ClassEnvironment
              _alternativesOcollectErrors :: TypeErrors
              _alternativesOcollectWarnings :: Warnings
              _alternativesOcurrentChunk :: Int
              _alternativesOdictionaryEnvironment :: DictionaryEnvironment
              _alternativesOimportEnvironment :: ImportEnvironment
              _alternativesOmatchIO :: (IO ())
              _alternativesOmonos :: Monos
              _alternativesOnamesInScope :: Names
              _alternativesOorderedTypeSynonyms :: OrderedTypeSynonyms
              _alternativesOparentTree :: InfoTree
              _alternativesOpatternMatchWarnings :: ([Warning])
              _alternativesOsubstitution :: FixpointSubstitution
              _alternativesOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _alternativesOuniqueChunk :: Int
              _rangeIself :: Range
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _alternativesIassumptions :: Assumptions
              _alternativesIbetaUnique :: Int
              _alternativesIcollectErrors :: TypeErrors
              _alternativesIcollectInstances :: ([(Name, Instance)])
              _alternativesIcollectWarnings :: Warnings
              _alternativesIconstraintslist :: ConstraintSets
              _alternativesIdictionaryEnvironment :: DictionaryEnvironment
              _alternativesIelementss :: ([([PatternElement], Bool)])
              _alternativesIinfoTrees :: InfoTrees
              _alternativesImatchIO :: (IO ())
              _alternativesIpatternMatchWarnings :: ([Warning])
              _alternativesIself :: Alternatives
              _alternativesIunboundNames :: Names
              _alternativesIuniqueChunk :: Int
              _alternativesIunrwars :: ([Warning])
              _expressionObetaUnique =
                  _lhsIbetaUnique + 2
              _alternativesObetaLeft =
                  _beta'
              _alternativesObetaRight =
                  _beta
              _assumptions =
                  _expressionIassumptions `combine` _alternativesIassumptions
              _constraints =
                  Node [ _newcon .<. _expressionIconstraints
                       , Node _alternativesIconstraintslist
                       ]
              _beta =
                  TVar _lhsIbetaUnique
              _beta' =
                  TVar (_lhsIbetaUnique + 1)
              _newcon =
                  [ (_expressionIbeta .==. _beta') _cinfo ]
              _cinfo =
                  childConstraint 0 "scrutinee of case expression" _parentTree
                     [ Unifier (head (ftv _beta')) ("case patterns", _localInfo, "scrutinee") ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo (_expressionIinfoTree : _alternativesIinfoTrees)
              _lhsOinfoTree =
                  _parentTree
              _lhsOmatches =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in matchOnlyVariable infoTuple _lhsItryPatterns
              _expressionOtryPatterns =
                  []
              _lhsOpatternMatchWarnings =
                  patternMatchWarnings _lhsIimportEnvironment
                                       _lhsIsubstitution
                                       _expressionIbeta
                                       (:[])
                                       _alternativesIelementss
                                       _rangeIself
                                       Nothing
                                       False
                                       _alternativesIunrwars
                                       "case expression"
                                       "->"
                  ++ _alternativesIpatternMatchWarnings
              _lhsOcollectInstances =
                  _expressionIcollectInstances  ++  _alternativesIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames ++ _alternativesIunboundNames
              _self =
                  Expression_Case _rangeIself _expressionIself _alternativesIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _assumptions
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _alternativesIbetaUnique
              _lhsOcollectErrors =
                  _alternativesIcollectErrors
              _lhsOcollectWarnings =
                  _alternativesIcollectWarnings
              _lhsOconstraints =
                  _constraints
              _lhsOdictionaryEnvironment =
                  _alternativesIdictionaryEnvironment
              _lhsOmatchIO =
                  _alternativesImatchIO
              _lhsOuniqueChunk =
                  _alternativesIuniqueChunk
              _lhsOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _parentTree
              _expressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _alternativesOallPatterns =
                  _lhsIallPatterns
              _alternativesOallTypeSchemes =
                  _lhsIallTypeSchemes
              _alternativesOavailablePredicates =
                  _lhsIavailablePredicates
              _alternativesObetaUnique =
                  _expressionIbetaUnique
              _alternativesOclassEnvironment =
                  _lhsIclassEnvironment
              _alternativesOcollectErrors =
                  _expressionIcollectErrors
              _alternativesOcollectWarnings =
                  _expressionIcollectWarnings
              _alternativesOcurrentChunk =
                  _lhsIcurrentChunk
              _alternativesOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _alternativesOimportEnvironment =
                  _lhsIimportEnvironment
              _alternativesOmatchIO =
                  _expressionImatchIO
              _alternativesOmonos =
                  _lhsImonos
              _alternativesOnamesInScope =
                  _lhsInamesInScope
              _alternativesOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _alternativesOparentTree =
                  _parentTree
              _alternativesOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _alternativesOsubstitution =
                  _lhsIsubstitution
              _alternativesOtypeschemeMap =
                  _lhsItypeschemeMap
              _alternativesOuniqueChunk =
                  _expressionIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
              ( _alternativesIassumptions,_alternativesIbetaUnique,_alternativesIcollectErrors,_alternativesIcollectInstances,_alternativesIcollectWarnings,_alternativesIconstraintslist,_alternativesIdictionaryEnvironment,_alternativesIelementss,_alternativesIinfoTrees,_alternativesImatchIO,_alternativesIpatternMatchWarnings,_alternativesIself,_alternativesIunboundNames,_alternativesIuniqueChunk,_alternativesIunrwars) =
                  (alternatives_ _alternativesOallPatterns _alternativesOallTypeSchemes _alternativesOavailablePredicates _alternativesObetaLeft _alternativesObetaRight _alternativesObetaUnique _alternativesOclassEnvironment _alternativesOcollectErrors _alternativesOcollectWarnings _alternativesOcurrentChunk _alternativesOdictionaryEnvironment _alternativesOimportEnvironment _alternativesOmatchIO _alternativesOmonos _alternativesOnamesInScope _alternativesOorderedTypeSynonyms _alternativesOparentTree _alternativesOpatternMatchWarnings _alternativesOsubstitution _alternativesOtypeschemeMap _alternativesOuniqueChunk )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Comprehension :: T_Range  ->
                                T_Expression  ->
                                T_Qualifiers  ->
                                T_Expression 
sem_Expression_Comprehension range_ expression_ qualifiers_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _expressionObetaUnique :: Int
              _expressionOmonos :: Monos
              _qualifiersOassumptions :: Assumptions
              _qualifiersOconstraints :: ConstraintSet
              _qualifiersOmonos :: Monos
              _lhsOinfoTree :: InfoTree
              _lhsOunboundNames :: Names
              _expressionOnamesInScope :: Names
              _qualifiersOnamesInScope :: Names
              _qualifiersOunboundNames :: Names
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Expression
              _lhsOassumptions :: Assumptions
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _qualifiersOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _qualifiersOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _qualifiersOavailablePredicates :: Predicates
              _qualifiersObetaUnique :: Int
              _qualifiersOclassEnvironment :: ClassEnvironment
              _qualifiersOcollectErrors :: TypeErrors
              _qualifiersOcollectWarnings :: Warnings
              _qualifiersOcurrentChunk :: Int
              _qualifiersOdictionaryEnvironment :: DictionaryEnvironment
              _qualifiersOimportEnvironment :: ImportEnvironment
              _qualifiersOmatchIO :: (IO ())
              _qualifiersOorderedTypeSynonyms :: OrderedTypeSynonyms
              _qualifiersOparentTree :: InfoTree
              _qualifiersOpatternMatchWarnings :: ([Warning])
              _qualifiersOsubstitution :: FixpointSubstitution
              _qualifiersOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _qualifiersOuniqueChunk :: Int
              _qualifiersOuniqueSecondRound :: Int
              _rangeIself :: Range
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _qualifiersIassumptions :: Assumptions
              _qualifiersIbetaUnique :: Int
              _qualifiersIcollectErrors :: TypeErrors
              _qualifiersIcollectInstances :: ([(Name, Instance)])
              _qualifiersIcollectWarnings :: Warnings
              _qualifiersIconstraints :: ConstraintSet
              _qualifiersIdictionaryEnvironment :: DictionaryEnvironment
              _qualifiersIinfoTrees :: InfoTrees
              _qualifiersImatchIO :: (IO ())
              _qualifiersImonos :: Monos
              _qualifiersInamesInScope :: Names
              _qualifiersIpatternMatchWarnings :: ([Warning])
              _qualifiersIself :: Qualifiers
              _qualifiersIunboundNames :: Names
              _qualifiersIuniqueChunk :: Int
              _qualifiersIuniqueSecondRound :: Int
              _expressionObetaUnique =
                  _lhsIbetaUnique + 1
              _expressionOmonos =
                  _qualifiersImonos
              _qualifiersOassumptions =
                  _expressionIassumptions
              _qualifiersOconstraints =
                  _expressionIconstraints
              _qualifiersOmonos =
                  _lhsImonos
              _assumptions =
                  _qualifiersIassumptions
              _constraints =
                  _newcon .>. Node [ _qualifiersIconstraints ]
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  [ (listType _expressionIbeta .==. _beta) _cinfo ]
              _cinfo =
                  resultConstraint "list comprehension" _parentTree
                     [ FolkloreConstraint ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo _qualifiersIinfoTrees
              _lhsOinfoTree =
                  _parentTree
              _lhsOunboundNames =
                  _qualifiersIunboundNames
              _expressionOnamesInScope =
                  _qualifiersInamesInScope
              _qualifiersOnamesInScope =
                  _lhsInamesInScope
              _qualifiersOunboundNames =
                  _expressionIunboundNames
              _lhsOmatches =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in matchOnlyVariable infoTuple _lhsItryPatterns
              _expressionOtryPatterns =
                  []
              _lhsOcollectInstances =
                  _expressionIcollectInstances  ++  _qualifiersIcollectInstances
              _self =
                  Expression_Comprehension _rangeIself _expressionIself _qualifiersIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _assumptions
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _qualifiersIbetaUnique
              _lhsOcollectErrors =
                  _qualifiersIcollectErrors
              _lhsOcollectWarnings =
                  _qualifiersIcollectWarnings
              _lhsOconstraints =
                  _constraints
              _lhsOdictionaryEnvironment =
                  _qualifiersIdictionaryEnvironment
              _lhsOmatchIO =
                  _qualifiersImatchIO
              _lhsOpatternMatchWarnings =
                  _qualifiersIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _qualifiersIuniqueChunk
              _lhsOuniqueSecondRound =
                  _qualifiersIuniqueSecondRound
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _parentTree
              _expressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _qualifiersOallPatterns =
                  _lhsIallPatterns
              _qualifiersOallTypeSchemes =
                  _lhsIallTypeSchemes
              _qualifiersOavailablePredicates =
                  _lhsIavailablePredicates
              _qualifiersObetaUnique =
                  _expressionIbetaUnique
              _qualifiersOclassEnvironment =
                  _lhsIclassEnvironment
              _qualifiersOcollectErrors =
                  _expressionIcollectErrors
              _qualifiersOcollectWarnings =
                  _expressionIcollectWarnings
              _qualifiersOcurrentChunk =
                  _lhsIcurrentChunk
              _qualifiersOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _qualifiersOimportEnvironment =
                  _lhsIimportEnvironment
              _qualifiersOmatchIO =
                  _expressionImatchIO
              _qualifiersOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _qualifiersOparentTree =
                  _parentTree
              _qualifiersOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _qualifiersOsubstitution =
                  _lhsIsubstitution
              _qualifiersOtypeschemeMap =
                  _lhsItypeschemeMap
              _qualifiersOuniqueChunk =
                  _expressionIuniqueChunk
              _qualifiersOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
              ( _qualifiersIassumptions,_qualifiersIbetaUnique,_qualifiersIcollectErrors,_qualifiersIcollectInstances,_qualifiersIcollectWarnings,_qualifiersIconstraints,_qualifiersIdictionaryEnvironment,_qualifiersIinfoTrees,_qualifiersImatchIO,_qualifiersImonos,_qualifiersInamesInScope,_qualifiersIpatternMatchWarnings,_qualifiersIself,_qualifiersIunboundNames,_qualifiersIuniqueChunk,_qualifiersIuniqueSecondRound) =
                  (qualifiers_ _qualifiersOallPatterns _qualifiersOallTypeSchemes _qualifiersOassumptions _qualifiersOavailablePredicates _qualifiersObetaUnique _qualifiersOclassEnvironment _qualifiersOcollectErrors _qualifiersOcollectWarnings _qualifiersOconstraints _qualifiersOcurrentChunk _qualifiersOdictionaryEnvironment _qualifiersOimportEnvironment _qualifiersOmatchIO _qualifiersOmonos _qualifiersOnamesInScope _qualifiersOorderedTypeSynonyms _qualifiersOparentTree _qualifiersOpatternMatchWarnings _qualifiersOsubstitution _qualifiersOtypeschemeMap _qualifiersOunboundNames _qualifiersOuniqueChunk _qualifiersOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Constructor :: T_Range  ->
                              T_Name  ->
                              T_Expression 
sem_Expression_Constructor range_ name_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOuniqueSecondRound :: Int
              _lhsOmatchIO :: (IO ())
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsObeta :: Tp
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _rangeIself :: Range
              _nameIself :: Name
              _lhsObetaUnique =
                  _lhsIbetaUnique + 1
              _assumptions =
                  noAssumptions
              _constraints =
                  listTree _newcon
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  case M.lookup _nameIself (valueConstructors _lhsIimportEnvironment) of
                     Nothing  -> []
                     Just ctp -> [ (_beta .::. ctp) _cinfo ]
              _cinfo =
                  resultConstraint "constructor" _parentTree
                     [ FolkloreConstraint, HasTrustFactor 10.0, IsImported _nameIself ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo []
              _lhsOinfoTree =
                  _parentTree
              __tup6 =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in match0 infoTuple _lhsIuniqueSecondRound
                            (match_Expression_Constructor _nameIself)
                            _lhsItryPatterns _lhsIallPatterns
                            []
              (__tup7,_,_,_,_,_) =
                  __tup6
              (_,_lhsOmatches,_,_,_,_) =
                  __tup6
              (_,_,_lhsOconstraints,_,_,_) =
                  __tup6
              (_,_,_,_lhsOassumptions,_,_) =
                  __tup6
              (_,_,_,_,_lhsOuniqueSecondRound,_) =
                  __tup6
              (_,_,_,_,_,_ioMatch) =
                  __tup6
              _lhsOmatchIO =
                  _lhsImatchIO             >> _ioMatch
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Expression_Constructor _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Do :: T_Range  ->
                     T_Statements  ->
                     T_Expression 
sem_Expression_Do range_ statements_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOconstraints :: ConstraintSet
              _statementsObetaUnique :: Int
              _statementsOgeneratorBeta :: (Maybe Tp)
              _statementsOassumptions :: Assumptions
              _lhsOinfoTree :: InfoTree
              _statementsOunboundNames :: Names
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOassumptions :: Assumptions
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _statementsOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _statementsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _statementsOavailablePredicates :: Predicates
              _statementsOclassEnvironment :: ClassEnvironment
              _statementsOcollectErrors :: TypeErrors
              _statementsOcollectWarnings :: Warnings
              _statementsOconstraints :: ConstraintSet
              _statementsOcurrentChunk :: Int
              _statementsOdictionaryEnvironment :: DictionaryEnvironment
              _statementsOimportEnvironment :: ImportEnvironment
              _statementsOmatchIO :: (IO ())
              _statementsOmonos :: Monos
              _statementsOnamesInScope :: Names
              _statementsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _statementsOparentTree :: InfoTree
              _statementsOpatternMatchWarnings :: ([Warning])
              _statementsOsubstitution :: FixpointSubstitution
              _statementsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _statementsOuniqueChunk :: Int
              _statementsOuniqueSecondRound :: Int
              _rangeIself :: Range
              _statementsIassumptions :: Assumptions
              _statementsIbetaUnique :: Int
              _statementsIcollectErrors :: TypeErrors
              _statementsIcollectInstances :: ([(Name, Instance)])
              _statementsIcollectWarnings :: Warnings
              _statementsIconstraints :: ConstraintSet
              _statementsIdictionaryEnvironment :: DictionaryEnvironment
              _statementsIgeneratorBeta :: (Maybe Tp)
              _statementsIinfoTrees :: InfoTrees
              _statementsImatchIO :: (IO ())
              _statementsInamesInScope :: Names
              _statementsIpatternMatchWarnings :: ([Warning])
              _statementsIself :: Statements
              _statementsIunboundNames :: Names
              _statementsIuniqueChunk :: Int
              _statementsIuniqueSecondRound :: Int
              _lhsOconstraints =
                  Node [ _newcon .<. _statementsIconstraints ]
              _statementsObetaUnique =
                  _lhsIbetaUnique + 1
              _statementsOgeneratorBeta =
                  Nothing
              _statementsOassumptions =
                  noAssumptions
              _assumptions =
                  _statementsIassumptions
              _constraints =
                  emptyTree
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  case _statementsIgeneratorBeta of
                     Nothing -> []
                     Just b  -> [ (ioType b .==. _beta) _cinfo ]
              _cinfo =
                  resultConstraint "do-expression" _parentTree
                     [ FolkloreConstraint ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo _statementsIinfoTrees
              _lhsOinfoTree =
                  _parentTree
              _statementsOunboundNames =
                  []
              _lhsOmatches =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in matchOnlyVariable infoTuple _lhsItryPatterns
              _lhsOcollectInstances =
                  _statementsIcollectInstances
              _lhsOunboundNames =
                  _statementsIunboundNames
              _self =
                  Expression_Do _rangeIself _statementsIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _assumptions
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _statementsIbetaUnique
              _lhsOcollectErrors =
                  _statementsIcollectErrors
              _lhsOcollectWarnings =
                  _statementsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _statementsIdictionaryEnvironment
              _lhsOmatchIO =
                  _statementsImatchIO
              _lhsOpatternMatchWarnings =
                  _statementsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _statementsIuniqueChunk
              _lhsOuniqueSecondRound =
                  _statementsIuniqueSecondRound
              _statementsOallPatterns =
                  _lhsIallPatterns
              _statementsOallTypeSchemes =
                  _lhsIallTypeSchemes
              _statementsOavailablePredicates =
                  _lhsIavailablePredicates
              _statementsOclassEnvironment =
                  _lhsIclassEnvironment
              _statementsOcollectErrors =
                  _lhsIcollectErrors
              _statementsOcollectWarnings =
                  _lhsIcollectWarnings
              _statementsOconstraints =
                  _constraints
              _statementsOcurrentChunk =
                  _lhsIcurrentChunk
              _statementsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _statementsOimportEnvironment =
                  _lhsIimportEnvironment
              _statementsOmatchIO =
                  _lhsImatchIO
              _statementsOmonos =
                  _lhsImonos
              _statementsOnamesInScope =
                  _lhsInamesInScope
              _statementsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _statementsOparentTree =
                  _parentTree
              _statementsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _statementsOsubstitution =
                  _lhsIsubstitution
              _statementsOtypeschemeMap =
                  _lhsItypeschemeMap
              _statementsOuniqueChunk =
                  _lhsIuniqueChunk
              _statementsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _statementsIassumptions,_statementsIbetaUnique,_statementsIcollectErrors,_statementsIcollectInstances,_statementsIcollectWarnings,_statementsIconstraints,_statementsIdictionaryEnvironment,_statementsIgeneratorBeta,_statementsIinfoTrees,_statementsImatchIO,_statementsInamesInScope,_statementsIpatternMatchWarnings,_statementsIself,_statementsIunboundNames,_statementsIuniqueChunk,_statementsIuniqueSecondRound) =
                  (statements_ _statementsOallPatterns _statementsOallTypeSchemes _statementsOassumptions _statementsOavailablePredicates _statementsObetaUnique _statementsOclassEnvironment _statementsOcollectErrors _statementsOcollectWarnings _statementsOconstraints _statementsOcurrentChunk _statementsOdictionaryEnvironment _statementsOgeneratorBeta _statementsOimportEnvironment _statementsOmatchIO _statementsOmonos _statementsOnamesInScope _statementsOorderedTypeSynonyms _statementsOparentTree _statementsOpatternMatchWarnings _statementsOsubstitution _statementsOtypeschemeMap _statementsOunboundNames _statementsOuniqueChunk _statementsOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Enum :: T_Range  ->
                       T_Expression  ->
                       T_MaybeExpression  ->
                       T_MaybeExpression  ->
                       T_Expression 
sem_Expression_Enum range_ from_ then_ to_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _fromObetaUnique :: Int
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOinfoTree :: InfoTree
              __tup9 :: (([(Expression     , [String])],[(MaybeExpression, [String])],[(MaybeExpression, [String])]))
              _fromOtryPatterns :: ([(Expression     , [String])])
              _thenOtryPatterns :: ([(MaybeExpression, [String])])
              _toOtryPatterns :: ([(MaybeExpression, [String])])
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOuniqueSecondRound :: Int
              _lhsOmatchIO :: (IO ())
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _fromOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _fromOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _fromOavailablePredicates :: Predicates
              _fromOclassEnvironment :: ClassEnvironment
              _fromOcollectErrors :: TypeErrors
              _fromOcollectWarnings :: Warnings
              _fromOcurrentChunk :: Int
              _fromOdictionaryEnvironment :: DictionaryEnvironment
              _fromOimportEnvironment :: ImportEnvironment
              _fromOmatchIO :: (IO ())
              _fromOmonos :: Monos
              _fromOnamesInScope :: Names
              _fromOorderedTypeSynonyms :: OrderedTypeSynonyms
              _fromOparentTree :: InfoTree
              _fromOpatternMatchWarnings :: ([Warning])
              _fromOsubstitution :: FixpointSubstitution
              _fromOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _fromOuniqueChunk :: Int
              _fromOuniqueSecondRound :: Int
              _thenOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _thenOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _thenOavailablePredicates :: Predicates
              _thenObetaUnique :: Int
              _thenOclassEnvironment :: ClassEnvironment
              _thenOcollectErrors :: TypeErrors
              _thenOcollectWarnings :: Warnings
              _thenOcurrentChunk :: Int
              _thenOdictionaryEnvironment :: DictionaryEnvironment
              _thenOimportEnvironment :: ImportEnvironment
              _thenOmatchIO :: (IO ())
              _thenOmonos :: Monos
              _thenOnamesInScope :: Names
              _thenOorderedTypeSynonyms :: OrderedTypeSynonyms
              _thenOparentTree :: InfoTree
              _thenOpatternMatchWarnings :: ([Warning])
              _thenOsubstitution :: FixpointSubstitution
              _thenOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _thenOuniqueChunk :: Int
              _thenOuniqueSecondRound :: Int
              _toOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _toOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _toOavailablePredicates :: Predicates
              _toObetaUnique :: Int
              _toOclassEnvironment :: ClassEnvironment
              _toOcollectErrors :: TypeErrors
              _toOcollectWarnings :: Warnings
              _toOcurrentChunk :: Int
              _toOdictionaryEnvironment :: DictionaryEnvironment
              _toOimportEnvironment :: ImportEnvironment
              _toOmatchIO :: (IO ())
              _toOmonos :: Monos
              _toOnamesInScope :: Names
              _toOorderedTypeSynonyms :: OrderedTypeSynonyms
              _toOparentTree :: InfoTree
              _toOpatternMatchWarnings :: ([Warning])
              _toOsubstitution :: FixpointSubstitution
              _toOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _toOuniqueChunk :: Int
              _toOuniqueSecondRound :: Int
              _rangeIself :: Range
              _fromIassumptions :: Assumptions
              _fromIbeta :: Tp
              _fromIbetaUnique :: Int
              _fromIcollectErrors :: TypeErrors
              _fromIcollectInstances :: ([(Name, Instance)])
              _fromIcollectWarnings :: Warnings
              _fromIconstraints :: ConstraintSet
              _fromIdictionaryEnvironment :: DictionaryEnvironment
              _fromIinfoTree :: InfoTree
              _fromImatchIO :: (IO ())
              _fromImatches :: ([Maybe MetaVariableTable])
              _fromIpatternMatchWarnings :: ([Warning])
              _fromIself :: Expression
              _fromIunboundNames :: Names
              _fromIuniqueChunk :: Int
              _fromIuniqueSecondRound :: Int
              _thenIassumptions :: Assumptions
              _thenIbeta :: Tp
              _thenIbetaUnique :: Int
              _thenIcollectErrors :: TypeErrors
              _thenIcollectInstances :: ([(Name, Instance)])
              _thenIcollectWarnings :: Warnings
              _thenIconstraints :: ConstraintSet
              _thenIdictionaryEnvironment :: DictionaryEnvironment
              _thenIinfoTrees :: InfoTrees
              _thenImatchIO :: (IO ())
              _thenImatches :: ([Maybe MetaVariableTable])
              _thenIpatternMatchWarnings :: ([Warning])
              _thenIsection :: Bool
              _thenIself :: MaybeExpression
              _thenIunboundNames :: Names
              _thenIuniqueChunk :: Int
              _thenIuniqueSecondRound :: Int
              _toIassumptions :: Assumptions
              _toIbeta :: Tp
              _toIbetaUnique :: Int
              _toIcollectErrors :: TypeErrors
              _toIcollectInstances :: ([(Name, Instance)])
              _toIcollectWarnings :: Warnings
              _toIconstraints :: ConstraintSet
              _toIdictionaryEnvironment :: DictionaryEnvironment
              _toIinfoTrees :: InfoTrees
              _toImatchIO :: (IO ())
              _toImatches :: ([Maybe MetaVariableTable])
              _toIpatternMatchWarnings :: ([Warning])
              _toIsection :: Bool
              _toIself :: MaybeExpression
              _toIunboundNames :: Names
              _toIuniqueChunk :: Int
              _toIuniqueSecondRound :: Int
              _fromObetaUnique =
                  _lhsIbetaUnique + (if _overloaded then 2 else 1)
              _assumptions =
                  _fromIassumptions `combine` _thenIassumptions `combine` _toIassumptions
              _constraints =
                  (_conList ++ _conPredicate) .>.
                  Node [ _conFrom .<. _fromIconstraints
                       , _conThen .<. _thenIconstraints
                       , _conTo   .<. _toIconstraints
                       ]
              _beta =
                  TVar _lhsIbetaUnique
              _overloaded =
                  case M.lookup enumFromName (typeEnvironment _lhsIimportEnvironment) of
                     Just scheme -> isOverloaded scheme
                     Nothing     -> False
              _elementType =
                  if _overloaded then TVar (_lhsIbetaUnique + 1) else intType
              _conPredicate =
                  if _overloaded then [predicate (Predicate "Enum" _elementType) _cinfoPred] else []
              _conList =
                  [ (listType _elementType .==. _beta) _cinfoResult ]
              _conFrom =
                  [ (_fromIbeta .==. _elementType) _cinfoFrom ]
              _conThen =
                  [ (_thenIbeta .==. _elementType) _cinfoThen ]
              _conTo =
                  [ (_toIbeta   .==. _elementType) _cinfoTo   ]
              _lhsOdictionaryEnvironment =
                  _newDEnv
              _localName =
                  flip setNameRange _rangeIself $
                  case (_thenIsection, _toIsection) of
                     (False, False) -> enumFromThenToName
                     (False, True ) -> enumFromThenName
                     (True , False) -> enumFromToName
                     (True , True ) -> enumFromName
              _requiredDictionaries =
                  if _overloaded then _lhsIsubstitution |-> [Predicate "Enum" _elementType] else []
              _newDEnv =
                  resolveOverloading (_lhsIclassEnvironment)  _localName
                                     (_lhsIsubstitution |-> _lhsIavailablePredicates)
                                     (_lhsIsubstitution |-> _requiredDictionaries)
                                     _toIdictionaryEnvironment
              _cinfoFrom =
                  childConstraint 0 "enumeration" _parentTree
                     []
              _cinfoThen =
                  childConstraint 1 "enumeration" _parentTree
                     []
              _toChildNr =
                  1 + length _thenIinfoTrees
              _cinfoTo =
                  childConstraint _toChildNr "enumeration" _parentTree
                     []
              _cinfoResult =
                  resultConstraint "enumeration" _parentTree
                     [ FolkloreConstraint ]
              _cinfoPred =
                  resultConstraint "enumeration" _parentTree
                     [ ReductionErrorInfo (Predicate "Enum" _elementType) ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo (_fromIinfoTree : _thenIinfoTrees ++ _toIinfoTrees)
              _lhsOinfoTree =
                  _parentTree
              __tup8 =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in match3 infoTuple _toIuniqueSecondRound
                            match_Expression_Enum
                            _lhsItryPatterns _lhsIallPatterns
                            [_fromImatches, _thenImatches, _toImatches]
              (__tup9,_,_,_,_,_) =
                  __tup8
              (_fromOtryPatterns,_,_) =
                  __tup9
              (_,_thenOtryPatterns,_) =
                  __tup9
              (_,_,_toOtryPatterns) =
                  __tup9
              (_,_lhsOmatches,_,_,_,_) =
                  __tup8
              (_,_,_lhsOconstraints,_,_,_) =
                  __tup8
              (_,_,_,_lhsOassumptions,_,_) =
                  __tup8
              (_,_,_,_,_lhsOuniqueSecondRound,_) =
                  __tup8
              (_,_,_,_,_,_ioMatch) =
                  __tup8
              _lhsOmatchIO =
                  _toImatchIO              >> _ioMatch
              _lhsOcollectInstances =
                  _fromIcollectInstances  ++  _thenIcollectInstances  ++  _toIcollectInstances
              _lhsOunboundNames =
                  _fromIunboundNames ++ _thenIunboundNames ++ _toIunboundNames
              _self =
                  Expression_Enum _rangeIself _fromIself _thenIself _toIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _toIbetaUnique
              _lhsOcollectErrors =
                  _toIcollectErrors
              _lhsOcollectWarnings =
                  _toIcollectWarnings
              _lhsOpatternMatchWarnings =
                  _toIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _toIuniqueChunk
              _fromOallPatterns =
                  _lhsIallPatterns
              _fromOallTypeSchemes =
                  _lhsIallTypeSchemes
              _fromOavailablePredicates =
                  _lhsIavailablePredicates
              _fromOclassEnvironment =
                  _lhsIclassEnvironment
              _fromOcollectErrors =
                  _lhsIcollectErrors
              _fromOcollectWarnings =
                  _lhsIcollectWarnings
              _fromOcurrentChunk =
                  _lhsIcurrentChunk
              _fromOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _fromOimportEnvironment =
                  _lhsIimportEnvironment
              _fromOmatchIO =
                  _lhsImatchIO
              _fromOmonos =
                  _lhsImonos
              _fromOnamesInScope =
                  _lhsInamesInScope
              _fromOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _fromOparentTree =
                  _parentTree
              _fromOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _fromOsubstitution =
                  _lhsIsubstitution
              _fromOtypeschemeMap =
                  _lhsItypeschemeMap
              _fromOuniqueChunk =
                  _lhsIuniqueChunk
              _fromOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _thenOallPatterns =
                  _lhsIallPatterns
              _thenOallTypeSchemes =
                  _lhsIallTypeSchemes
              _thenOavailablePredicates =
                  _lhsIavailablePredicates
              _thenObetaUnique =
                  _fromIbetaUnique
              _thenOclassEnvironment =
                  _lhsIclassEnvironment
              _thenOcollectErrors =
                  _fromIcollectErrors
              _thenOcollectWarnings =
                  _fromIcollectWarnings
              _thenOcurrentChunk =
                  _lhsIcurrentChunk
              _thenOdictionaryEnvironment =
                  _fromIdictionaryEnvironment
              _thenOimportEnvironment =
                  _lhsIimportEnvironment
              _thenOmatchIO =
                  _fromImatchIO
              _thenOmonos =
                  _lhsImonos
              _thenOnamesInScope =
                  _lhsInamesInScope
              _thenOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _thenOparentTree =
                  _parentTree
              _thenOpatternMatchWarnings =
                  _fromIpatternMatchWarnings
              _thenOsubstitution =
                  _lhsIsubstitution
              _thenOtypeschemeMap =
                  _lhsItypeschemeMap
              _thenOuniqueChunk =
                  _fromIuniqueChunk
              _thenOuniqueSecondRound =
                  _fromIuniqueSecondRound
              _toOallPatterns =
                  _lhsIallPatterns
              _toOallTypeSchemes =
                  _lhsIallTypeSchemes
              _toOavailablePredicates =
                  _lhsIavailablePredicates
              _toObetaUnique =
                  _thenIbetaUnique
              _toOclassEnvironment =
                  _lhsIclassEnvironment
              _toOcollectErrors =
                  _thenIcollectErrors
              _toOcollectWarnings =
                  _thenIcollectWarnings
              _toOcurrentChunk =
                  _lhsIcurrentChunk
              _toOdictionaryEnvironment =
                  _thenIdictionaryEnvironment
              _toOimportEnvironment =
                  _lhsIimportEnvironment
              _toOmatchIO =
                  _thenImatchIO
              _toOmonos =
                  _lhsImonos
              _toOnamesInScope =
                  _lhsInamesInScope
              _toOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _toOparentTree =
                  _parentTree
              _toOpatternMatchWarnings =
                  _thenIpatternMatchWarnings
              _toOsubstitution =
                  _lhsIsubstitution
              _toOtypeschemeMap =
                  _lhsItypeschemeMap
              _toOuniqueChunk =
                  _thenIuniqueChunk
              _toOuniqueSecondRound =
                  _thenIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _fromIassumptions,_fromIbeta,_fromIbetaUnique,_fromIcollectErrors,_fromIcollectInstances,_fromIcollectWarnings,_fromIconstraints,_fromIdictionaryEnvironment,_fromIinfoTree,_fromImatchIO,_fromImatches,_fromIpatternMatchWarnings,_fromIself,_fromIunboundNames,_fromIuniqueChunk,_fromIuniqueSecondRound) =
                  (from_ _fromOallPatterns _fromOallTypeSchemes _fromOavailablePredicates _fromObetaUnique _fromOclassEnvironment _fromOcollectErrors _fromOcollectWarnings _fromOcurrentChunk _fromOdictionaryEnvironment _fromOimportEnvironment _fromOmatchIO _fromOmonos _fromOnamesInScope _fromOorderedTypeSynonyms _fromOparentTree _fromOpatternMatchWarnings _fromOsubstitution _fromOtryPatterns _fromOtypeschemeMap _fromOuniqueChunk _fromOuniqueSecondRound )
              ( _thenIassumptions,_thenIbeta,_thenIbetaUnique,_thenIcollectErrors,_thenIcollectInstances,_thenIcollectWarnings,_thenIconstraints,_thenIdictionaryEnvironment,_thenIinfoTrees,_thenImatchIO,_thenImatches,_thenIpatternMatchWarnings,_thenIsection,_thenIself,_thenIunboundNames,_thenIuniqueChunk,_thenIuniqueSecondRound) =
                  (then_ _thenOallPatterns _thenOallTypeSchemes _thenOavailablePredicates _thenObetaUnique _thenOclassEnvironment _thenOcollectErrors _thenOcollectWarnings _thenOcurrentChunk _thenOdictionaryEnvironment _thenOimportEnvironment _thenOmatchIO _thenOmonos _thenOnamesInScope _thenOorderedTypeSynonyms _thenOparentTree _thenOpatternMatchWarnings _thenOsubstitution _thenOtryPatterns _thenOtypeschemeMap _thenOuniqueChunk _thenOuniqueSecondRound )
              ( _toIassumptions,_toIbeta,_toIbetaUnique,_toIcollectErrors,_toIcollectInstances,_toIcollectWarnings,_toIconstraints,_toIdictionaryEnvironment,_toIinfoTrees,_toImatchIO,_toImatches,_toIpatternMatchWarnings,_toIsection,_toIself,_toIunboundNames,_toIuniqueChunk,_toIuniqueSecondRound) =
                  (to_ _toOallPatterns _toOallTypeSchemes _toOavailablePredicates _toObetaUnique _toOclassEnvironment _toOcollectErrors _toOcollectWarnings _toOcurrentChunk _toOdictionaryEnvironment _toOimportEnvironment _toOmatchIO _toOmonos _toOnamesInScope _toOorderedTypeSynonyms _toOparentTree _toOpatternMatchWarnings _toOsubstitution _toOtryPatterns _toOtypeschemeMap _toOuniqueChunk _toOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_If :: T_Range  ->
                     T_Expression  ->
                     T_Expression  ->
                     T_Expression  ->
                     T_Expression 
sem_Expression_If range_ guardExpression_ thenExpression_ elseExpression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _guardExpressionObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              __tup11 :: (([(Expression     , [String])],[(Expression     , [String])],[(Expression     , [String])]))
              _guardExpressionOtryPatterns :: ([(Expression     , [String])])
              _thenExpressionOtryPatterns :: ([(Expression     , [String])])
              _elseExpressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOuniqueSecondRound :: Int
              _lhsOmatchIO :: (IO ())
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _guardExpressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _guardExpressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _guardExpressionOavailablePredicates :: Predicates
              _guardExpressionOclassEnvironment :: ClassEnvironment
              _guardExpressionOcollectErrors :: TypeErrors
              _guardExpressionOcollectWarnings :: Warnings
              _guardExpressionOcurrentChunk :: Int
              _guardExpressionOdictionaryEnvironment :: DictionaryEnvironment
              _guardExpressionOimportEnvironment :: ImportEnvironment
              _guardExpressionOmatchIO :: (IO ())
              _guardExpressionOmonos :: Monos
              _guardExpressionOnamesInScope :: Names
              _guardExpressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _guardExpressionOparentTree :: InfoTree
              _guardExpressionOpatternMatchWarnings :: ([Warning])
              _guardExpressionOsubstitution :: FixpointSubstitution
              _guardExpressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _guardExpressionOuniqueChunk :: Int
              _guardExpressionOuniqueSecondRound :: Int
              _thenExpressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _thenExpressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _thenExpressionOavailablePredicates :: Predicates
              _thenExpressionObetaUnique :: Int
              _thenExpressionOclassEnvironment :: ClassEnvironment
              _thenExpressionOcollectErrors :: TypeErrors
              _thenExpressionOcollectWarnings :: Warnings
              _thenExpressionOcurrentChunk :: Int
              _thenExpressionOdictionaryEnvironment :: DictionaryEnvironment
              _thenExpressionOimportEnvironment :: ImportEnvironment
              _thenExpressionOmatchIO :: (IO ())
              _thenExpressionOmonos :: Monos
              _thenExpressionOnamesInScope :: Names
              _thenExpressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _thenExpressionOparentTree :: InfoTree
              _thenExpressionOpatternMatchWarnings :: ([Warning])
              _thenExpressionOsubstitution :: FixpointSubstitution
              _thenExpressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _thenExpressionOuniqueChunk :: Int
              _thenExpressionOuniqueSecondRound :: Int
              _elseExpressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _elseExpressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _elseExpressionOavailablePredicates :: Predicates
              _elseExpressionObetaUnique :: Int
              _elseExpressionOclassEnvironment :: ClassEnvironment
              _elseExpressionOcollectErrors :: TypeErrors
              _elseExpressionOcollectWarnings :: Warnings
              _elseExpressionOcurrentChunk :: Int
              _elseExpressionOdictionaryEnvironment :: DictionaryEnvironment
              _elseExpressionOimportEnvironment :: ImportEnvironment
              _elseExpressionOmatchIO :: (IO ())
              _elseExpressionOmonos :: Monos
              _elseExpressionOnamesInScope :: Names
              _elseExpressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _elseExpressionOparentTree :: InfoTree
              _elseExpressionOpatternMatchWarnings :: ([Warning])
              _elseExpressionOsubstitution :: FixpointSubstitution
              _elseExpressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _elseExpressionOuniqueChunk :: Int
              _elseExpressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _guardExpressionIassumptions :: Assumptions
              _guardExpressionIbeta :: Tp
              _guardExpressionIbetaUnique :: Int
              _guardExpressionIcollectErrors :: TypeErrors
              _guardExpressionIcollectInstances :: ([(Name, Instance)])
              _guardExpressionIcollectWarnings :: Warnings
              _guardExpressionIconstraints :: ConstraintSet
              _guardExpressionIdictionaryEnvironment :: DictionaryEnvironment
              _guardExpressionIinfoTree :: InfoTree
              _guardExpressionImatchIO :: (IO ())
              _guardExpressionImatches :: ([Maybe MetaVariableTable])
              _guardExpressionIpatternMatchWarnings :: ([Warning])
              _guardExpressionIself :: Expression
              _guardExpressionIunboundNames :: Names
              _guardExpressionIuniqueChunk :: Int
              _guardExpressionIuniqueSecondRound :: Int
              _thenExpressionIassumptions :: Assumptions
              _thenExpressionIbeta :: Tp
              _thenExpressionIbetaUnique :: Int
              _thenExpressionIcollectErrors :: TypeErrors
              _thenExpressionIcollectInstances :: ([(Name, Instance)])
              _thenExpressionIcollectWarnings :: Warnings
              _thenExpressionIconstraints :: ConstraintSet
              _thenExpressionIdictionaryEnvironment :: DictionaryEnvironment
              _thenExpressionIinfoTree :: InfoTree
              _thenExpressionImatchIO :: (IO ())
              _thenExpressionImatches :: ([Maybe MetaVariableTable])
              _thenExpressionIpatternMatchWarnings :: ([Warning])
              _thenExpressionIself :: Expression
              _thenExpressionIunboundNames :: Names
              _thenExpressionIuniqueChunk :: Int
              _thenExpressionIuniqueSecondRound :: Int
              _elseExpressionIassumptions :: Assumptions
              _elseExpressionIbeta :: Tp
              _elseExpressionIbetaUnique :: Int
              _elseExpressionIcollectErrors :: TypeErrors
              _elseExpressionIcollectInstances :: ([(Name, Instance)])
              _elseExpressionIcollectWarnings :: Warnings
              _elseExpressionIconstraints :: ConstraintSet
              _elseExpressionIdictionaryEnvironment :: DictionaryEnvironment
              _elseExpressionIinfoTree :: InfoTree
              _elseExpressionImatchIO :: (IO ())
              _elseExpressionImatches :: ([Maybe MetaVariableTable])
              _elseExpressionIpatternMatchWarnings :: ([Warning])
              _elseExpressionIself :: Expression
              _elseExpressionIunboundNames :: Names
              _elseExpressionIuniqueChunk :: Int
              _elseExpressionIuniqueSecondRound :: Int
              _guardExpressionObetaUnique =
                  _lhsIbetaUnique + 1
              _assumptions =
                  _guardExpressionIassumptions `combine` _thenExpressionIassumptions `combine` _elseExpressionIassumptions
              _constraints =
                  Node [ _conGuard .<. _guardExpressionIconstraints
                       , _conThen  .<. _thenExpressionIconstraints
                       , _conElse  .<. _elseExpressionIconstraints
                       ]
              _beta =
                  TVar _lhsIbetaUnique
              _conGuard =
                  [ (_guardExpressionIbeta .==. boolType) _cinfoGuard ]
              _conThen =
                  [ (_thenExpressionIbeta  .==. _beta   ) _cinfoThen  ]
              _conElse =
                  [ (_elseExpressionIbeta  .==. _beta   ) _cinfoElse  ]
              _cinfoGuard =
                  childConstraint 0 "conditional" _parentTree
                     []
              _cinfoThen =
                  childConstraint 1 "then branch of conditional" _parentTree
                     [ Unifier (head (ftv _beta)) ("conditional", _localInfo, "then branch") ]
              _cinfoElse =
                  childConstraint 2 "else branch of conditional" _parentTree
                     [ Unifier (head (ftv _beta)) ("conditional", _localInfo, "else branch") ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo [_guardExpressionIinfoTree, _thenExpressionIinfoTree, _elseExpressionIinfoTree]
              _lhsOinfoTree =
                  _parentTree
              __tup10 =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in match3 infoTuple _elseExpressionIuniqueSecondRound
                            match_Expression_If
                            _lhsItryPatterns _lhsIallPatterns
                            [_guardExpressionImatches,_thenExpressionImatches,_elseExpressionImatches]
              (__tup11,_,_,_,_,_) =
                  __tup10
              (_guardExpressionOtryPatterns,_,_) =
                  __tup11
              (_,_thenExpressionOtryPatterns,_) =
                  __tup11
              (_,_,_elseExpressionOtryPatterns) =
                  __tup11
              (_,_lhsOmatches,_,_,_,_) =
                  __tup10
              (_,_,_lhsOconstraints,_,_,_) =
                  __tup10
              (_,_,_,_lhsOassumptions,_,_) =
                  __tup10
              (_,_,_,_,_lhsOuniqueSecondRound,_) =
                  __tup10
              (_,_,_,_,_,_ioMatch) =
                  __tup10
              _lhsOmatchIO =
                  _elseExpressionImatchIO  >> _ioMatch
              _lhsOcollectInstances =
                  _guardExpressionIcollectInstances  ++  _thenExpressionIcollectInstances  ++  _elseExpressionIcollectInstances
              _lhsOunboundNames =
                  _guardExpressionIunboundNames ++ _thenExpressionIunboundNames ++ _elseExpressionIunboundNames
              _self =
                  Expression_If _rangeIself _guardExpressionIself _thenExpressionIself _elseExpressionIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _elseExpressionIbetaUnique
              _lhsOcollectErrors =
                  _elseExpressionIcollectErrors
              _lhsOcollectWarnings =
                  _elseExpressionIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _elseExpressionIdictionaryEnvironment
              _lhsOpatternMatchWarnings =
                  _elseExpressionIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _elseExpressionIuniqueChunk
              _guardExpressionOallPatterns =
                  _lhsIallPatterns
              _guardExpressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _guardExpressionOavailablePredicates =
                  _lhsIavailablePredicates
              _guardExpressionOclassEnvironment =
                  _lhsIclassEnvironment
              _guardExpressionOcollectErrors =
                  _lhsIcollectErrors
              _guardExpressionOcollectWarnings =
                  _lhsIcollectWarnings
              _guardExpressionOcurrentChunk =
                  _lhsIcurrentChunk
              _guardExpressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _guardExpressionOimportEnvironment =
                  _lhsIimportEnvironment
              _guardExpressionOmatchIO =
                  _lhsImatchIO
              _guardExpressionOmonos =
                  _lhsImonos
              _guardExpressionOnamesInScope =
                  _lhsInamesInScope
              _guardExpressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _guardExpressionOparentTree =
                  _parentTree
              _guardExpressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _guardExpressionOsubstitution =
                  _lhsIsubstitution
              _guardExpressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _guardExpressionOuniqueChunk =
                  _lhsIuniqueChunk
              _guardExpressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _thenExpressionOallPatterns =
                  _lhsIallPatterns
              _thenExpressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _thenExpressionOavailablePredicates =
                  _lhsIavailablePredicates
              _thenExpressionObetaUnique =
                  _guardExpressionIbetaUnique
              _thenExpressionOclassEnvironment =
                  _lhsIclassEnvironment
              _thenExpressionOcollectErrors =
                  _guardExpressionIcollectErrors
              _thenExpressionOcollectWarnings =
                  _guardExpressionIcollectWarnings
              _thenExpressionOcurrentChunk =
                  _lhsIcurrentChunk
              _thenExpressionOdictionaryEnvironment =
                  _guardExpressionIdictionaryEnvironment
              _thenExpressionOimportEnvironment =
                  _lhsIimportEnvironment
              _thenExpressionOmatchIO =
                  _guardExpressionImatchIO
              _thenExpressionOmonos =
                  _lhsImonos
              _thenExpressionOnamesInScope =
                  _lhsInamesInScope
              _thenExpressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _thenExpressionOparentTree =
                  _parentTree
              _thenExpressionOpatternMatchWarnings =
                  _guardExpressionIpatternMatchWarnings
              _thenExpressionOsubstitution =
                  _lhsIsubstitution
              _thenExpressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _thenExpressionOuniqueChunk =
                  _guardExpressionIuniqueChunk
              _thenExpressionOuniqueSecondRound =
                  _guardExpressionIuniqueSecondRound
              _elseExpressionOallPatterns =
                  _lhsIallPatterns
              _elseExpressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _elseExpressionOavailablePredicates =
                  _lhsIavailablePredicates
              _elseExpressionObetaUnique =
                  _thenExpressionIbetaUnique
              _elseExpressionOclassEnvironment =
                  _lhsIclassEnvironment
              _elseExpressionOcollectErrors =
                  _thenExpressionIcollectErrors
              _elseExpressionOcollectWarnings =
                  _thenExpressionIcollectWarnings
              _elseExpressionOcurrentChunk =
                  _lhsIcurrentChunk
              _elseExpressionOdictionaryEnvironment =
                  _thenExpressionIdictionaryEnvironment
              _elseExpressionOimportEnvironment =
                  _lhsIimportEnvironment
              _elseExpressionOmatchIO =
                  _thenExpressionImatchIO
              _elseExpressionOmonos =
                  _lhsImonos
              _elseExpressionOnamesInScope =
                  _lhsInamesInScope
              _elseExpressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _elseExpressionOparentTree =
                  _parentTree
              _elseExpressionOpatternMatchWarnings =
                  _thenExpressionIpatternMatchWarnings
              _elseExpressionOsubstitution =
                  _lhsIsubstitution
              _elseExpressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _elseExpressionOuniqueChunk =
                  _thenExpressionIuniqueChunk
              _elseExpressionOuniqueSecondRound =
                  _thenExpressionIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _guardExpressionIassumptions,_guardExpressionIbeta,_guardExpressionIbetaUnique,_guardExpressionIcollectErrors,_guardExpressionIcollectInstances,_guardExpressionIcollectWarnings,_guardExpressionIconstraints,_guardExpressionIdictionaryEnvironment,_guardExpressionIinfoTree,_guardExpressionImatchIO,_guardExpressionImatches,_guardExpressionIpatternMatchWarnings,_guardExpressionIself,_guardExpressionIunboundNames,_guardExpressionIuniqueChunk,_guardExpressionIuniqueSecondRound) =
                  (guardExpression_ _guardExpressionOallPatterns _guardExpressionOallTypeSchemes _guardExpressionOavailablePredicates _guardExpressionObetaUnique _guardExpressionOclassEnvironment _guardExpressionOcollectErrors _guardExpressionOcollectWarnings _guardExpressionOcurrentChunk _guardExpressionOdictionaryEnvironment _guardExpressionOimportEnvironment _guardExpressionOmatchIO _guardExpressionOmonos _guardExpressionOnamesInScope _guardExpressionOorderedTypeSynonyms _guardExpressionOparentTree _guardExpressionOpatternMatchWarnings _guardExpressionOsubstitution _guardExpressionOtryPatterns _guardExpressionOtypeschemeMap _guardExpressionOuniqueChunk _guardExpressionOuniqueSecondRound )
              ( _thenExpressionIassumptions,_thenExpressionIbeta,_thenExpressionIbetaUnique,_thenExpressionIcollectErrors,_thenExpressionIcollectInstances,_thenExpressionIcollectWarnings,_thenExpressionIconstraints,_thenExpressionIdictionaryEnvironment,_thenExpressionIinfoTree,_thenExpressionImatchIO,_thenExpressionImatches,_thenExpressionIpatternMatchWarnings,_thenExpressionIself,_thenExpressionIunboundNames,_thenExpressionIuniqueChunk,_thenExpressionIuniqueSecondRound) =
                  (thenExpression_ _thenExpressionOallPatterns _thenExpressionOallTypeSchemes _thenExpressionOavailablePredicates _thenExpressionObetaUnique _thenExpressionOclassEnvironment _thenExpressionOcollectErrors _thenExpressionOcollectWarnings _thenExpressionOcurrentChunk _thenExpressionOdictionaryEnvironment _thenExpressionOimportEnvironment _thenExpressionOmatchIO _thenExpressionOmonos _thenExpressionOnamesInScope _thenExpressionOorderedTypeSynonyms _thenExpressionOparentTree _thenExpressionOpatternMatchWarnings _thenExpressionOsubstitution _thenExpressionOtryPatterns _thenExpressionOtypeschemeMap _thenExpressionOuniqueChunk _thenExpressionOuniqueSecondRound )
              ( _elseExpressionIassumptions,_elseExpressionIbeta,_elseExpressionIbetaUnique,_elseExpressionIcollectErrors,_elseExpressionIcollectInstances,_elseExpressionIcollectWarnings,_elseExpressionIconstraints,_elseExpressionIdictionaryEnvironment,_elseExpressionIinfoTree,_elseExpressionImatchIO,_elseExpressionImatches,_elseExpressionIpatternMatchWarnings,_elseExpressionIself,_elseExpressionIunboundNames,_elseExpressionIuniqueChunk,_elseExpressionIuniqueSecondRound) =
                  (elseExpression_ _elseExpressionOallPatterns _elseExpressionOallTypeSchemes _elseExpressionOavailablePredicates _elseExpressionObetaUnique _elseExpressionOclassEnvironment _elseExpressionOcollectErrors _elseExpressionOcollectWarnings _elseExpressionOcurrentChunk _elseExpressionOdictionaryEnvironment _elseExpressionOimportEnvironment _elseExpressionOmatchIO _elseExpressionOmonos _elseExpressionOnamesInScope _elseExpressionOorderedTypeSynonyms _elseExpressionOparentTree _elseExpressionOpatternMatchWarnings _elseExpressionOsubstitution _elseExpressionOtryPatterns _elseExpressionOtypeschemeMap _elseExpressionOuniqueChunk _elseExpressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_InfixApplication :: T_Range  ->
                                   T_MaybeExpression  ->
                                   T_Expression  ->
                                   T_MaybeExpression  ->
                                   T_Expression 
sem_Expression_InfixApplication range_ leftExpression_ operator_ rightExpression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _leftExpressionObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              __tup13 :: (([(MaybeExpression, [String])],[(Expression     , [String])],[(MaybeExpression, [String])]))
              _leftExpressionOtryPatterns :: ([(MaybeExpression, [String])])
              _operatorOtryPatterns :: ([(Expression     , [String])])
              _rightExpressionOtryPatterns :: ([(MaybeExpression, [String])])
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOuniqueSecondRound :: Int
              _lhsOmatchIO :: (IO ())
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _leftExpressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _leftExpressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _leftExpressionOavailablePredicates :: Predicates
              _leftExpressionOclassEnvironment :: ClassEnvironment
              _leftExpressionOcollectErrors :: TypeErrors
              _leftExpressionOcollectWarnings :: Warnings
              _leftExpressionOcurrentChunk :: Int
              _leftExpressionOdictionaryEnvironment :: DictionaryEnvironment
              _leftExpressionOimportEnvironment :: ImportEnvironment
              _leftExpressionOmatchIO :: (IO ())
              _leftExpressionOmonos :: Monos
              _leftExpressionOnamesInScope :: Names
              _leftExpressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _leftExpressionOparentTree :: InfoTree
              _leftExpressionOpatternMatchWarnings :: ([Warning])
              _leftExpressionOsubstitution :: FixpointSubstitution
              _leftExpressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _leftExpressionOuniqueChunk :: Int
              _leftExpressionOuniqueSecondRound :: Int
              _operatorOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _operatorOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _operatorOavailablePredicates :: Predicates
              _operatorObetaUnique :: Int
              _operatorOclassEnvironment :: ClassEnvironment
              _operatorOcollectErrors :: TypeErrors
              _operatorOcollectWarnings :: Warnings
              _operatorOcurrentChunk :: Int
              _operatorOdictionaryEnvironment :: DictionaryEnvironment
              _operatorOimportEnvironment :: ImportEnvironment
              _operatorOmatchIO :: (IO ())
              _operatorOmonos :: Monos
              _operatorOnamesInScope :: Names
              _operatorOorderedTypeSynonyms :: OrderedTypeSynonyms
              _operatorOparentTree :: InfoTree
              _operatorOpatternMatchWarnings :: ([Warning])
              _operatorOsubstitution :: FixpointSubstitution
              _operatorOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _operatorOuniqueChunk :: Int
              _operatorOuniqueSecondRound :: Int
              _rightExpressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _rightExpressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _rightExpressionOavailablePredicates :: Predicates
              _rightExpressionObetaUnique :: Int
              _rightExpressionOclassEnvironment :: ClassEnvironment
              _rightExpressionOcollectErrors :: TypeErrors
              _rightExpressionOcollectWarnings :: Warnings
              _rightExpressionOcurrentChunk :: Int
              _rightExpressionOdictionaryEnvironment :: DictionaryEnvironment
              _rightExpressionOimportEnvironment :: ImportEnvironment
              _rightExpressionOmatchIO :: (IO ())
              _rightExpressionOmonos :: Monos
              _rightExpressionOnamesInScope :: Names
              _rightExpressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _rightExpressionOparentTree :: InfoTree
              _rightExpressionOpatternMatchWarnings :: ([Warning])
              _rightExpressionOsubstitution :: FixpointSubstitution
              _rightExpressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _rightExpressionOuniqueChunk :: Int
              _rightExpressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _leftExpressionIassumptions :: Assumptions
              _leftExpressionIbeta :: Tp
              _leftExpressionIbetaUnique :: Int
              _leftExpressionIcollectErrors :: TypeErrors
              _leftExpressionIcollectInstances :: ([(Name, Instance)])
              _leftExpressionIcollectWarnings :: Warnings
              _leftExpressionIconstraints :: ConstraintSet
              _leftExpressionIdictionaryEnvironment :: DictionaryEnvironment
              _leftExpressionIinfoTrees :: InfoTrees
              _leftExpressionImatchIO :: (IO ())
              _leftExpressionImatches :: ([Maybe MetaVariableTable])
              _leftExpressionIpatternMatchWarnings :: ([Warning])
              _leftExpressionIsection :: Bool
              _leftExpressionIself :: MaybeExpression
              _leftExpressionIunboundNames :: Names
              _leftExpressionIuniqueChunk :: Int
              _leftExpressionIuniqueSecondRound :: Int
              _operatorIassumptions :: Assumptions
              _operatorIbeta :: Tp
              _operatorIbetaUnique :: Int
              _operatorIcollectErrors :: TypeErrors
              _operatorIcollectInstances :: ([(Name, Instance)])
              _operatorIcollectWarnings :: Warnings
              _operatorIconstraints :: ConstraintSet
              _operatorIdictionaryEnvironment :: DictionaryEnvironment
              _operatorIinfoTree :: InfoTree
              _operatorImatchIO :: (IO ())
              _operatorImatches :: ([Maybe MetaVariableTable])
              _operatorIpatternMatchWarnings :: ([Warning])
              _operatorIself :: Expression
              _operatorIunboundNames :: Names
              _operatorIuniqueChunk :: Int
              _operatorIuniqueSecondRound :: Int
              _rightExpressionIassumptions :: Assumptions
              _rightExpressionIbeta :: Tp
              _rightExpressionIbetaUnique :: Int
              _rightExpressionIcollectErrors :: TypeErrors
              _rightExpressionIcollectInstances :: ([(Name, Instance)])
              _rightExpressionIcollectWarnings :: Warnings
              _rightExpressionIconstraints :: ConstraintSet
              _rightExpressionIdictionaryEnvironment :: DictionaryEnvironment
              _rightExpressionIinfoTrees :: InfoTrees
              _rightExpressionImatchIO :: (IO ())
              _rightExpressionImatches :: ([Maybe MetaVariableTable])
              _rightExpressionIpatternMatchWarnings :: ([Warning])
              _rightExpressionIsection :: Bool
              _rightExpressionIself :: MaybeExpression
              _rightExpressionIunboundNames :: Names
              _rightExpressionIuniqueChunk :: Int
              _rightExpressionIuniqueSecondRound :: Int
              _leftExpressionObetaUnique =
                  _lhsIbetaUnique + 2
              _assumptions =
                  _leftExpressionIassumptions `combine` _operatorIassumptions `combine` _rightExpressionIassumptions
              _constraints =
                  _conTotal .>.
                  Node [ _operatorIconstraints
                       , _leftExpressionIconstraints
                       , _rightExpressionIconstraints
                       ]
              _beta =
                  TVar _lhsIbetaUnique
              _betaResOp =
                  TVar (_lhsIbetaUnique + 1)
              _conOperator =
                  (_operatorIbeta .==. _leftExpressionIbeta .->. _rightExpressionIbeta .->. _betaResOp) _cinfoOperator
              _conTotal =
                  case (_leftExpressionIsection,_rightExpressionIsection) of
                         (False,False) -> [ _conOperator, (_betaResOp     .==. _beta)                        _cinfoComplete     ]
                         (True ,True ) -> [               (_operatorIbeta .==. _beta)                        _cinfoEmpty        ]
                         (False,True ) -> [ _conOperator, (_rightExpressionIbeta .->. _betaResOp .==. _beta) _cinfoRightSection ]
                         (True ,False) -> [ _conOperator, (_leftExpressionIbeta  .->. _betaResOp .==. _beta) _cinfoLeftSection  ]
              _operatorNr =
                  length _leftExpressionIinfoTrees
              _cinfoOperator =
                  childConstraint _operatorNr "infix application" _parentTree $
                     if _leftExpressionIsection || _rightExpressionIsection
                     then [ HasTrustFactor 10.0 ]
                     else [ ApplicationEdge True (map attribute (_leftExpressionIinfoTrees ++ _rightExpressionIinfoTrees)) ]
              _cinfoComplete =
                  specialConstraint "infix application (INTERNAL ERROR)" _parentTree
                     (self _localInfo, Nothing)
                     [ FolkloreConstraint, highlyTrusted ]
              _cinfoLeftSection =
                  specialConstraint "left section" _parentTree
                     (self _localInfo, Nothing)
                     [  ]
              _cinfoRightSection =
                  specialConstraint "right section" _parentTree
                     (self _localInfo, Nothing)
                     [ ]
              _cinfoEmpty =
                  specialConstraint "infix application" _parentTree
                    (self _localInfo, Nothing)
                    [ FolkloreConstraint, HasTrustFactor 10.0 ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo
                    (_leftExpressionIinfoTrees ++ [_operatorIinfoTree] ++ _rightExpressionIinfoTrees)
              _lhsOinfoTree =
                  _parentTree
              __tup12 =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in match3 infoTuple _rightExpressionIuniqueSecondRound
                            match_Expression_InfixApplication
                            _lhsItryPatterns _lhsIallPatterns
                            [_leftExpressionImatches, _operatorImatches,_rightExpressionImatches]
              (__tup13,_,_,_,_,_) =
                  __tup12
              (_leftExpressionOtryPatterns,_,_) =
                  __tup13
              (_,_operatorOtryPatterns,_) =
                  __tup13
              (_,_,_rightExpressionOtryPatterns) =
                  __tup13
              (_,_lhsOmatches,_,_,_,_) =
                  __tup12
              (_,_,_lhsOconstraints,_,_,_) =
                  __tup12
              (_,_,_,_lhsOassumptions,_,_) =
                  __tup12
              (_,_,_,_,_lhsOuniqueSecondRound,_) =
                  __tup12
              (_,_,_,_,_,_ioMatch) =
                  __tup12
              _lhsOmatchIO =
                  _rightExpressionImatchIO >> _ioMatch
              _lhsOcollectInstances =
                  _leftExpressionIcollectInstances  ++  _operatorIcollectInstances  ++  _rightExpressionIcollectInstances
              _lhsOunboundNames =
                  _leftExpressionIunboundNames ++ _operatorIunboundNames ++ _rightExpressionIunboundNames
              _self =
                  Expression_InfixApplication _rangeIself _leftExpressionIself _operatorIself _rightExpressionIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _rightExpressionIbetaUnique
              _lhsOcollectErrors =
                  _rightExpressionIcollectErrors
              _lhsOcollectWarnings =
                  _rightExpressionIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _rightExpressionIdictionaryEnvironment
              _lhsOpatternMatchWarnings =
                  _rightExpressionIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _rightExpressionIuniqueChunk
              _leftExpressionOallPatterns =
                  _lhsIallPatterns
              _leftExpressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _leftExpressionOavailablePredicates =
                  _lhsIavailablePredicates
              _leftExpressionOclassEnvironment =
                  _lhsIclassEnvironment
              _leftExpressionOcollectErrors =
                  _lhsIcollectErrors
              _leftExpressionOcollectWarnings =
                  _lhsIcollectWarnings
              _leftExpressionOcurrentChunk =
                  _lhsIcurrentChunk
              _leftExpressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _leftExpressionOimportEnvironment =
                  _lhsIimportEnvironment
              _leftExpressionOmatchIO =
                  _lhsImatchIO
              _leftExpressionOmonos =
                  _lhsImonos
              _leftExpressionOnamesInScope =
                  _lhsInamesInScope
              _leftExpressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _leftExpressionOparentTree =
                  _parentTree
              _leftExpressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _leftExpressionOsubstitution =
                  _lhsIsubstitution
              _leftExpressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _leftExpressionOuniqueChunk =
                  _lhsIuniqueChunk
              _leftExpressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _operatorOallPatterns =
                  _lhsIallPatterns
              _operatorOallTypeSchemes =
                  _lhsIallTypeSchemes
              _operatorOavailablePredicates =
                  _lhsIavailablePredicates
              _operatorObetaUnique =
                  _leftExpressionIbetaUnique
              _operatorOclassEnvironment =
                  _lhsIclassEnvironment
              _operatorOcollectErrors =
                  _leftExpressionIcollectErrors
              _operatorOcollectWarnings =
                  _leftExpressionIcollectWarnings
              _operatorOcurrentChunk =
                  _lhsIcurrentChunk
              _operatorOdictionaryEnvironment =
                  _leftExpressionIdictionaryEnvironment
              _operatorOimportEnvironment =
                  _lhsIimportEnvironment
              _operatorOmatchIO =
                  _leftExpressionImatchIO
              _operatorOmonos =
                  _lhsImonos
              _operatorOnamesInScope =
                  _lhsInamesInScope
              _operatorOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _operatorOparentTree =
                  _parentTree
              _operatorOpatternMatchWarnings =
                  _leftExpressionIpatternMatchWarnings
              _operatorOsubstitution =
                  _lhsIsubstitution
              _operatorOtypeschemeMap =
                  _lhsItypeschemeMap
              _operatorOuniqueChunk =
                  _leftExpressionIuniqueChunk
              _operatorOuniqueSecondRound =
                  _leftExpressionIuniqueSecondRound
              _rightExpressionOallPatterns =
                  _lhsIallPatterns
              _rightExpressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _rightExpressionOavailablePredicates =
                  _lhsIavailablePredicates
              _rightExpressionObetaUnique =
                  _operatorIbetaUnique
              _rightExpressionOclassEnvironment =
                  _lhsIclassEnvironment
              _rightExpressionOcollectErrors =
                  _operatorIcollectErrors
              _rightExpressionOcollectWarnings =
                  _operatorIcollectWarnings
              _rightExpressionOcurrentChunk =
                  _lhsIcurrentChunk
              _rightExpressionOdictionaryEnvironment =
                  _operatorIdictionaryEnvironment
              _rightExpressionOimportEnvironment =
                  _lhsIimportEnvironment
              _rightExpressionOmatchIO =
                  _operatorImatchIO
              _rightExpressionOmonos =
                  _lhsImonos
              _rightExpressionOnamesInScope =
                  _lhsInamesInScope
              _rightExpressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _rightExpressionOparentTree =
                  _parentTree
              _rightExpressionOpatternMatchWarnings =
                  _operatorIpatternMatchWarnings
              _rightExpressionOsubstitution =
                  _lhsIsubstitution
              _rightExpressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _rightExpressionOuniqueChunk =
                  _operatorIuniqueChunk
              _rightExpressionOuniqueSecondRound =
                  _operatorIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _leftExpressionIassumptions,_leftExpressionIbeta,_leftExpressionIbetaUnique,_leftExpressionIcollectErrors,_leftExpressionIcollectInstances,_leftExpressionIcollectWarnings,_leftExpressionIconstraints,_leftExpressionIdictionaryEnvironment,_leftExpressionIinfoTrees,_leftExpressionImatchIO,_leftExpressionImatches,_leftExpressionIpatternMatchWarnings,_leftExpressionIsection,_leftExpressionIself,_leftExpressionIunboundNames,_leftExpressionIuniqueChunk,_leftExpressionIuniqueSecondRound) =
                  (leftExpression_ _leftExpressionOallPatterns _leftExpressionOallTypeSchemes _leftExpressionOavailablePredicates _leftExpressionObetaUnique _leftExpressionOclassEnvironment _leftExpressionOcollectErrors _leftExpressionOcollectWarnings _leftExpressionOcurrentChunk _leftExpressionOdictionaryEnvironment _leftExpressionOimportEnvironment _leftExpressionOmatchIO _leftExpressionOmonos _leftExpressionOnamesInScope _leftExpressionOorderedTypeSynonyms _leftExpressionOparentTree _leftExpressionOpatternMatchWarnings _leftExpressionOsubstitution _leftExpressionOtryPatterns _leftExpressionOtypeschemeMap _leftExpressionOuniqueChunk _leftExpressionOuniqueSecondRound )
              ( _operatorIassumptions,_operatorIbeta,_operatorIbetaUnique,_operatorIcollectErrors,_operatorIcollectInstances,_operatorIcollectWarnings,_operatorIconstraints,_operatorIdictionaryEnvironment,_operatorIinfoTree,_operatorImatchIO,_operatorImatches,_operatorIpatternMatchWarnings,_operatorIself,_operatorIunboundNames,_operatorIuniqueChunk,_operatorIuniqueSecondRound) =
                  (operator_ _operatorOallPatterns _operatorOallTypeSchemes _operatorOavailablePredicates _operatorObetaUnique _operatorOclassEnvironment _operatorOcollectErrors _operatorOcollectWarnings _operatorOcurrentChunk _operatorOdictionaryEnvironment _operatorOimportEnvironment _operatorOmatchIO _operatorOmonos _operatorOnamesInScope _operatorOorderedTypeSynonyms _operatorOparentTree _operatorOpatternMatchWarnings _operatorOsubstitution _operatorOtryPatterns _operatorOtypeschemeMap _operatorOuniqueChunk _operatorOuniqueSecondRound )
              ( _rightExpressionIassumptions,_rightExpressionIbeta,_rightExpressionIbetaUnique,_rightExpressionIcollectErrors,_rightExpressionIcollectInstances,_rightExpressionIcollectWarnings,_rightExpressionIconstraints,_rightExpressionIdictionaryEnvironment,_rightExpressionIinfoTrees,_rightExpressionImatchIO,_rightExpressionImatches,_rightExpressionIpatternMatchWarnings,_rightExpressionIsection,_rightExpressionIself,_rightExpressionIunboundNames,_rightExpressionIuniqueChunk,_rightExpressionIuniqueSecondRound) =
                  (rightExpression_ _rightExpressionOallPatterns _rightExpressionOallTypeSchemes _rightExpressionOavailablePredicates _rightExpressionObetaUnique _rightExpressionOclassEnvironment _rightExpressionOcollectErrors _rightExpressionOcollectWarnings _rightExpressionOcurrentChunk _rightExpressionOdictionaryEnvironment _rightExpressionOimportEnvironment _rightExpressionOmatchIO _rightExpressionOmonos _rightExpressionOnamesInScope _rightExpressionOorderedTypeSynonyms _rightExpressionOparentTree _rightExpressionOpatternMatchWarnings _rightExpressionOsubstitution _rightExpressionOtryPatterns _rightExpressionOtypeschemeMap _rightExpressionOuniqueChunk _rightExpressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Lambda :: T_Range  ->
                         T_Patterns  ->
                         T_Expression  ->
                         T_Expression 
sem_Expression_Lambda range_ patterns_ expression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _patternsObetaUnique :: Int
              _expressionOmonos :: Monos
              _lhsOinfoTree :: InfoTree
              _lhsOunboundNames :: Names
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Expression
              _lhsOassumptions :: Assumptions
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _patternsOimportEnvironment :: ImportEnvironment
              _patternsOmonos :: Monos
              _patternsOnamesInScope :: Names
              _patternsOparentTree :: InfoTree
              _patternsOpatternMatchWarnings :: ([Warning])
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionObetaUnique :: Int
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _patternsIbetaUnique :: Int
              _patternsIbetas :: Tps
              _patternsIconstraintslist :: ConstraintSets
              _patternsIelementss :: ([ [PatternElement]       ])
              _patternsIenvironment :: PatternAssumptions
              _patternsIinfoTrees :: InfoTrees
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIpatternMatchWarnings :: ([Warning])
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _patternsObetaUnique =
                  _lhsIbetaUnique + 1
              _expressionOmonos =
                  M.elems _patternsIenvironment ++ getMonos _csetBinds ++ _lhsImonos
              _constraints =
                  _newcon .>. _csetBinds .>>.
                  Node [ Node _patternsIconstraintslist
                       , _expressionIconstraints
                       ]
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  [ (foldr (.->.) _expressionIbeta _patternsIbetas .==. _beta) _cinfoType ]
              __tup14 =
                  (_patternsIenvironment .===. _expressionIassumptions) _cinfoBind
              (_csetBinds,_) =
                  __tup14
              (_,_assumptions) =
                  __tup14
              _cinfoBind =
                  \name -> variableConstraint "variable" (nameToUHA_Expr name)
                     [ FolkloreConstraint
                     , makeUnifier name "lambda abstraction" _patternsIenvironment _parentTree
                     ]
              _cinfoType =
                  resultConstraint "lambda abstraction" _parentTree
                     [ FolkloreConstraint ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo (_patternsIinfoTrees ++ [_expressionIinfoTree])
              _lhsOinfoTree =
                  _parentTree
              __tup15 =
                  changeOfScope _patternsIpatVarNames _expressionIunboundNames _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup15
              (_,_unboundNames,_) =
                  __tup15
              (_,_,_scopeInfo) =
                  __tup15
              _lhsOunboundNames =
                  _unboundNames
              _lhsOmatches =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in matchOnlyVariable infoTuple _lhsItryPatterns
              _expressionOtryPatterns =
                  []
              _lhsOpatternMatchWarnings =
                  patternMatchWarnings _lhsIimportEnvironment
                                       _lhsIsubstitution
                                       _beta
                                       (take (length _patternsIself) . fst . functionSpine)
                                       [(concat _patternsIelementss, False)]
                                       _rangeIself
                                       (Just $ Name_Special noRange [] "\\")
                                       True
                                       []
                                       "lambda expression"
                                       "->"
                  ++ _expressionIpatternMatchWarnings
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _self =
                  Expression_Lambda _rangeIself _patternsIself _expressionIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _assumptions
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _expressionIbetaUnique
              _lhsOcollectErrors =
                  _expressionIcollectErrors
              _lhsOcollectWarnings =
                  _expressionIcollectWarnings
              _lhsOconstraints =
                  _constraints
              _lhsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _lhsOmatchIO =
                  _expressionImatchIO
              _lhsOuniqueChunk =
                  _expressionIuniqueChunk
              _lhsOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              _patternsOimportEnvironment =
                  _lhsIimportEnvironment
              _patternsOmonos =
                  _lhsImonos
              _patternsOnamesInScope =
                  _namesInScope
              _patternsOparentTree =
                  _parentTree
              _patternsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionObetaUnique =
                  _patternsIbetaUnique
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOnamesInScope =
                  _namesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _parentTree
              _expressionOpatternMatchWarnings =
                  _patternsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _patternsIbetaUnique,_patternsIbetas,_patternsIconstraintslist,_patternsIelementss,_patternsIenvironment,_patternsIinfoTrees,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIpatternMatchWarnings,_patternsIself,_patternsIunboundNames) =
                  (patterns_ _patternsObetaUnique _patternsOimportEnvironment _patternsOmonos _patternsOnamesInScope _patternsOparentTree _patternsOpatternMatchWarnings )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Let :: T_Range  ->
                      T_Declarations  ->
                      T_Expression  ->
                      T_Expression 
sem_Expression_Let range_ declarations_ expression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _declarationsObetaUnique :: Int
              _declarationsObindingGroups :: BindingGroups
              _lhsObetaUnique :: Int
              _lhsOcollectWarnings :: Warnings
              _lhsOcollectErrors :: TypeErrors
              _declarationsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _lhsOinfoTree :: InfoTree
              _expressionOparentTree :: InfoTree
              _declarationsOparentTree :: InfoTree
              _lhsOunboundNames :: Names
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Expression
              _lhsOassumptions :: Assumptions
              _lhsObeta :: Tp
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueSecondRound :: Int
              _declarationsOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _declarationsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _declarationsOavailablePredicates :: Predicates
              _declarationsOclassEnvironment :: ClassEnvironment
              _declarationsOcollectErrors :: TypeErrors
              _declarationsOcollectWarnings :: Warnings
              _declarationsOcurrentChunk :: Int
              _declarationsOdictionaryEnvironment :: DictionaryEnvironment
              _declarationsOimportEnvironment :: ImportEnvironment
              _declarationsOinheritedBDG :: InheritedBDG
              _declarationsOmatchIO :: (IO ())
              _declarationsOmonos :: Monos
              _declarationsOnamesInScope :: Names
              _declarationsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _declarationsOpatternMatchWarnings :: ([Warning])
              _declarationsOsubstitution :: FixpointSubstitution
              _declarationsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _declarationsOuniqueChunk :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionObetaUnique :: Int
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _declarationsIbetaUnique :: Int
              _declarationsIbindingGroups :: BindingGroups
              _declarationsIcollectErrors :: TypeErrors
              _declarationsIcollectInstances :: ([(Name, Instance)])
              _declarationsIcollectWarnings :: Warnings
              _declarationsIdeclVarNames :: Names
              _declarationsIdictionaryEnvironment :: DictionaryEnvironment
              _declarationsIinfoTrees :: InfoTrees
              _declarationsImatchIO :: (IO ())
              _declarationsIpatternMatchWarnings :: ([Warning])
              _declarationsIrestrictedNames :: Names
              _declarationsIself :: Declarations
              _declarationsIsimplePatNames :: Names
              _declarationsItypeSignatures :: TypeEnvironment
              _declarationsIunboundNames :: Names
              _declarationsIuniqueChunk :: Int
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _declarationsObetaUnique =
                  _lhsIbetaUnique + 1
              _declarationsObindingGroups =
                  []
              _constraints =
                  [ (_expressionIbeta .==. _beta) _cinfoType ] .>. _cset
              _beta =
                  TVar _lhsIbetaUnique
              __tup16 =
                  let inputBDG   = (False, _lhsIcurrentChunk, _expressionIuniqueChunk, _lhsImonos, _declarationsItypeSignatures, mybdggroup, _expressionIbetaUnique)
                      mybdggroup = Just (_expressionIassumptions, [_expressionIconstraints])
                  in performBindingGroup inputBDG _declarationsIbindingGroups
              (_assumptions,_,_,_,_,_) =
                  __tup16
              (_,_cset,_,_,_,_) =
                  __tup16
              (_,_,_inheritedBDG,_,_,_) =
                  __tup16
              (_,_,_,_chunkNr,_,_) =
                  __tup16
              (_,_,_,_,_lhsObetaUnique,_) =
                  __tup16
              (_,_,_,_,_,_implicitsFM) =
                  __tup16
              _inferredTypes =
                  findInferredTypes _lhsItypeschemeMap _implicitsFM
              _lhsOcollectWarnings =
                  missingTypeSignature False _declarationsIsimplePatNames  _inferredTypes
                  ++ _expressionIcollectWarnings
              _lhsOcollectErrors =
                  restrictedNameErrors _inferredTypes _declarationsIrestrictedNames
                  ++ _declarationsIcollectErrors
              _allTypeSchemes =
                  _localTypes `M.union` _lhsIallTypeSchemes
              _localTypes =
                  makeLocalTypeEnv (_declarationsItypeSignatures `M.union` _inferredTypes) _declarationsIbindingGroups
              _declarationsOtypeSignatures =
                  M.empty
              _lhsOuniqueChunk =
                  _chunkNr
              _cinfoType =
                  resultConstraint "let expression (INTERNAL ERROR)" _thisTree
                     [ FolkloreConstraint, highlyTrusted ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _declInfo =
                  LocalInfo { self = UHA_Decls _declarationsIself
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _thisTree =
                  node _lhsIparentTree _localInfo [_declTree, _expressionIinfoTree]
              _declTree =
                  node _thisTree _declInfo _declarationsIinfoTrees
              _lhsOinfoTree =
                  _thisTree
              _expressionOparentTree =
                  _thisTree
              _declarationsOparentTree =
                  _declTree
              __tup17 =
                  internalError "PartialSyntax.ag" "n/a" "toplevel Expression"
              (_collectTypeConstructors,_,_,_,_,_) =
                  __tup17
              (_,_collectValueConstructors,_,_,_,_) =
                  __tup17
              (_,_,_collectTypeSynonyms,_,_,_) =
                  __tup17
              (_,_,_,_collectConstructorEnv,_,_) =
                  __tup17
              (_,_,_,_,_derivedFunctions,_) =
                  __tup17
              (_,_,_,_,_,_operatorFixities) =
                  __tup17
              __tup18 =
                  changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _expressionIunboundNames) _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup18
              (_,_unboundNames,_) =
                  __tup18
              (_,_,_scopeInfo) =
                  __tup18
              _lhsOunboundNames =
                  _unboundNames
              _lhsOmatches =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in matchOnlyVariable infoTuple _lhsItryPatterns
              _expressionOtryPatterns =
                  []
              _lhsOcollectInstances =
                  _declarationsIcollectInstances  ++  _expressionIcollectInstances
              _self =
                  Expression_Let _rangeIself _declarationsIself _expressionIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _assumptions
              _lhsObeta =
                  _beta
              _lhsOconstraints =
                  _constraints
              _lhsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _lhsOmatchIO =
                  _expressionImatchIO
              _lhsOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _lhsOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              _declarationsOallPatterns =
                  _lhsIallPatterns
              _declarationsOallTypeSchemes =
                  _allTypeSchemes
              _declarationsOavailablePredicates =
                  _lhsIavailablePredicates
              _declarationsOclassEnvironment =
                  _lhsIclassEnvironment
              _declarationsOcollectErrors =
                  _lhsIcollectErrors
              _declarationsOcollectWarnings =
                  _lhsIcollectWarnings
              _declarationsOcurrentChunk =
                  _lhsIcurrentChunk
              _declarationsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _declarationsOimportEnvironment =
                  _lhsIimportEnvironment
              _declarationsOinheritedBDG =
                  _inheritedBDG
              _declarationsOmatchIO =
                  _lhsImatchIO
              _declarationsOmonos =
                  _lhsImonos
              _declarationsOnamesInScope =
                  _namesInScope
              _declarationsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _declarationsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _declarationsOsubstitution =
                  _lhsIsubstitution
              _declarationsOtypeschemeMap =
                  _lhsItypeschemeMap
              _declarationsOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _allTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionObetaUnique =
                  _declarationsIbetaUnique
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _declarationsIcollectErrors
              _expressionOcollectWarnings =
                  _declarationsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _declarationsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _declarationsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOnamesInScope =
                  _namesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOpatternMatchWarnings =
                  _declarationsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _declarationsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIbetaUnique,_declarationsIbindingGroups,_declarationsIcollectErrors,_declarationsIcollectInstances,_declarationsIcollectWarnings,_declarationsIdeclVarNames,_declarationsIdictionaryEnvironment,_declarationsIinfoTrees,_declarationsImatchIO,_declarationsIpatternMatchWarnings,_declarationsIrestrictedNames,_declarationsIself,_declarationsIsimplePatNames,_declarationsItypeSignatures,_declarationsIunboundNames,_declarationsIuniqueChunk) =
                  (declarations_ _declarationsOallPatterns _declarationsOallTypeSchemes _declarationsOavailablePredicates _declarationsObetaUnique _declarationsObindingGroups _declarationsOclassEnvironment _declarationsOcollectErrors _declarationsOcollectWarnings _declarationsOcurrentChunk _declarationsOdictionaryEnvironment _declarationsOimportEnvironment _declarationsOinheritedBDG _declarationsOmatchIO _declarationsOmonos _declarationsOnamesInScope _declarationsOorderedTypeSynonyms _declarationsOparentTree _declarationsOpatternMatchWarnings _declarationsOsubstitution _declarationsOtypeSignatures _declarationsOtypeschemeMap _declarationsOuniqueChunk )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_List :: T_Range  ->
                       T_Expressions  ->
                       T_Expression 
sem_Expression_List range_ expressions_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _expressionsObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _expressionsOtryPatterns :: ([(Expressions    , [String])])
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOuniqueSecondRound :: Int
              _lhsOmatchIO :: (IO ())
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _expressionsOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionsOavailablePredicates :: Predicates
              _expressionsOclassEnvironment :: ClassEnvironment
              _expressionsOcollectErrors :: TypeErrors
              _expressionsOcollectWarnings :: Warnings
              _expressionsOcurrentChunk :: Int
              _expressionsOdictionaryEnvironment :: DictionaryEnvironment
              _expressionsOimportEnvironment :: ImportEnvironment
              _expressionsOmatchIO :: (IO ())
              _expressionsOmonos :: Monos
              _expressionsOnamesInScope :: Names
              _expressionsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionsOparentTree :: InfoTree
              _expressionsOpatternMatchWarnings :: ([Warning])
              _expressionsOsubstitution :: FixpointSubstitution
              _expressionsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionsOuniqueChunk :: Int
              _expressionsOuniqueSecondRound :: Int
              _rangeIself :: Range
              _expressionsIassumptions :: Assumptions
              _expressionsIbetaUnique :: Int
              _expressionsIbetas :: Tps
              _expressionsIcollectErrors :: TypeErrors
              _expressionsIcollectInstances :: ([(Name, Instance)])
              _expressionsIcollectWarnings :: Warnings
              _expressionsIconstraintslist :: ConstraintSets
              _expressionsIdictionaryEnvironment :: DictionaryEnvironment
              _expressionsIinfoTrees :: InfoTrees
              _expressionsImatchIO :: (IO ())
              _expressionsImatches :: ([Maybe MetaVariableTable])
              _expressionsIpatternMatchWarnings :: ([Warning])
              _expressionsIself :: Expressions
              _expressionsIunboundNames :: Names
              _expressionsIuniqueChunk :: Int
              _expressionsIuniqueSecondRound :: Int
              _expressionsObetaUnique =
                  _lhsIbetaUnique + 2
              _constraints =
                  _newcon .>.
                   Node (zipWith3 _zipf _expressionsIbetas [0..] _expressionsIconstraintslist)
              _beta =
                  TVar _lhsIbetaUnique
              _beta' =
                  TVar (_lhsIbetaUnique + 1)
              _newcon =
                  [ (listType _beta' .==. _beta) _cinfoResult ]
              _zipf =
                  \tp childNr ctree -> [ (tp .==. _beta') (_cinfoElem childNr) ] .<. ctree
              _cinfoElem =
                  \elemNr ->
                  childConstraint elemNr "element of list" _parentTree $
                     [ HasTrustFactor 10.0 | length _expressionsIbetas < 2 ] ++
                     [ Unifier (head (ftv _beta')) ("list", _localInfo, ordinal False (elemNr+1) ++ " element") ]
              _cinfoResult =
                  resultConstraint "list" _parentTree
                  [ FolkloreConstraint ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo (_expressionsIinfoTrees)
              _lhsOinfoTree =
                  _parentTree
              __tup19 =
                  let infoTuple = metaVarInfo _constraints _expressionsIassumptions _localInfo
                  in match1 infoTuple _expressionsIuniqueSecondRound
                            match_Expression_List
                            _lhsItryPatterns _lhsIallPatterns
                            [_expressionsImatches]
              (_expressionsOtryPatterns,_,_,_,_,_) =
                  __tup19
              (_,_lhsOmatches,_,_,_,_) =
                  __tup19
              (_,_,_lhsOconstraints,_,_,_) =
                  __tup19
              (_,_,_,_lhsOassumptions,_,_) =
                  __tup19
              (_,_,_,_,_lhsOuniqueSecondRound,_) =
                  __tup19
              (_,_,_,_,_,_ioMatch) =
                  __tup19
              _lhsOmatchIO =
                  _expressionsImatchIO     >> _ioMatch
              _lhsOcollectInstances =
                  _expressionsIcollectInstances
              _lhsOunboundNames =
                  _expressionsIunboundNames
              _self =
                  Expression_List _rangeIself _expressionsIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _expressionsIbetaUnique
              _lhsOcollectErrors =
                  _expressionsIcollectErrors
              _lhsOcollectWarnings =
                  _expressionsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _expressionsIdictionaryEnvironment
              _lhsOpatternMatchWarnings =
                  _expressionsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _expressionsIuniqueChunk
              _expressionsOallPatterns =
                  _lhsIallPatterns
              _expressionsOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionsOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionsOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionsOcollectErrors =
                  _lhsIcollectErrors
              _expressionsOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionsOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionsOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionsOmatchIO =
                  _lhsImatchIO
              _expressionsOmonos =
                  _lhsImonos
              _expressionsOnamesInScope =
                  _lhsInamesInScope
              _expressionsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionsOparentTree =
                  _parentTree
              _expressionsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionsOsubstitution =
                  _lhsIsubstitution
              _expressionsOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionsOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _expressionsIassumptions,_expressionsIbetaUnique,_expressionsIbetas,_expressionsIcollectErrors,_expressionsIcollectInstances,_expressionsIcollectWarnings,_expressionsIconstraintslist,_expressionsIdictionaryEnvironment,_expressionsIinfoTrees,_expressionsImatchIO,_expressionsImatches,_expressionsIpatternMatchWarnings,_expressionsIself,_expressionsIunboundNames,_expressionsIuniqueChunk,_expressionsIuniqueSecondRound) =
                  (expressions_ _expressionsOallPatterns _expressionsOallTypeSchemes _expressionsOavailablePredicates _expressionsObetaUnique _expressionsOclassEnvironment _expressionsOcollectErrors _expressionsOcollectWarnings _expressionsOcurrentChunk _expressionsOdictionaryEnvironment _expressionsOimportEnvironment _expressionsOmatchIO _expressionsOmonos _expressionsOnamesInScope _expressionsOorderedTypeSynonyms _expressionsOparentTree _expressionsOpatternMatchWarnings _expressionsOsubstitution _expressionsOtryPatterns _expressionsOtypeschemeMap _expressionsOuniqueChunk _expressionsOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Literal :: T_Range  ->
                          T_Literal  ->
                          T_Expression 
sem_Expression_Literal range_ literal_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOuniqueSecondRound :: Int
              _lhsOmatchIO :: (IO ())
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsObeta :: Tp
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _rangeIself :: Range
              _literalIelements :: (  [PatternElement]        )
              _literalIliteralType :: Tp
              _literalIself :: Literal
              _lhsObetaUnique =
                  _lhsIbetaUnique + 1
              _assumptions =
                  noAssumptions
              _constraints =
                  unitTree ((_literalIliteralType .==. _beta) _cinfo)
              _beta =
                  TVar _lhsIbetaUnique
              _cinfo =
                  resultConstraint "literal" _parentTree
                     [ FolkloreConstraint, HasTrustFactor 10.0 ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo []
              _lhsOinfoTree =
                  _parentTree
              __tup20 =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in match0 infoTuple _lhsIuniqueSecondRound
                            (match_Expression_Literal _literalIself)
                            _lhsItryPatterns _lhsIallPatterns
                            []
              (__tup21,_,_,_,_,_) =
                  __tup20
              (_,_lhsOmatches,_,_,_,_) =
                  __tup20
              (_,_,_lhsOconstraints,_,_,_) =
                  __tup20
              (_,_,_,_lhsOassumptions,_,_) =
                  __tup20
              (_,_,_,_,_lhsOuniqueSecondRound,_) =
                  __tup20
              (_,_,_,_,_,_ioMatch) =
                  __tup20
              _lhsOmatchIO =
                  _lhsImatchIO             >> _ioMatch
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Expression_Literal _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _literalIelements,_literalIliteralType,_literalIself) =
                  (literal_ )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Negate :: T_Range  ->
                         T_Expression  ->
                         T_Expression 
sem_Expression_Negate range_ expression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _expressionObetaUnique :: Int
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOinfoTree :: InfoTree
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOuniqueSecondRound :: Int
              _lhsOmatchIO :: (IO ())
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _expressionObetaUnique =
                  _lhsIbetaUnique + 1
              _constraints =
                  _newcon .>. Node [ _expressionIconstraints ]
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  let standard = makeScheme [] [Predicate "Num" (TVar 0)] (TVar 0 .->. TVar 0)
                      tpscheme = M.findWithDefault standard (nameFromString "negate") (typeEnvironment _lhsIimportEnvironment)
                  in [ (_expressionIbeta .->. _beta .::. tpscheme) _cinfo]
              _lhsOdictionaryEnvironment =
                  _newDEnv
              _localName =
                  setNameRange intUnaryMinusName _rangeIself
              _negateTypeScheme =
                  case M.lookup _localName (typeEnvironment _lhsIimportEnvironment) of
                     Just scheme -> scheme
                     Nothing     -> internalError "TypeInferenceOverloading.ag" "n/a" "type of negate unknown"
              _requiredDictionaries =
                  getRequiredDictionaries
                     (getOrderedTypeSynonyms _lhsIimportEnvironment)
                     (_lhsIsubstitution |-> _usedAsType)
                     (_lhsIsubstitution |-> _negateTypeScheme)
              _usedAsType =
                  _lhsIsubstitution |-> (_expressionIbeta .->. _beta)
              _newDEnv =
                  resolveOverloading (_lhsIclassEnvironment)  _localName
                                     (_lhsIsubstitution |-> _lhsIavailablePredicates)
                                     (_lhsIsubstitution |-> _requiredDictionaries)
                                     _expressionIdictionaryEnvironment
              _cinfo =
                  specialConstraint "negation" _parentTree
                     (self _localInfo, Just $ nameToUHA_Expr (Name_Operator _rangeIself [] "-"))
                     []
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo [_expressionIinfoTree]
              _lhsOinfoTree =
                  _parentTree
              __tup22 =
                  let infoTuple = metaVarInfo _constraints _expressionIassumptions _localInfo
                  in match1 infoTuple _expressionIuniqueSecondRound
                            match_Expression_Negate
                            _lhsItryPatterns _lhsIallPatterns
                            [_expressionImatches]
              (_expressionOtryPatterns,_,_,_,_,_) =
                  __tup22
              (_,_lhsOmatches,_,_,_,_) =
                  __tup22
              (_,_,_lhsOconstraints,_,_,_) =
                  __tup22
              (_,_,_,_lhsOassumptions,_,_) =
                  __tup22
              (_,_,_,_,_lhsOuniqueSecondRound,_) =
                  __tup22
              (_,_,_,_,_,_ioMatch) =
                  __tup22
              _lhsOmatchIO =
                  _expressionImatchIO      >> _ioMatch
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  Expression_Negate _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _expressionIbetaUnique
              _lhsOcollectErrors =
                  _expressionIcollectErrors
              _lhsOcollectWarnings =
                  _expressionIcollectWarnings
              _lhsOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _expressionIuniqueChunk
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _parentTree
              _expressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_NegateFloat :: T_Range  ->
                              T_Expression  ->
                              T_Expression 
sem_Expression_NegateFloat range_ expression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _expressionObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOuniqueSecondRound :: Int
              _lhsOmatchIO :: (IO ())
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _expressionObetaUnique =
                  _lhsIbetaUnique + 1
              _constraints =
                  _newcon .>. Node [ _expressionIconstraints ]
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  [ (floatType .->. floatType .==. _expressionIbeta .->. _beta) _cinfo]
              _cinfo =
                  specialConstraint "negation" _parentTree
                     (self _localInfo, Just $ nameToUHA_Expr (Name_Operator _rangeIself [] "-."))
                     []
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo [_expressionIinfoTree]
              _lhsOinfoTree =
                  _parentTree
              __tup23 =
                  let infoTuple = metaVarInfo _constraints _expressionIassumptions _localInfo
                  in match1 infoTuple _expressionIuniqueSecondRound
                            match_Expression_NegateFloat
                            _lhsItryPatterns _lhsIallPatterns
                            [_expressionImatches]
              (_expressionOtryPatterns,_,_,_,_,_) =
                  __tup23
              (_,_lhsOmatches,_,_,_,_) =
                  __tup23
              (_,_,_lhsOconstraints,_,_,_) =
                  __tup23
              (_,_,_,_lhsOassumptions,_,_) =
                  __tup23
              (_,_,_,_,_lhsOuniqueSecondRound,_) =
                  __tup23
              (_,_,_,_,_,_ioMatch) =
                  __tup23
              _lhsOmatchIO =
                  _expressionImatchIO      >> _ioMatch
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  Expression_NegateFloat _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _expressionIbetaUnique
              _lhsOcollectErrors =
                  _expressionIcollectErrors
              _lhsOcollectWarnings =
                  _expressionIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _lhsOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _expressionIuniqueChunk
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _parentTree
              _expressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_NormalApplication :: T_Range  ->
                                    T_Expression  ->
                                    T_Expressions  ->
                                    T_Expression 
sem_Expression_NormalApplication range_ function_ arguments_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _functionObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              __tup25 :: (([(Expression     , [String])],[(Expressions    , [String])]))
              _functionOtryPatterns :: ([(Expression     , [String])])
              _argumentsOtryPatterns :: ([(Expressions    , [String])])
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOuniqueSecondRound :: Int
              _lhsOmatchIO :: (IO ())
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _functionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _functionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _functionOavailablePredicates :: Predicates
              _functionOclassEnvironment :: ClassEnvironment
              _functionOcollectErrors :: TypeErrors
              _functionOcollectWarnings :: Warnings
              _functionOcurrentChunk :: Int
              _functionOdictionaryEnvironment :: DictionaryEnvironment
              _functionOimportEnvironment :: ImportEnvironment
              _functionOmatchIO :: (IO ())
              _functionOmonos :: Monos
              _functionOnamesInScope :: Names
              _functionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _functionOparentTree :: InfoTree
              _functionOpatternMatchWarnings :: ([Warning])
              _functionOsubstitution :: FixpointSubstitution
              _functionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _functionOuniqueChunk :: Int
              _functionOuniqueSecondRound :: Int
              _argumentsOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _argumentsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _argumentsOavailablePredicates :: Predicates
              _argumentsObetaUnique :: Int
              _argumentsOclassEnvironment :: ClassEnvironment
              _argumentsOcollectErrors :: TypeErrors
              _argumentsOcollectWarnings :: Warnings
              _argumentsOcurrentChunk :: Int
              _argumentsOdictionaryEnvironment :: DictionaryEnvironment
              _argumentsOimportEnvironment :: ImportEnvironment
              _argumentsOmatchIO :: (IO ())
              _argumentsOmonos :: Monos
              _argumentsOnamesInScope :: Names
              _argumentsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _argumentsOparentTree :: InfoTree
              _argumentsOpatternMatchWarnings :: ([Warning])
              _argumentsOsubstitution :: FixpointSubstitution
              _argumentsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _argumentsOuniqueChunk :: Int
              _argumentsOuniqueSecondRound :: Int
              _rangeIself :: Range
              _functionIassumptions :: Assumptions
              _functionIbeta :: Tp
              _functionIbetaUnique :: Int
              _functionIcollectErrors :: TypeErrors
              _functionIcollectInstances :: ([(Name, Instance)])
              _functionIcollectWarnings :: Warnings
              _functionIconstraints :: ConstraintSet
              _functionIdictionaryEnvironment :: DictionaryEnvironment
              _functionIinfoTree :: InfoTree
              _functionImatchIO :: (IO ())
              _functionImatches :: ([Maybe MetaVariableTable])
              _functionIpatternMatchWarnings :: ([Warning])
              _functionIself :: Expression
              _functionIunboundNames :: Names
              _functionIuniqueChunk :: Int
              _functionIuniqueSecondRound :: Int
              _argumentsIassumptions :: Assumptions
              _argumentsIbetaUnique :: Int
              _argumentsIbetas :: Tps
              _argumentsIcollectErrors :: TypeErrors
              _argumentsIcollectInstances :: ([(Name, Instance)])
              _argumentsIcollectWarnings :: Warnings
              _argumentsIconstraintslist :: ConstraintSets
              _argumentsIdictionaryEnvironment :: DictionaryEnvironment
              _argumentsIinfoTrees :: InfoTrees
              _argumentsImatchIO :: (IO ())
              _argumentsImatches :: ([Maybe MetaVariableTable])
              _argumentsIpatternMatchWarnings :: ([Warning])
              _argumentsIself :: Expressions
              _argumentsIunboundNames :: Names
              _argumentsIuniqueChunk :: Int
              _argumentsIuniqueSecondRound :: Int
              _functionObetaUnique =
                  _lhsIbetaUnique + 1
              _assumptions =
                  _functionIassumptions `combine` _argumentsIassumptions
              _constraints =
                  _newcon .>.
                  Node [ _functionIconstraints
                       , Node _argumentsIconstraintslist
                       ]
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  [ (_functionIbeta .==. foldr (.->.) _beta _argumentsIbetas) _cinfo ]
              _cinfo =
                  childConstraint 0 "application" _parentTree
                     [ ApplicationEdge False (map attribute _argumentsIinfoTrees) ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo (_functionIinfoTree : _argumentsIinfoTrees)
              _lhsOinfoTree =
                  _parentTree
              __tup24 =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in match2 infoTuple _argumentsIuniqueSecondRound
                            match_Expression_NormalApplication
                            _lhsItryPatterns _lhsIallPatterns
                            [_functionImatches, _argumentsImatches]
              (__tup25,_,_,_,_,_) =
                  __tup24
              (_functionOtryPatterns,_) =
                  __tup25
              (_,_argumentsOtryPatterns) =
                  __tup25
              (_,_lhsOmatches,_,_,_,_) =
                  __tup24
              (_,_,_lhsOconstraints,_,_,_) =
                  __tup24
              (_,_,_,_lhsOassumptions,_,_) =
                  __tup24
              (_,_,_,_,_lhsOuniqueSecondRound,_) =
                  __tup24
              (_,_,_,_,_,_ioMatch) =
                  __tup24
              _lhsOmatchIO =
                  _argumentsImatchIO       >> _ioMatch
              _lhsOcollectInstances =
                  _functionIcollectInstances  ++  _argumentsIcollectInstances
              _lhsOunboundNames =
                  _functionIunboundNames ++ _argumentsIunboundNames
              _self =
                  Expression_NormalApplication _rangeIself _functionIself _argumentsIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _argumentsIbetaUnique
              _lhsOcollectErrors =
                  _argumentsIcollectErrors
              _lhsOcollectWarnings =
                  _argumentsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _argumentsIdictionaryEnvironment
              _lhsOpatternMatchWarnings =
                  _argumentsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _argumentsIuniqueChunk
              _functionOallPatterns =
                  _lhsIallPatterns
              _functionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _functionOavailablePredicates =
                  _lhsIavailablePredicates
              _functionOclassEnvironment =
                  _lhsIclassEnvironment
              _functionOcollectErrors =
                  _lhsIcollectErrors
              _functionOcollectWarnings =
                  _lhsIcollectWarnings
              _functionOcurrentChunk =
                  _lhsIcurrentChunk
              _functionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _functionOimportEnvironment =
                  _lhsIimportEnvironment
              _functionOmatchIO =
                  _lhsImatchIO
              _functionOmonos =
                  _lhsImonos
              _functionOnamesInScope =
                  _lhsInamesInScope
              _functionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _functionOparentTree =
                  _parentTree
              _functionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _functionOsubstitution =
                  _lhsIsubstitution
              _functionOtypeschemeMap =
                  _lhsItypeschemeMap
              _functionOuniqueChunk =
                  _lhsIuniqueChunk
              _functionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _argumentsOallPatterns =
                  _lhsIallPatterns
              _argumentsOallTypeSchemes =
                  _lhsIallTypeSchemes
              _argumentsOavailablePredicates =
                  _lhsIavailablePredicates
              _argumentsObetaUnique =
                  _functionIbetaUnique
              _argumentsOclassEnvironment =
                  _lhsIclassEnvironment
              _argumentsOcollectErrors =
                  _functionIcollectErrors
              _argumentsOcollectWarnings =
                  _functionIcollectWarnings
              _argumentsOcurrentChunk =
                  _lhsIcurrentChunk
              _argumentsOdictionaryEnvironment =
                  _functionIdictionaryEnvironment
              _argumentsOimportEnvironment =
                  _lhsIimportEnvironment
              _argumentsOmatchIO =
                  _functionImatchIO
              _argumentsOmonos =
                  _lhsImonos
              _argumentsOnamesInScope =
                  _lhsInamesInScope
              _argumentsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _argumentsOparentTree =
                  _parentTree
              _argumentsOpatternMatchWarnings =
                  _functionIpatternMatchWarnings
              _argumentsOsubstitution =
                  _lhsIsubstitution
              _argumentsOtypeschemeMap =
                  _lhsItypeschemeMap
              _argumentsOuniqueChunk =
                  _functionIuniqueChunk
              _argumentsOuniqueSecondRound =
                  _functionIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _functionIassumptions,_functionIbeta,_functionIbetaUnique,_functionIcollectErrors,_functionIcollectInstances,_functionIcollectWarnings,_functionIconstraints,_functionIdictionaryEnvironment,_functionIinfoTree,_functionImatchIO,_functionImatches,_functionIpatternMatchWarnings,_functionIself,_functionIunboundNames,_functionIuniqueChunk,_functionIuniqueSecondRound) =
                  (function_ _functionOallPatterns _functionOallTypeSchemes _functionOavailablePredicates _functionObetaUnique _functionOclassEnvironment _functionOcollectErrors _functionOcollectWarnings _functionOcurrentChunk _functionOdictionaryEnvironment _functionOimportEnvironment _functionOmatchIO _functionOmonos _functionOnamesInScope _functionOorderedTypeSynonyms _functionOparentTree _functionOpatternMatchWarnings _functionOsubstitution _functionOtryPatterns _functionOtypeschemeMap _functionOuniqueChunk _functionOuniqueSecondRound )
              ( _argumentsIassumptions,_argumentsIbetaUnique,_argumentsIbetas,_argumentsIcollectErrors,_argumentsIcollectInstances,_argumentsIcollectWarnings,_argumentsIconstraintslist,_argumentsIdictionaryEnvironment,_argumentsIinfoTrees,_argumentsImatchIO,_argumentsImatches,_argumentsIpatternMatchWarnings,_argumentsIself,_argumentsIunboundNames,_argumentsIuniqueChunk,_argumentsIuniqueSecondRound) =
                  (arguments_ _argumentsOallPatterns _argumentsOallTypeSchemes _argumentsOavailablePredicates _argumentsObetaUnique _argumentsOclassEnvironment _argumentsOcollectErrors _argumentsOcollectWarnings _argumentsOcurrentChunk _argumentsOdictionaryEnvironment _argumentsOimportEnvironment _argumentsOmatchIO _argumentsOmonos _argumentsOnamesInScope _argumentsOorderedTypeSynonyms _argumentsOparentTree _argumentsOpatternMatchWarnings _argumentsOsubstitution _argumentsOtryPatterns _argumentsOtypeschemeMap _argumentsOuniqueChunk _argumentsOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Parenthesized :: T_Range  ->
                                T_Expression  ->
                                T_Expression 
sem_Expression_Parenthesized range_ expression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOassumptions :: Assumptions
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOinfoTree :: InfoTree
              _lhsOmatchIO :: (IO ())
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionObetaUnique :: Int
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  Expression_Parenthesized _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _expressionIassumptions
              _lhsObeta =
                  _expressionIbeta
              _lhsObetaUnique =
                  _expressionIbetaUnique
              _lhsOcollectErrors =
                  _expressionIcollectErrors
              _lhsOcollectWarnings =
                  _expressionIcollectWarnings
              _lhsOconstraints =
                  _expressionIconstraints
              _lhsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _lhsOinfoTree =
                  _expressionIinfoTree
              _lhsOmatchIO =
                  _expressionImatchIO
              _lhsOmatches =
                  _expressionImatches
              _lhsOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _expressionIuniqueChunk
              _lhsOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionObetaUnique =
                  _lhsIbetaUnique
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _lhsIparentTree
              _expressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtryPatterns =
                  _lhsItryPatterns
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_RecordConstruction :: T_Range  ->
                                     T_Name  ->
                                     T_RecordExpressionBindings  ->
                                     T_Expression 
sem_Expression_RecordConstruction range_ name_ recordExpressionBindings_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOassumptions :: Assumptions
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOinfoTree :: InfoTree
              _lhsOmatchIO :: (IO ())
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _recordExpressionBindingsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _recordExpressionBindingsOavailablePredicates :: Predicates
              _recordExpressionBindingsOclassEnvironment :: ClassEnvironment
              _recordExpressionBindingsOcollectErrors :: TypeErrors
              _recordExpressionBindingsOcollectWarnings :: Warnings
              _recordExpressionBindingsOcurrentChunk :: Int
              _recordExpressionBindingsOdictionaryEnvironment :: DictionaryEnvironment
              _recordExpressionBindingsOimportEnvironment :: ImportEnvironment
              _recordExpressionBindingsOnamesInScope :: Names
              _recordExpressionBindingsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _recordExpressionBindingsOpatternMatchWarnings :: ([Warning])
              _recordExpressionBindingsOsubstitution :: FixpointSubstitution
              _recordExpressionBindingsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _recordExpressionBindingsOuniqueChunk :: Int
              _rangeIself :: Range
              _nameIself :: Name
              _recordExpressionBindingsIcollectErrors :: TypeErrors
              _recordExpressionBindingsIcollectInstances :: ([(Name, Instance)])
              _recordExpressionBindingsIcollectWarnings :: Warnings
              _recordExpressionBindingsIdictionaryEnvironment :: DictionaryEnvironment
              _recordExpressionBindingsIpatternMatchWarnings :: ([Warning])
              _recordExpressionBindingsIself :: RecordExpressionBindings
              _recordExpressionBindingsIunboundNames :: Names
              _recordExpressionBindingsIuniqueChunk :: Int
              _infoTree =
                  globalInfoError
              __tup26 =
                  internalError "PartialSyntax.ag" "n/a" "Expression.RecordConstruction"
              (_assumptions,_,_) =
                  __tup26
              (_,_constraints,_) =
                  __tup26
              (_,_,_beta) =
                  __tup26
              _matches =
                  internalError "TS_PatternMatching.ag" "n/a" "RecordConstruction is not supported"
              _lhsOcollectInstances =
                  _recordExpressionBindingsIcollectInstances
              _lhsOunboundNames =
                  _recordExpressionBindingsIunboundNames
              _self =
                  Expression_RecordConstruction _rangeIself _nameIself _recordExpressionBindingsIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _assumptions
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOcollectErrors =
                  _recordExpressionBindingsIcollectErrors
              _lhsOcollectWarnings =
                  _recordExpressionBindingsIcollectWarnings
              _lhsOconstraints =
                  _constraints
              _lhsOdictionaryEnvironment =
                  _recordExpressionBindingsIdictionaryEnvironment
              _lhsOinfoTree =
                  _infoTree
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOmatches =
                  _matches
              _lhsOpatternMatchWarnings =
                  _recordExpressionBindingsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _recordExpressionBindingsIuniqueChunk
              _lhsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _recordExpressionBindingsOallTypeSchemes =
                  _lhsIallTypeSchemes
              _recordExpressionBindingsOavailablePredicates =
                  _lhsIavailablePredicates
              _recordExpressionBindingsOclassEnvironment =
                  _lhsIclassEnvironment
              _recordExpressionBindingsOcollectErrors =
                  _lhsIcollectErrors
              _recordExpressionBindingsOcollectWarnings =
                  _lhsIcollectWarnings
              _recordExpressionBindingsOcurrentChunk =
                  _lhsIcurrentChunk
              _recordExpressionBindingsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _recordExpressionBindingsOimportEnvironment =
                  _lhsIimportEnvironment
              _recordExpressionBindingsOnamesInScope =
                  _lhsInamesInScope
              _recordExpressionBindingsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _recordExpressionBindingsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _recordExpressionBindingsOsubstitution =
                  _lhsIsubstitution
              _recordExpressionBindingsOtypeschemeMap =
                  _lhsItypeschemeMap
              _recordExpressionBindingsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _recordExpressionBindingsIcollectErrors,_recordExpressionBindingsIcollectInstances,_recordExpressionBindingsIcollectWarnings,_recordExpressionBindingsIdictionaryEnvironment,_recordExpressionBindingsIpatternMatchWarnings,_recordExpressionBindingsIself,_recordExpressionBindingsIunboundNames,_recordExpressionBindingsIuniqueChunk) =
                  (recordExpressionBindings_ _recordExpressionBindingsOallTypeSchemes _recordExpressionBindingsOavailablePredicates _recordExpressionBindingsOclassEnvironment _recordExpressionBindingsOcollectErrors _recordExpressionBindingsOcollectWarnings _recordExpressionBindingsOcurrentChunk _recordExpressionBindingsOdictionaryEnvironment _recordExpressionBindingsOimportEnvironment _recordExpressionBindingsOnamesInScope _recordExpressionBindingsOorderedTypeSynonyms _recordExpressionBindingsOpatternMatchWarnings _recordExpressionBindingsOsubstitution _recordExpressionBindingsOtypeschemeMap _recordExpressionBindingsOuniqueChunk )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_RecordUpdate :: T_Range  ->
                               T_Expression  ->
                               T_RecordExpressionBindings  ->
                               T_Expression 
sem_Expression_RecordUpdate range_ expression_ recordExpressionBindings_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOassumptions :: Assumptions
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOinfoTree :: InfoTree
              _lhsOmatchIO :: (IO ())
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionObetaUnique :: Int
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _recordExpressionBindingsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _recordExpressionBindingsOavailablePredicates :: Predicates
              _recordExpressionBindingsOclassEnvironment :: ClassEnvironment
              _recordExpressionBindingsOcollectErrors :: TypeErrors
              _recordExpressionBindingsOcollectWarnings :: Warnings
              _recordExpressionBindingsOcurrentChunk :: Int
              _recordExpressionBindingsOdictionaryEnvironment :: DictionaryEnvironment
              _recordExpressionBindingsOimportEnvironment :: ImportEnvironment
              _recordExpressionBindingsOnamesInScope :: Names
              _recordExpressionBindingsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _recordExpressionBindingsOpatternMatchWarnings :: ([Warning])
              _recordExpressionBindingsOsubstitution :: FixpointSubstitution
              _recordExpressionBindingsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _recordExpressionBindingsOuniqueChunk :: Int
              _rangeIself :: Range
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _recordExpressionBindingsIcollectErrors :: TypeErrors
              _recordExpressionBindingsIcollectInstances :: ([(Name, Instance)])
              _recordExpressionBindingsIcollectWarnings :: Warnings
              _recordExpressionBindingsIdictionaryEnvironment :: DictionaryEnvironment
              _recordExpressionBindingsIpatternMatchWarnings :: ([Warning])
              _recordExpressionBindingsIself :: RecordExpressionBindings
              _recordExpressionBindingsIunboundNames :: Names
              _recordExpressionBindingsIuniqueChunk :: Int
              _lhsOcollectInstances =
                  _expressionIcollectInstances  ++  _recordExpressionBindingsIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames ++ _recordExpressionBindingsIunboundNames
              _self =
                  Expression_RecordUpdate _rangeIself _expressionIself _recordExpressionBindingsIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _expressionIassumptions
              _lhsObeta =
                  _expressionIbeta
              _lhsObetaUnique =
                  _expressionIbetaUnique
              _lhsOcollectErrors =
                  _recordExpressionBindingsIcollectErrors
              _lhsOcollectWarnings =
                  _recordExpressionBindingsIcollectWarnings
              _lhsOconstraints =
                  _expressionIconstraints
              _lhsOdictionaryEnvironment =
                  _recordExpressionBindingsIdictionaryEnvironment
              _lhsOinfoTree =
                  _expressionIinfoTree
              _lhsOmatchIO =
                  _expressionImatchIO
              _lhsOmatches =
                  _expressionImatches
              _lhsOpatternMatchWarnings =
                  _recordExpressionBindingsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _recordExpressionBindingsIuniqueChunk
              _lhsOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionObetaUnique =
                  _lhsIbetaUnique
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _lhsIparentTree
              _expressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtryPatterns =
                  _lhsItryPatterns
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _recordExpressionBindingsOallTypeSchemes =
                  _lhsIallTypeSchemes
              _recordExpressionBindingsOavailablePredicates =
                  _lhsIavailablePredicates
              _recordExpressionBindingsOclassEnvironment =
                  _lhsIclassEnvironment
              _recordExpressionBindingsOcollectErrors =
                  _expressionIcollectErrors
              _recordExpressionBindingsOcollectWarnings =
                  _expressionIcollectWarnings
              _recordExpressionBindingsOcurrentChunk =
                  _lhsIcurrentChunk
              _recordExpressionBindingsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _recordExpressionBindingsOimportEnvironment =
                  _lhsIimportEnvironment
              _recordExpressionBindingsOnamesInScope =
                  _lhsInamesInScope
              _recordExpressionBindingsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _recordExpressionBindingsOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _recordExpressionBindingsOsubstitution =
                  _lhsIsubstitution
              _recordExpressionBindingsOtypeschemeMap =
                  _lhsItypeschemeMap
              _recordExpressionBindingsOuniqueChunk =
                  _expressionIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
              ( _recordExpressionBindingsIcollectErrors,_recordExpressionBindingsIcollectInstances,_recordExpressionBindingsIcollectWarnings,_recordExpressionBindingsIdictionaryEnvironment,_recordExpressionBindingsIpatternMatchWarnings,_recordExpressionBindingsIself,_recordExpressionBindingsIunboundNames,_recordExpressionBindingsIuniqueChunk) =
                  (recordExpressionBindings_ _recordExpressionBindingsOallTypeSchemes _recordExpressionBindingsOavailablePredicates _recordExpressionBindingsOclassEnvironment _recordExpressionBindingsOcollectErrors _recordExpressionBindingsOcollectWarnings _recordExpressionBindingsOcurrentChunk _recordExpressionBindingsOdictionaryEnvironment _recordExpressionBindingsOimportEnvironment _recordExpressionBindingsOnamesInScope _recordExpressionBindingsOorderedTypeSynonyms _recordExpressionBindingsOpatternMatchWarnings _recordExpressionBindingsOsubstitution _recordExpressionBindingsOtypeschemeMap _recordExpressionBindingsOuniqueChunk )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Tuple :: T_Range  ->
                        T_Expressions  ->
                        T_Expression 
sem_Expression_Tuple range_ expressions_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _expressionsObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _expressionsOtryPatterns :: ([(Expressions    , [String])])
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOuniqueSecondRound :: Int
              _lhsOmatchIO :: (IO ())
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _expressionsOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionsOavailablePredicates :: Predicates
              _expressionsOclassEnvironment :: ClassEnvironment
              _expressionsOcollectErrors :: TypeErrors
              _expressionsOcollectWarnings :: Warnings
              _expressionsOcurrentChunk :: Int
              _expressionsOdictionaryEnvironment :: DictionaryEnvironment
              _expressionsOimportEnvironment :: ImportEnvironment
              _expressionsOmatchIO :: (IO ())
              _expressionsOmonos :: Monos
              _expressionsOnamesInScope :: Names
              _expressionsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionsOparentTree :: InfoTree
              _expressionsOpatternMatchWarnings :: ([Warning])
              _expressionsOsubstitution :: FixpointSubstitution
              _expressionsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionsOuniqueChunk :: Int
              _expressionsOuniqueSecondRound :: Int
              _rangeIself :: Range
              _expressionsIassumptions :: Assumptions
              _expressionsIbetaUnique :: Int
              _expressionsIbetas :: Tps
              _expressionsIcollectErrors :: TypeErrors
              _expressionsIcollectInstances :: ([(Name, Instance)])
              _expressionsIcollectWarnings :: Warnings
              _expressionsIconstraintslist :: ConstraintSets
              _expressionsIdictionaryEnvironment :: DictionaryEnvironment
              _expressionsIinfoTrees :: InfoTrees
              _expressionsImatchIO :: (IO ())
              _expressionsImatches :: ([Maybe MetaVariableTable])
              _expressionsIpatternMatchWarnings :: ([Warning])
              _expressionsIself :: Expressions
              _expressionsIunboundNames :: Names
              _expressionsIuniqueChunk :: Int
              _expressionsIuniqueSecondRound :: Int
              _expressionsObetaUnique =
                  _lhsIbetaUnique + 1
              _constraints =
                  _newcon .>. Node _expressionsIconstraintslist
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  [ (tupleType _expressionsIbetas .==. _beta) _cinfo ]
              _cinfo =
                  resultConstraint "tuple" _parentTree
                     [ FolkloreConstraint ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo (_expressionsIinfoTrees)
              _lhsOinfoTree =
                  _parentTree
              __tup27 =
                  let infoTuple = metaVarInfo _constraints _expressionsIassumptions _localInfo
                  in match1 infoTuple _expressionsIuniqueSecondRound
                            match_Expression_Tuple
                            _lhsItryPatterns _lhsIallPatterns
                            [_expressionsImatches]
              (_expressionsOtryPatterns,_,_,_,_,_) =
                  __tup27
              (_,_lhsOmatches,_,_,_,_) =
                  __tup27
              (_,_,_lhsOconstraints,_,_,_) =
                  __tup27
              (_,_,_,_lhsOassumptions,_,_) =
                  __tup27
              (_,_,_,_,_lhsOuniqueSecondRound,_) =
                  __tup27
              (_,_,_,_,_,_ioMatch) =
                  __tup27
              _lhsOmatchIO =
                  _expressionsImatchIO     >> _ioMatch
              _lhsOcollectInstances =
                  _expressionsIcollectInstances
              _lhsOunboundNames =
                  _expressionsIunboundNames
              _self =
                  Expression_Tuple _rangeIself _expressionsIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _expressionsIbetaUnique
              _lhsOcollectErrors =
                  _expressionsIcollectErrors
              _lhsOcollectWarnings =
                  _expressionsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _expressionsIdictionaryEnvironment
              _lhsOpatternMatchWarnings =
                  _expressionsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _expressionsIuniqueChunk
              _expressionsOallPatterns =
                  _lhsIallPatterns
              _expressionsOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionsOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionsOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionsOcollectErrors =
                  _lhsIcollectErrors
              _expressionsOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionsOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionsOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionsOmatchIO =
                  _lhsImatchIO
              _expressionsOmonos =
                  _lhsImonos
              _expressionsOnamesInScope =
                  _lhsInamesInScope
              _expressionsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionsOparentTree =
                  _parentTree
              _expressionsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionsOsubstitution =
                  _lhsIsubstitution
              _expressionsOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionsOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _expressionsIassumptions,_expressionsIbetaUnique,_expressionsIbetas,_expressionsIcollectErrors,_expressionsIcollectInstances,_expressionsIcollectWarnings,_expressionsIconstraintslist,_expressionsIdictionaryEnvironment,_expressionsIinfoTrees,_expressionsImatchIO,_expressionsImatches,_expressionsIpatternMatchWarnings,_expressionsIself,_expressionsIunboundNames,_expressionsIuniqueChunk,_expressionsIuniqueSecondRound) =
                  (expressions_ _expressionsOallPatterns _expressionsOallTypeSchemes _expressionsOavailablePredicates _expressionsObetaUnique _expressionsOclassEnvironment _expressionsOcollectErrors _expressionsOcollectWarnings _expressionsOcurrentChunk _expressionsOdictionaryEnvironment _expressionsOimportEnvironment _expressionsOmatchIO _expressionsOmonos _expressionsOnamesInScope _expressionsOorderedTypeSynonyms _expressionsOparentTree _expressionsOpatternMatchWarnings _expressionsOsubstitution _expressionsOtryPatterns _expressionsOtypeschemeMap _expressionsOuniqueChunk _expressionsOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Typed :: T_Range  ->
                        T_Expression  ->
                        T_Type  ->
                        T_Expression 
sem_Expression_Typed range_ expression_ type_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _expressionObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOassumptions :: Assumptions
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _typeIself :: Type
              _expressionObetaUnique =
                  _lhsIbetaUnique + 1
              _assumptions =
                  _expressionIassumptions
              _constraints =
                  _conResult .>.
                  Node [ _conExpr .<. _expressionIconstraints ]
              _beta =
                  TVar _lhsIbetaUnique
              _typeScheme =
                  makeTpSchemeFromType _typeIself
              _conResult =
                  [ (_beta            .::. _typeScheme) _cinfoResult          ]
              _conExpr =
                  [ (_expressionIbeta !::! _typeScheme) _lhsImonos _cinfoExpr ]
              _cinfoExpr =
                  childConstraint 0 "type annotation" _parentTree
                     [ TypeSignatureLocation (getTypeRange _typeIself) ]
              _cinfoResult =
                  resultConstraint "type annotation" _parentTree
                     [ FolkloreConstraint ]
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo [_expressionIinfoTree]
              _lhsOinfoTree =
                  _parentTree
              _lhsOmatches =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in matchOnlyVariable infoTuple _lhsItryPatterns
              _expressionOtryPatterns =
                  []
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  Expression_Typed _rangeIself _expressionIself _typeIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _assumptions
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _expressionIbetaUnique
              _lhsOcollectErrors =
                  _expressionIcollectErrors
              _lhsOcollectWarnings =
                  _expressionIcollectWarnings
              _lhsOconstraints =
                  _constraints
              _lhsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _lhsOmatchIO =
                  _expressionImatchIO
              _lhsOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _expressionIuniqueChunk
              _lhsOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _parentTree
              _expressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
              ( _typeIself) =
                  (type_ )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expression_Variable :: T_Range  ->
                           T_Name  ->
                           T_Expression 
sem_Expression_Variable range_ name_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsObetaUnique :: Int
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOinfoTree :: InfoTree
              _lhsOunboundNames :: Names
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOuniqueSecondRound :: Int
              _lhsOmatchIO :: (IO ())
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Expression
              _lhsObeta :: Tp
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _rangeIself :: Range
              _nameIself :: Name
              _lhsObetaUnique =
                  _lhsIbetaUnique + 1
              _assumptions =
                  _nameIself `single` _beta
              _constraints =
                  Node [ Receive _lhsIbetaUnique ]
              _beta =
                  TVar _lhsIbetaUnique
              _lhsOdictionaryEnvironment =
                  _newDEnv
              _nameInScope =
                  case filter (_nameIself==) _lhsInamesInScope of
                     [name] -> NameWithRange name
                     _      -> internalError "TypeInferenceOverloading.ag" "n/a" "name not in scope"
              _maybeInferredType =
                  M.lookup _nameInScope _lhsIallTypeSchemes
              _requiredDictionaries =
                  case _maybeInferredType of
                     Nothing     -> []
                     Just scheme -> getRequiredDictionaries
                                       (getOrderedTypeSynonyms _lhsIimportEnvironment)
                                       (_lhsIsubstitution |-> _usedAsType)
                                       (_lhsIsubstitution |-> scheme)
              _newDEnv =
                  resolveOverloading (_lhsIclassEnvironment)
                                     _nameIself
                                     (_lhsIsubstitution |-> _lhsIavailablePredicates)
                                     (_lhsIsubstitution |-> _requiredDictionaries)
                                     _lhsIdictionaryEnvironment
              _usedAsType =
                  _lhsIsubstitution |-> _beta
              _localInfo =
                  LocalInfo { self = UHA_Expr _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo []
              _lhsOinfoTree =
                  _parentTree
              _lhsOunboundNames =
                  [ _nameIself ]
              __tup28 =
                  let infoTuple = metaVarInfo _constraints _assumptions _localInfo
                  in match0 infoTuple _lhsIuniqueSecondRound
                            (match_Expression_Variable _nameIself)
                            _lhsItryPatterns _lhsIallPatterns
                            []
              (__tup29,_,_,_,_,_) =
                  __tup28
              (_,_lhsOmatches,_,_,_,_) =
                  __tup28
              (_,_,_lhsOconstraints,_,_,_) =
                  __tup28
              (_,_,_,_lhsOassumptions,_,_) =
                  __tup28
              (_,_,_,_,_lhsOuniqueSecondRound,_) =
                  __tup28
              (_,_,_,_,_,_ioMatch) =
                  __tup28
              _lhsOmatchIO =
                  _lhsImatchIO             >> _ioMatch
              _lhsOcollectInstances =
                  []
              _self =
                  Expression_Variable _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
-- Expressions -------------------------------------------------
-- cata
sem_Expressions :: Expressions  ->
                   T_Expressions 
sem_Expressions list  =
    (Prelude.foldr sem_Expressions_Cons sem_Expressions_Nil (Prelude.map sem_Expression list) )
-- semantic domain
type T_Expressions  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                      (M.Map NameWithRange TpScheme) ->
                      Predicates ->
                      Int ->
                      ClassEnvironment ->
                      TypeErrors ->
                      Warnings ->
                      Int ->
                      DictionaryEnvironment ->
                      ImportEnvironment ->
                      (IO ()) ->
                      Monos ->
                      Names ->
                      OrderedTypeSynonyms ->
                      InfoTree ->
                      ([Warning]) ->
                      FixpointSubstitution ->
                      ([(Expressions    , [String])]) ->
                      (M.Map Int (Scheme Predicates)) ->
                      Int ->
                      Int ->
                      ( Assumptions,Int,Tps,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSets,DictionaryEnvironment,InfoTrees,(IO ()),([Maybe MetaVariableTable]),([Warning]),Expressions,Names,Int,Int)
sem_Expressions_Cons :: T_Expression  ->
                        T_Expressions  ->
                        T_Expressions 
sem_Expressions_Cons hd_ tl_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsObetas :: Tps
              _lhsOassumptions :: Assumptions
              _lhsOconstraintslist :: ConstraintSets
              _lhsOinfoTrees :: InfoTrees
              __tup31 :: (([(Expression     , [String])],[(Expressions    , [String])]))
              _hdOtryPatterns :: ([(Expression     , [String])])
              _tlOtryPatterns :: ([(Expressions    , [String])])
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expressions
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _hdOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _hdOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _hdOavailablePredicates :: Predicates
              _hdObetaUnique :: Int
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectErrors :: TypeErrors
              _hdOcollectWarnings :: Warnings
              _hdOcurrentChunk :: Int
              _hdOdictionaryEnvironment :: DictionaryEnvironment
              _hdOimportEnvironment :: ImportEnvironment
              _hdOmatchIO :: (IO ())
              _hdOmonos :: Monos
              _hdOnamesInScope :: Names
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOparentTree :: InfoTree
              _hdOpatternMatchWarnings :: ([Warning])
              _hdOsubstitution :: FixpointSubstitution
              _hdOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _hdOuniqueChunk :: Int
              _hdOuniqueSecondRound :: Int
              _tlOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _tlOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _tlOavailablePredicates :: Predicates
              _tlObetaUnique :: Int
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectErrors :: TypeErrors
              _tlOcollectWarnings :: Warnings
              _tlOcurrentChunk :: Int
              _tlOdictionaryEnvironment :: DictionaryEnvironment
              _tlOimportEnvironment :: ImportEnvironment
              _tlOmatchIO :: (IO ())
              _tlOmonos :: Monos
              _tlOnamesInScope :: Names
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOparentTree :: InfoTree
              _tlOpatternMatchWarnings :: ([Warning])
              _tlOsubstitution :: FixpointSubstitution
              _tlOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _tlOuniqueChunk :: Int
              _tlOuniqueSecondRound :: Int
              _hdIassumptions :: Assumptions
              _hdIbeta :: Tp
              _hdIbetaUnique :: Int
              _hdIcollectErrors :: TypeErrors
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectWarnings :: Warnings
              _hdIconstraints :: ConstraintSet
              _hdIdictionaryEnvironment :: DictionaryEnvironment
              _hdIinfoTree :: InfoTree
              _hdImatchIO :: (IO ())
              _hdImatches :: ([Maybe MetaVariableTable])
              _hdIpatternMatchWarnings :: ([Warning])
              _hdIself :: Expression
              _hdIunboundNames :: Names
              _hdIuniqueChunk :: Int
              _hdIuniqueSecondRound :: Int
              _tlIassumptions :: Assumptions
              _tlIbetaUnique :: Int
              _tlIbetas :: Tps
              _tlIcollectErrors :: TypeErrors
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectWarnings :: Warnings
              _tlIconstraintslist :: ConstraintSets
              _tlIdictionaryEnvironment :: DictionaryEnvironment
              _tlIinfoTrees :: InfoTrees
              _tlImatchIO :: (IO ())
              _tlImatches :: ([Maybe MetaVariableTable])
              _tlIpatternMatchWarnings :: ([Warning])
              _tlIself :: Expressions
              _tlIunboundNames :: Names
              _tlIuniqueChunk :: Int
              _tlIuniqueSecondRound :: Int
              _lhsObetas =
                  _hdIbeta : _tlIbetas
              _lhsOassumptions =
                  _hdIassumptions `combine` _tlIassumptions
              _lhsOconstraintslist =
                  _hdIconstraints : _tlIconstraintslist
              _lhsOinfoTrees =
                  _hdIinfoTree : _tlIinfoTrees
              __tup30 =
                  match2' match_Expressions_Cons _lhsItryPatterns [] [_hdImatches, _tlImatches]
              (__tup31,_,_,_,_,_) =
                  __tup30
              (_hdOtryPatterns,_) =
                  __tup31
              (_,_tlOtryPatterns) =
                  __tup31
              (_,_lhsOmatches,_,_,_,_) =
                  __tup30
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _tlIbetaUnique
              _lhsOcollectErrors =
                  _tlIcollectErrors
              _lhsOcollectWarnings =
                  _tlIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _tlIdictionaryEnvironment
              _lhsOmatchIO =
                  _tlImatchIO
              _lhsOpatternMatchWarnings =
                  _tlIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _tlIuniqueChunk
              _lhsOuniqueSecondRound =
                  _tlIuniqueSecondRound
              _hdOallPatterns =
                  _lhsIallPatterns
              _hdOallTypeSchemes =
                  _lhsIallTypeSchemes
              _hdOavailablePredicates =
                  _lhsIavailablePredicates
              _hdObetaUnique =
                  _lhsIbetaUnique
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectErrors =
                  _lhsIcollectErrors
              _hdOcollectWarnings =
                  _lhsIcollectWarnings
              _hdOcurrentChunk =
                  _lhsIcurrentChunk
              _hdOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _hdOimportEnvironment =
                  _lhsIimportEnvironment
              _hdOmatchIO =
                  _lhsImatchIO
              _hdOmonos =
                  _lhsImonos
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOparentTree =
                  _lhsIparentTree
              _hdOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _hdOsubstitution =
                  _lhsIsubstitution
              _hdOtypeschemeMap =
                  _lhsItypeschemeMap
              _hdOuniqueChunk =
                  _lhsIuniqueChunk
              _hdOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _tlOallPatterns =
                  _lhsIallPatterns
              _tlOallTypeSchemes =
                  _lhsIallTypeSchemes
              _tlOavailablePredicates =
                  _lhsIavailablePredicates
              _tlObetaUnique =
                  _hdIbetaUnique
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectErrors =
                  _hdIcollectErrors
              _tlOcollectWarnings =
                  _hdIcollectWarnings
              _tlOcurrentChunk =
                  _lhsIcurrentChunk
              _tlOdictionaryEnvironment =
                  _hdIdictionaryEnvironment
              _tlOimportEnvironment =
                  _lhsIimportEnvironment
              _tlOmatchIO =
                  _hdImatchIO
              _tlOmonos =
                  _lhsImonos
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOparentTree =
                  _lhsIparentTree
              _tlOpatternMatchWarnings =
                  _hdIpatternMatchWarnings
              _tlOsubstitution =
                  _lhsIsubstitution
              _tlOtypeschemeMap =
                  _lhsItypeschemeMap
              _tlOuniqueChunk =
                  _hdIuniqueChunk
              _tlOuniqueSecondRound =
                  _hdIuniqueSecondRound
              ( _hdIassumptions,_hdIbeta,_hdIbetaUnique,_hdIcollectErrors,_hdIcollectInstances,_hdIcollectWarnings,_hdIconstraints,_hdIdictionaryEnvironment,_hdIinfoTree,_hdImatchIO,_hdImatches,_hdIpatternMatchWarnings,_hdIself,_hdIunboundNames,_hdIuniqueChunk,_hdIuniqueSecondRound) =
                  (hd_ _hdOallPatterns _hdOallTypeSchemes _hdOavailablePredicates _hdObetaUnique _hdOclassEnvironment _hdOcollectErrors _hdOcollectWarnings _hdOcurrentChunk _hdOdictionaryEnvironment _hdOimportEnvironment _hdOmatchIO _hdOmonos _hdOnamesInScope _hdOorderedTypeSynonyms _hdOparentTree _hdOpatternMatchWarnings _hdOsubstitution _hdOtryPatterns _hdOtypeschemeMap _hdOuniqueChunk _hdOuniqueSecondRound )
              ( _tlIassumptions,_tlIbetaUnique,_tlIbetas,_tlIcollectErrors,_tlIcollectInstances,_tlIcollectWarnings,_tlIconstraintslist,_tlIdictionaryEnvironment,_tlIinfoTrees,_tlImatchIO,_tlImatches,_tlIpatternMatchWarnings,_tlIself,_tlIunboundNames,_tlIuniqueChunk,_tlIuniqueSecondRound) =
                  (tl_ _tlOallPatterns _tlOallTypeSchemes _tlOavailablePredicates _tlObetaUnique _tlOclassEnvironment _tlOcollectErrors _tlOcollectWarnings _tlOcurrentChunk _tlOdictionaryEnvironment _tlOimportEnvironment _tlOmatchIO _tlOmonos _tlOnamesInScope _tlOorderedTypeSynonyms _tlOparentTree _tlOpatternMatchWarnings _tlOsubstitution _tlOtryPatterns _tlOtypeschemeMap _tlOuniqueChunk _tlOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsObetas,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraintslist,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Expressions_Nil :: T_Expressions 
sem_Expressions_Nil  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsObetas :: Tps
              _lhsOassumptions :: Assumptions
              _lhsOconstraintslist :: ConstraintSets
              _lhsOinfoTrees :: InfoTrees
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expressions
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _lhsObetas =
                  []
              _lhsOassumptions =
                  noAssumptions
              _lhsOconstraintslist =
                  []
              _lhsOinfoTrees =
                  []
              __tup32 =
                  match0' match_Expressions_Nil _lhsItryPatterns [] []
              (__tup33,_,_,_,_,_) =
                  __tup32
              (_,_lhsOmatches,_,_,_,_) =
                  __tup32
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              _lhsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsObetas,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraintslist,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
-- FieldDeclaration --------------------------------------------
-- cata
sem_FieldDeclaration :: FieldDeclaration  ->
                        T_FieldDeclaration 
sem_FieldDeclaration (FieldDeclaration_FieldDeclaration _range _names _type )  =
    (sem_FieldDeclaration_FieldDeclaration (sem_Range _range ) (sem_Names _names ) (sem_AnnotatedType _type ) )
-- semantic domain
type T_FieldDeclaration  = Names ->
                           ( FieldDeclaration,Names)
sem_FieldDeclaration_FieldDeclaration :: T_Range  ->
                                         T_Names  ->
                                         T_AnnotatedType  ->
                                         T_FieldDeclaration 
sem_FieldDeclaration_FieldDeclaration range_ names_ type_  =
    (\ _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: FieldDeclaration
              _typeOnamesInScope :: Names
              _rangeIself :: Range
              _namesIself :: Names
              _typeIself :: AnnotatedType
              _typeIunboundNames :: Names
              __tup34 =
                  internalError "PartialSyntax.ag" "n/a" "FieldDeclaration.FieldDeclaration"
              (_kindErrors,_,_,_,_,_,_,_,_) =
                  __tup34
              (_,_tyconEnv,_,_,_,_,_,_,_) =
                  __tup34
              (_,_,_constructorenv,_,_,_,_,_,_) =
                  __tup34
              (_,_,_,_importEnvironment,_,_,_,_,_) =
                  __tup34
              (_,_,_,_,_valueConstructors,_,_,_,_) =
                  __tup34
              (_,_,_,_,_,_allValueConstructors,_,_,_) =
                  __tup34
              (_,_,_,_,_,_,_typeConstructors,_,_) =
                  __tup34
              (_,_,_,_,_,_,_,_allTypeConstructors,_) =
                  __tup34
              (_,_,_,_,_,_,_,_,_warnings) =
                  __tup34
              _lhsOunboundNames =
                  _typeIunboundNames
              _self =
                  FieldDeclaration_FieldDeclaration _rangeIself _namesIself _typeIself
              _lhsOself =
                  _self
              _typeOnamesInScope =
                  _lhsInamesInScope
              ( _rangeIself) =
                  (range_ )
              ( _namesIself) =
                  (names_ )
              ( _typeIself,_typeIunboundNames) =
                  (type_ _typeOnamesInScope )
          in  ( _lhsOself,_lhsOunboundNames)))
-- FieldDeclarations -------------------------------------------
-- cata
sem_FieldDeclarations :: FieldDeclarations  ->
                         T_FieldDeclarations 
sem_FieldDeclarations list  =
    (Prelude.foldr sem_FieldDeclarations_Cons sem_FieldDeclarations_Nil (Prelude.map sem_FieldDeclaration list) )
-- semantic domain
type T_FieldDeclarations  = Names ->
                            ( FieldDeclarations,Names)
sem_FieldDeclarations_Cons :: T_FieldDeclaration  ->
                              T_FieldDeclarations  ->
                              T_FieldDeclarations 
sem_FieldDeclarations_Cons hd_ tl_  =
    (\ _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: FieldDeclarations
              _hdOnamesInScope :: Names
              _tlOnamesInScope :: Names
              _hdIself :: FieldDeclaration
              _hdIunboundNames :: Names
              _tlIself :: FieldDeclarations
              _tlIunboundNames :: Names
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOnamesInScope =
                  _lhsInamesInScope
              _tlOnamesInScope =
                  _lhsInamesInScope
              ( _hdIself,_hdIunboundNames) =
                  (hd_ _hdOnamesInScope )
              ( _tlIself,_tlIunboundNames) =
                  (tl_ _tlOnamesInScope )
          in  ( _lhsOself,_lhsOunboundNames)))
sem_FieldDeclarations_Nil :: T_FieldDeclarations 
sem_FieldDeclarations_Nil  =
    (\ _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: FieldDeclarations
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOself,_lhsOunboundNames)))
-- Fixity ------------------------------------------------------
-- cata
sem_Fixity :: Fixity  ->
              T_Fixity 
sem_Fixity (Fixity_Infix _range )  =
    (sem_Fixity_Infix (sem_Range _range ) )
sem_Fixity (Fixity_Infixl _range )  =
    (sem_Fixity_Infixl (sem_Range _range ) )
sem_Fixity (Fixity_Infixr _range )  =
    (sem_Fixity_Infixr (sem_Range _range ) )
-- semantic domain
type T_Fixity  = ( Fixity)
sem_Fixity_Infix :: T_Range  ->
                    T_Fixity 
sem_Fixity_Infix range_  =
    (let _lhsOself :: Fixity
         _rangeIself :: Range
         _self =
             Fixity_Infix _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_Fixity_Infixl :: T_Range  ->
                     T_Fixity 
sem_Fixity_Infixl range_  =
    (let _lhsOself :: Fixity
         _rangeIself :: Range
         _self =
             Fixity_Infixl _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_Fixity_Infixr :: T_Range  ->
                     T_Fixity 
sem_Fixity_Infixr range_  =
    (let _lhsOself :: Fixity
         _rangeIself :: Range
         _self =
             Fixity_Infixr _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
-- FunctionBinding ---------------------------------------------
-- cata
sem_FunctionBinding :: FunctionBinding  ->
                       T_FunctionBinding 
sem_FunctionBinding (FunctionBinding_FunctionBinding _range _lefthandside _righthandside )  =
    (sem_FunctionBinding_FunctionBinding (sem_Range _range ) (sem_LeftHandSide _lefthandside ) (sem_RightHandSide _righthandside ) )
-- semantic domain
type T_FunctionBinding  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                          (M.Map NameWithRange TpScheme) ->
                          Predicates ->
                          Tp ->
                          Int ->
                          Tps ->
                          ClassEnvironment ->
                          TypeErrors ->
                          Warnings ->
                          Int ->
                          DictionaryEnvironment ->
                          ImportEnvironment ->
                          (IO ()) ->
                          Monos ->
                          Names ->
                          OrderedTypeSynonyms ->
                          InfoTree ->
                          ([Warning]) ->
                          FixpointSubstitution ->
                          (M.Map Int (Scheme Predicates)) ->
                          Int ->
                          ( Int,Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,DictionaryEnvironment,( ([PatternElement], Bool) ),InfoTree,(IO ()),Name,Int,([Warning]),FunctionBinding,Names,Int,Warning)
sem_FunctionBinding_FunctionBinding :: T_Range  ->
                                       T_LeftHandSide  ->
                                       T_RightHandSide  ->
                                       T_FunctionBinding 
sem_FunctionBinding_FunctionBinding range_ lefthandside_ righthandside_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIbetasLeft
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _righthandsideOmonos :: Monos
              _lhsOassumptions :: Assumptions
              _lhsOinfoTree :: InfoTree
              _lhsOunboundNames :: Names
              _lhsOunrwar :: Warning
              _lhsOelements :: ( ([PatternElement], Bool) )
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: FunctionBinding
              _lhsOargcount :: Int
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOname :: Name
              _lhsOnumberOfPatterns :: Int
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lefthandsideObetaUnique :: Int
              _lefthandsideOimportEnvironment :: ImportEnvironment
              _lefthandsideOmonos :: Monos
              _lefthandsideOnamesInScope :: Names
              _lefthandsideOparentTree :: InfoTree
              _lefthandsideOpatternMatchWarnings :: ([Warning])
              _righthandsideOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _righthandsideOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _righthandsideOavailablePredicates :: Predicates
              _righthandsideObetaRight :: Tp
              _righthandsideObetaUnique :: Int
              _righthandsideOclassEnvironment :: ClassEnvironment
              _righthandsideOcollectErrors :: TypeErrors
              _righthandsideOcollectWarnings :: Warnings
              _righthandsideOcurrentChunk :: Int
              _righthandsideOdictionaryEnvironment :: DictionaryEnvironment
              _righthandsideOimportEnvironment :: ImportEnvironment
              _righthandsideOmatchIO :: (IO ())
              _righthandsideOnamesInScope :: Names
              _righthandsideOorderedTypeSynonyms :: OrderedTypeSynonyms
              _righthandsideOparentTree :: InfoTree
              _righthandsideOpatternMatchWarnings :: ([Warning])
              _righthandsideOsubstitution :: FixpointSubstitution
              _righthandsideOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _righthandsideOuniqueChunk :: Int
              _rangeIself :: Range
              _lefthandsideIargcount :: Int
              _lefthandsideIbetaUnique :: Int
              _lefthandsideIbetas :: Tps
              _lefthandsideIconstraints :: ConstraintSet
              _lefthandsideIelements :: (  [PatternElement]        )
              _lefthandsideIenvironment :: PatternAssumptions
              _lefthandsideIinfoTrees :: InfoTrees
              _lefthandsideIname :: Name
              _lefthandsideInumberOfPatterns :: Int
              _lefthandsideIpatVarNames :: Names
              _lefthandsideIpatternMatchWarnings :: ([Warning])
              _lefthandsideIself :: LeftHandSide
              _lefthandsideIunboundNames :: Names
              _righthandsideIassumptions :: Assumptions
              _righthandsideIbetaUnique :: Int
              _righthandsideIcollectErrors :: TypeErrors
              _righthandsideIcollectInstances :: ([(Name, Instance)])
              _righthandsideIcollectWarnings :: Warnings
              _righthandsideIconstraints :: ConstraintSet
              _righthandsideIdictionaryEnvironment :: DictionaryEnvironment
              _righthandsideIfallthrough :: Bool
              _righthandsideIinfoTree :: InfoTree
              _righthandsideImatchIO :: (IO ())
              _righthandsideIpatternMatchWarnings :: ([Warning])
              _righthandsideIself :: RightHandSide
              _righthandsideIunboundNames :: Names
              _righthandsideIuniqueChunk :: Int
              _righthandsideOmonos =
                  M.elems _lefthandsideIenvironment ++ getMonos _csetBinds ++ _lhsImonos
              _constraints =
                  _csetBinds .>>.
                  Node [ _conLeft  .<. _lefthandsideIconstraints
                       , _righthandsideIconstraints
                       ]
              _conLeft =
                  zipWith3 (\t1 t2 nr -> (t1 .==. t2) (_cinfoLeft nr)) _lefthandsideIbetas _lhsIbetasLeft [0..]
              __tup35 =
                  (_lefthandsideIenvironment .===. _righthandsideIassumptions) _cinfoBind
              (_csetBinds,_) =
                  __tup35
              (_,_lhsOassumptions) =
                  __tup35
              _cinfoLeft =
                  \num  ->
                  orphanConstraint num "pattern of function binding" _parentTree
                     [ Unifier (head (ftv (_lhsIbetasLeft !! num))) (ordinal True (num+1)++" pattern of function bindings", attribute _lhsIparentTree, "pattern") ]
              _cinfoBind =
                  \name -> variableConstraint "variable" (nameToUHA_Expr name)
                     [ FolkloreConstraint
                     , makeUnifier name "function binding" _lefthandsideIenvironment _parentTree
                     ]
              _localInfo =
                  LocalInfo { self = UHA_FB _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo (_lefthandsideIinfoTrees ++ [_righthandsideIinfoTree])
              _lhsOinfoTree =
                  _parentTree
              __tup36 =
                  changeOfScope _lefthandsideIpatVarNames _righthandsideIunboundNames _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup36
              (_,_unboundNames,_) =
                  __tup36
              (_,_,_scopeInfo) =
                  __tup36
              _lhsOunboundNames =
                  _unboundNames
              _lhsOunrwar =
                  UnreachablePatternLHS _lefthandsideIself
              _lhsOelements =
                  (_lefthandsideIelements, _righthandsideIfallthrough)
              _lhsOcollectInstances =
                  _righthandsideIcollectInstances
              _self =
                  FunctionBinding_FunctionBinding _rangeIself _lefthandsideIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsOargcount =
                  _lefthandsideIargcount
              _lhsObetaUnique =
                  _righthandsideIbetaUnique
              _lhsOcollectErrors =
                  _righthandsideIcollectErrors
              _lhsOcollectWarnings =
                  _righthandsideIcollectWarnings
              _lhsOconstraints =
                  _constraints
              _lhsOdictionaryEnvironment =
                  _righthandsideIdictionaryEnvironment
              _lhsOmatchIO =
                  _righthandsideImatchIO
              _lhsOname =
                  _lefthandsideIname
              _lhsOnumberOfPatterns =
                  _lefthandsideInumberOfPatterns
              _lhsOpatternMatchWarnings =
                  _righthandsideIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _righthandsideIuniqueChunk
              _lefthandsideObetaUnique =
                  _lhsIbetaUnique
              _lefthandsideOimportEnvironment =
                  _lhsIimportEnvironment
              _lefthandsideOmonos =
                  _lhsImonos
              _lefthandsideOnamesInScope =
                  _namesInScope
              _lefthandsideOparentTree =
                  _parentTree
              _lefthandsideOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _righthandsideOallPatterns =
                  _lhsIallPatterns
              _righthandsideOallTypeSchemes =
                  _lhsIallTypeSchemes
              _righthandsideOavailablePredicates =
                  _lhsIavailablePredicates
              _righthandsideObetaRight =
                  _lhsIbetaRight
              _righthandsideObetaUnique =
                  _lefthandsideIbetaUnique
              _righthandsideOclassEnvironment =
                  _lhsIclassEnvironment
              _righthandsideOcollectErrors =
                  _lhsIcollectErrors
              _righthandsideOcollectWarnings =
                  _lhsIcollectWarnings
              _righthandsideOcurrentChunk =
                  _lhsIcurrentChunk
              _righthandsideOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _righthandsideOimportEnvironment =
                  _lhsIimportEnvironment
              _righthandsideOmatchIO =
                  _lhsImatchIO
              _righthandsideOnamesInScope =
                  _namesInScope
              _righthandsideOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _righthandsideOparentTree =
                  _parentTree
              _righthandsideOpatternMatchWarnings =
                  _lefthandsideIpatternMatchWarnings
              _righthandsideOsubstitution =
                  _lhsIsubstitution
              _righthandsideOtypeschemeMap =
                  _lhsItypeschemeMap
              _righthandsideOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _lefthandsideIargcount,_lefthandsideIbetaUnique,_lefthandsideIbetas,_lefthandsideIconstraints,_lefthandsideIelements,_lefthandsideIenvironment,_lefthandsideIinfoTrees,_lefthandsideIname,_lefthandsideInumberOfPatterns,_lefthandsideIpatVarNames,_lefthandsideIpatternMatchWarnings,_lefthandsideIself,_lefthandsideIunboundNames) =
                  (lefthandside_ _lefthandsideObetaUnique _lefthandsideOimportEnvironment _lefthandsideOmonos _lefthandsideOnamesInScope _lefthandsideOparentTree _lefthandsideOpatternMatchWarnings )
              ( _righthandsideIassumptions,_righthandsideIbetaUnique,_righthandsideIcollectErrors,_righthandsideIcollectInstances,_righthandsideIcollectWarnings,_righthandsideIconstraints,_righthandsideIdictionaryEnvironment,_righthandsideIfallthrough,_righthandsideIinfoTree,_righthandsideImatchIO,_righthandsideIpatternMatchWarnings,_righthandsideIself,_righthandsideIunboundNames,_righthandsideIuniqueChunk) =
                  (righthandside_ _righthandsideOallPatterns _righthandsideOallTypeSchemes _righthandsideOavailablePredicates _righthandsideObetaRight _righthandsideObetaUnique _righthandsideOclassEnvironment _righthandsideOcollectErrors _righthandsideOcollectWarnings _righthandsideOcurrentChunk _righthandsideOdictionaryEnvironment _righthandsideOimportEnvironment _righthandsideOmatchIO _righthandsideOmonos _righthandsideOnamesInScope _righthandsideOorderedTypeSynonyms _righthandsideOparentTree _righthandsideOpatternMatchWarnings _righthandsideOsubstitution _righthandsideOtypeschemeMap _righthandsideOuniqueChunk )
          in  ( _lhsOargcount,_lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOelements,_lhsOinfoTree,_lhsOmatchIO,_lhsOname,_lhsOnumberOfPatterns,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOunrwar)))
-- FunctionBindings --------------------------------------------
-- cata
sem_FunctionBindings :: FunctionBindings  ->
                        T_FunctionBindings 
sem_FunctionBindings list  =
    (Prelude.foldr sem_FunctionBindings_Cons sem_FunctionBindings_Nil (Prelude.map sem_FunctionBinding list) )
-- semantic domain
type T_FunctionBindings  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                           (M.Map NameWithRange TpScheme) ->
                           Predicates ->
                           Tp ->
                           Int ->
                           Tps ->
                           ClassEnvironment ->
                           TypeErrors ->
                           Warnings ->
                           Int ->
                           DictionaryEnvironment ->
                           ImportEnvironment ->
                           (IO ()) ->
                           Monos ->
                           Names ->
                           OrderedTypeSynonyms ->
                           InfoTree ->
                           ([Warning]) ->
                           FixpointSubstitution ->
                           (M.Map Int (Scheme Predicates)) ->
                           Int ->
                           ( Int,Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSets,DictionaryEnvironment,([([PatternElement], Bool)]),InfoTrees,(IO ()),Name,Int,([Warning]),FunctionBindings,Names,Int,([Warning]))
sem_FunctionBindings_Cons :: T_FunctionBinding  ->
                             T_FunctionBindings  ->
                             T_FunctionBindings 
sem_FunctionBindings_Cons hd_ tl_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIbetasLeft
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOassumptions :: Assumptions
              _lhsOnumberOfPatterns :: Int
              _lhsOname :: Name
              _lhsOconstraintslist :: ConstraintSets
              _lhsOinfoTrees :: InfoTrees
              _lhsOelementss :: ([([PatternElement], Bool)])
              _lhsOunrwars :: ([Warning])
              _lhsOargcount :: Int
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: FunctionBindings
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _hdOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _hdOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _hdOavailablePredicates :: Predicates
              _hdObetaRight :: Tp
              _hdObetaUnique :: Int
              _hdObetasLeft :: Tps
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectErrors :: TypeErrors
              _hdOcollectWarnings :: Warnings
              _hdOcurrentChunk :: Int
              _hdOdictionaryEnvironment :: DictionaryEnvironment
              _hdOimportEnvironment :: ImportEnvironment
              _hdOmatchIO :: (IO ())
              _hdOmonos :: Monos
              _hdOnamesInScope :: Names
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOparentTree :: InfoTree
              _hdOpatternMatchWarnings :: ([Warning])
              _hdOsubstitution :: FixpointSubstitution
              _hdOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _hdOuniqueChunk :: Int
              _tlOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _tlOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _tlOavailablePredicates :: Predicates
              _tlObetaRight :: Tp
              _tlObetaUnique :: Int
              _tlObetasLeft :: Tps
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectErrors :: TypeErrors
              _tlOcollectWarnings :: Warnings
              _tlOcurrentChunk :: Int
              _tlOdictionaryEnvironment :: DictionaryEnvironment
              _tlOimportEnvironment :: ImportEnvironment
              _tlOmatchIO :: (IO ())
              _tlOmonos :: Monos
              _tlOnamesInScope :: Names
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOparentTree :: InfoTree
              _tlOpatternMatchWarnings :: ([Warning])
              _tlOsubstitution :: FixpointSubstitution
              _tlOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _tlOuniqueChunk :: Int
              _hdIargcount :: Int
              _hdIassumptions :: Assumptions
              _hdIbetaUnique :: Int
              _hdIcollectErrors :: TypeErrors
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectWarnings :: Warnings
              _hdIconstraints :: ConstraintSet
              _hdIdictionaryEnvironment :: DictionaryEnvironment
              _hdIelements :: ( ([PatternElement], Bool) )
              _hdIinfoTree :: InfoTree
              _hdImatchIO :: (IO ())
              _hdIname :: Name
              _hdInumberOfPatterns :: Int
              _hdIpatternMatchWarnings :: ([Warning])
              _hdIself :: FunctionBinding
              _hdIunboundNames :: Names
              _hdIuniqueChunk :: Int
              _hdIunrwar :: Warning
              _tlIargcount :: Int
              _tlIassumptions :: Assumptions
              _tlIbetaUnique :: Int
              _tlIcollectErrors :: TypeErrors
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectWarnings :: Warnings
              _tlIconstraintslist :: ConstraintSets
              _tlIdictionaryEnvironment :: DictionaryEnvironment
              _tlIelementss :: ([([PatternElement], Bool)])
              _tlIinfoTrees :: InfoTrees
              _tlImatchIO :: (IO ())
              _tlIname :: Name
              _tlInumberOfPatterns :: Int
              _tlIpatternMatchWarnings :: ([Warning])
              _tlIself :: FunctionBindings
              _tlIunboundNames :: Names
              _tlIuniqueChunk :: Int
              _tlIunrwars :: ([Warning])
              _lhsOassumptions =
                  _hdIassumptions `combine` _tlIassumptions
              _lhsOnumberOfPatterns =
                  _hdInumberOfPatterns
              _lhsOname =
                  _hdIname
              _lhsOconstraintslist =
                  _hdIconstraints : _tlIconstraintslist
              _lhsOinfoTrees =
                  _hdIinfoTree : _tlIinfoTrees
              _lhsOelementss =
                  _hdIelements : _tlIelementss
              _lhsOunrwars =
                  _hdIunrwar   : _tlIunrwars
              _lhsOargcount =
                  _hdIargcount
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _tlIbetaUnique
              _lhsOcollectErrors =
                  _tlIcollectErrors
              _lhsOcollectWarnings =
                  _tlIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _tlIdictionaryEnvironment
              _lhsOmatchIO =
                  _tlImatchIO
              _lhsOpatternMatchWarnings =
                  _tlIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _tlIuniqueChunk
              _hdOallPatterns =
                  _lhsIallPatterns
              _hdOallTypeSchemes =
                  _lhsIallTypeSchemes
              _hdOavailablePredicates =
                  _lhsIavailablePredicates
              _hdObetaRight =
                  _lhsIbetaRight
              _hdObetaUnique =
                  _lhsIbetaUnique
              _hdObetasLeft =
                  _lhsIbetasLeft
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectErrors =
                  _lhsIcollectErrors
              _hdOcollectWarnings =
                  _lhsIcollectWarnings
              _hdOcurrentChunk =
                  _lhsIcurrentChunk
              _hdOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _hdOimportEnvironment =
                  _lhsIimportEnvironment
              _hdOmatchIO =
                  _lhsImatchIO
              _hdOmonos =
                  _lhsImonos
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOparentTree =
                  _lhsIparentTree
              _hdOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _hdOsubstitution =
                  _lhsIsubstitution
              _hdOtypeschemeMap =
                  _lhsItypeschemeMap
              _hdOuniqueChunk =
                  _lhsIuniqueChunk
              _tlOallPatterns =
                  _lhsIallPatterns
              _tlOallTypeSchemes =
                  _lhsIallTypeSchemes
              _tlOavailablePredicates =
                  _lhsIavailablePredicates
              _tlObetaRight =
                  _lhsIbetaRight
              _tlObetaUnique =
                  _hdIbetaUnique
              _tlObetasLeft =
                  _lhsIbetasLeft
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectErrors =
                  _hdIcollectErrors
              _tlOcollectWarnings =
                  _hdIcollectWarnings
              _tlOcurrentChunk =
                  _lhsIcurrentChunk
              _tlOdictionaryEnvironment =
                  _hdIdictionaryEnvironment
              _tlOimportEnvironment =
                  _lhsIimportEnvironment
              _tlOmatchIO =
                  _hdImatchIO
              _tlOmonos =
                  _lhsImonos
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOparentTree =
                  _lhsIparentTree
              _tlOpatternMatchWarnings =
                  _hdIpatternMatchWarnings
              _tlOsubstitution =
                  _lhsIsubstitution
              _tlOtypeschemeMap =
                  _lhsItypeschemeMap
              _tlOuniqueChunk =
                  _hdIuniqueChunk
              ( _hdIargcount,_hdIassumptions,_hdIbetaUnique,_hdIcollectErrors,_hdIcollectInstances,_hdIcollectWarnings,_hdIconstraints,_hdIdictionaryEnvironment,_hdIelements,_hdIinfoTree,_hdImatchIO,_hdIname,_hdInumberOfPatterns,_hdIpatternMatchWarnings,_hdIself,_hdIunboundNames,_hdIuniqueChunk,_hdIunrwar) =
                  (hd_ _hdOallPatterns _hdOallTypeSchemes _hdOavailablePredicates _hdObetaRight _hdObetaUnique _hdObetasLeft _hdOclassEnvironment _hdOcollectErrors _hdOcollectWarnings _hdOcurrentChunk _hdOdictionaryEnvironment _hdOimportEnvironment _hdOmatchIO _hdOmonos _hdOnamesInScope _hdOorderedTypeSynonyms _hdOparentTree _hdOpatternMatchWarnings _hdOsubstitution _hdOtypeschemeMap _hdOuniqueChunk )
              ( _tlIargcount,_tlIassumptions,_tlIbetaUnique,_tlIcollectErrors,_tlIcollectInstances,_tlIcollectWarnings,_tlIconstraintslist,_tlIdictionaryEnvironment,_tlIelementss,_tlIinfoTrees,_tlImatchIO,_tlIname,_tlInumberOfPatterns,_tlIpatternMatchWarnings,_tlIself,_tlIunboundNames,_tlIuniqueChunk,_tlIunrwars) =
                  (tl_ _tlOallPatterns _tlOallTypeSchemes _tlOavailablePredicates _tlObetaRight _tlObetaUnique _tlObetasLeft _tlOclassEnvironment _tlOcollectErrors _tlOcollectWarnings _tlOcurrentChunk _tlOdictionaryEnvironment _tlOimportEnvironment _tlOmatchIO _tlOmonos _tlOnamesInScope _tlOorderedTypeSynonyms _tlOparentTree _tlOpatternMatchWarnings _tlOsubstitution _tlOtypeschemeMap _tlOuniqueChunk )
          in  ( _lhsOargcount,_lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraintslist,_lhsOdictionaryEnvironment,_lhsOelementss,_lhsOinfoTrees,_lhsOmatchIO,_lhsOname,_lhsOnumberOfPatterns,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOunrwars)))
sem_FunctionBindings_Nil :: T_FunctionBindings 
sem_FunctionBindings_Nil  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIbetasLeft
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOassumptions :: Assumptions
              _lhsOnumberOfPatterns :: Int
              _lhsOname :: Name
              _lhsOconstraintslist :: ConstraintSets
              _lhsOinfoTrees :: InfoTrees
              _lhsOelementss :: ([([PatternElement], Bool)])
              _lhsOunrwars :: ([Warning])
              _lhsOargcount :: Int
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: FunctionBindings
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOassumptions =
                  noAssumptions
              _lhsOnumberOfPatterns =
                  internalError "TypeInferencing.ag" "n/a" "FunctionBindings(1)"
              _lhsOname =
                  internalError "TypeInferencing.ag" "n/a" "FunctionBindings(2)"
              _lhsOconstraintslist =
                  []
              _lhsOinfoTrees =
                  []
              _lhsOelementss =
                  []
              _lhsOunrwars =
                  []
              _lhsOargcount =
                  pmError "FunctionBindings_Nil.argcount" "?empty list of function bindings?"
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
          in  ( _lhsOargcount,_lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraintslist,_lhsOdictionaryEnvironment,_lhsOelementss,_lhsOinfoTrees,_lhsOmatchIO,_lhsOname,_lhsOnumberOfPatterns,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOunrwars)))
-- GuardedExpression -------------------------------------------
-- cata
sem_GuardedExpression :: GuardedExpression  ->
                         T_GuardedExpression 
sem_GuardedExpression (GuardedExpression_GuardedExpression _range _guard _expression )  =
    (sem_GuardedExpression_GuardedExpression (sem_Range _range ) (sem_Expression _guard ) (sem_Expression _expression ) )
-- semantic domain
type T_GuardedExpression  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                            (M.Map NameWithRange TpScheme) ->
                            Predicates ->
                            Tp ->
                            Int ->
                            ClassEnvironment ->
                            TypeErrors ->
                            Warnings ->
                            Int ->
                            DictionaryEnvironment ->
                            ImportEnvironment ->
                            (IO ()) ->
                            Monos ->
                            Names ->
                            Int ->
                            OrderedTypeSynonyms ->
                            InfoTree ->
                            ([Warning]) ->
                            FixpointSubstitution ->
                            (M.Map Int (Scheme Predicates)) ->
                            Int ->
                            Int ->
                            ( Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,DictionaryEnvironment,Bool,InfoTrees,(IO ()),([Warning]),Range,GuardedExpression,Names,Int,Int,Warning)
sem_GuardedExpression_GuardedExpression :: T_Range  ->
                                           T_Expression  ->
                                           T_Expression  ->
                                           T_GuardedExpression 
sem_GuardedExpression_GuardedExpression range_ guard_ expression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsInumberOfGuards
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOinfoTrees :: InfoTrees
              _guardOtryPatterns :: ([(Expression     , [String])])
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOfallthrough :: Bool
              _lhsOunrwar :: Warning
              _lhsOrange :: Range
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: GuardedExpression
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _guardOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _guardOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _guardOavailablePredicates :: Predicates
              _guardObetaUnique :: Int
              _guardOclassEnvironment :: ClassEnvironment
              _guardOcollectErrors :: TypeErrors
              _guardOcollectWarnings :: Warnings
              _guardOcurrentChunk :: Int
              _guardOdictionaryEnvironment :: DictionaryEnvironment
              _guardOimportEnvironment :: ImportEnvironment
              _guardOmatchIO :: (IO ())
              _guardOmonos :: Monos
              _guardOnamesInScope :: Names
              _guardOorderedTypeSynonyms :: OrderedTypeSynonyms
              _guardOparentTree :: InfoTree
              _guardOpatternMatchWarnings :: ([Warning])
              _guardOsubstitution :: FixpointSubstitution
              _guardOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _guardOuniqueChunk :: Int
              _guardOuniqueSecondRound :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionObetaUnique :: Int
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _guardIassumptions :: Assumptions
              _guardIbeta :: Tp
              _guardIbetaUnique :: Int
              _guardIcollectErrors :: TypeErrors
              _guardIcollectInstances :: ([(Name, Instance)])
              _guardIcollectWarnings :: Warnings
              _guardIconstraints :: ConstraintSet
              _guardIdictionaryEnvironment :: DictionaryEnvironment
              _guardIinfoTree :: InfoTree
              _guardImatchIO :: (IO ())
              _guardImatches :: ([Maybe MetaVariableTable])
              _guardIpatternMatchWarnings :: ([Warning])
              _guardIself :: Expression
              _guardIunboundNames :: Names
              _guardIuniqueChunk :: Int
              _guardIuniqueSecondRound :: Int
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _lhsOconstraints =
                  Node [ _newconGuard .<. _guardIconstraints
                       , _newconExpr  .<. _expressionIconstraints
                       ]
              _lhsOassumptions =
                  _guardIassumptions `combine` _expressionIassumptions
              _newconGuard =
                  [ (_guardIbeta .==. boolType) _cinfoGuard ]
              _newconExpr =
                  [ (_expressionIbeta .==. _lhsIbetaRight) _cinfoExpr ]
              _cinfoGuard =
                  resultConstraint "guard" _guardIinfoTree
                     []
              _cinfoExpr =
                  resultConstraint "guarded expression" _expressionIinfoTree $
                     [ HasTrustFactor 10.0 | _lhsInumberOfGuards < 2 ] ++
                     [ Unifier (head (ftv _lhsIbetaRight)) ("right-hand sides", attribute (skip_UHA_FB_RHS _lhsIparentTree), "right-hand side") ]
              _lhsOinfoTrees =
                  [_guardIinfoTree, _expressionIinfoTree]
              _guardOtryPatterns =
                  []
              _expressionOtryPatterns =
                  []
              _lhsOfallthrough =
                  case _guardIself
                  of Expression_Variable    _ (Name_Identifier _ _ "otherwise") -> False
                     Expression_Constructor _ (Name_Identifier _ _ "True"     ) -> False
                     _                                                          -> True
              _lhsOunrwar =
                  UnreachableGuard _rangeIself _guardIself
              _lhsOrange =
                  _rangeIself
              _lhsOcollectInstances =
                  _guardIcollectInstances  ++  _expressionIcollectInstances
              _lhsOunboundNames =
                  _guardIunboundNames ++ _expressionIunboundNames
              _self =
                  GuardedExpression_GuardedExpression _rangeIself _guardIself _expressionIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _expressionIbetaUnique
              _lhsOcollectErrors =
                  _expressionIcollectErrors
              _lhsOcollectWarnings =
                  _expressionIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _lhsOmatchIO =
                  _expressionImatchIO
              _lhsOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _expressionIuniqueChunk
              _lhsOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              _guardOallPatterns =
                  _lhsIallPatterns
              _guardOallTypeSchemes =
                  _lhsIallTypeSchemes
              _guardOavailablePredicates =
                  _lhsIavailablePredicates
              _guardObetaUnique =
                  _lhsIbetaUnique
              _guardOclassEnvironment =
                  _lhsIclassEnvironment
              _guardOcollectErrors =
                  _lhsIcollectErrors
              _guardOcollectWarnings =
                  _lhsIcollectWarnings
              _guardOcurrentChunk =
                  _lhsIcurrentChunk
              _guardOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _guardOimportEnvironment =
                  _lhsIimportEnvironment
              _guardOmatchIO =
                  _lhsImatchIO
              _guardOmonos =
                  _lhsImonos
              _guardOnamesInScope =
                  _lhsInamesInScope
              _guardOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _guardOparentTree =
                  _lhsIparentTree
              _guardOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _guardOsubstitution =
                  _lhsIsubstitution
              _guardOtypeschemeMap =
                  _lhsItypeschemeMap
              _guardOuniqueChunk =
                  _lhsIuniqueChunk
              _guardOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionObetaUnique =
                  _guardIbetaUnique
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _guardIcollectErrors
              _expressionOcollectWarnings =
                  _guardIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _guardIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _guardImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _lhsIparentTree
              _expressionOpatternMatchWarnings =
                  _guardIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _guardIuniqueChunk
              _expressionOuniqueSecondRound =
                  _guardIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _guardIassumptions,_guardIbeta,_guardIbetaUnique,_guardIcollectErrors,_guardIcollectInstances,_guardIcollectWarnings,_guardIconstraints,_guardIdictionaryEnvironment,_guardIinfoTree,_guardImatchIO,_guardImatches,_guardIpatternMatchWarnings,_guardIself,_guardIunboundNames,_guardIuniqueChunk,_guardIuniqueSecondRound) =
                  (guard_ _guardOallPatterns _guardOallTypeSchemes _guardOavailablePredicates _guardObetaUnique _guardOclassEnvironment _guardOcollectErrors _guardOcollectWarnings _guardOcurrentChunk _guardOdictionaryEnvironment _guardOimportEnvironment _guardOmatchIO _guardOmonos _guardOnamesInScope _guardOorderedTypeSynonyms _guardOparentTree _guardOpatternMatchWarnings _guardOsubstitution _guardOtryPatterns _guardOtypeschemeMap _guardOuniqueChunk _guardOuniqueSecondRound )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOfallthrough,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOrange,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound,_lhsOunrwar)))
-- GuardedExpressions ------------------------------------------
-- cata
sem_GuardedExpressions :: GuardedExpressions  ->
                          T_GuardedExpressions 
sem_GuardedExpressions list  =
    (Prelude.foldr sem_GuardedExpressions_Cons sem_GuardedExpressions_Nil (Prelude.map sem_GuardedExpression list) )
-- semantic domain
type T_GuardedExpressions  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                             (M.Map NameWithRange TpScheme) ->
                             Predicates ->
                             Tp ->
                             Int ->
                             ClassEnvironment ->
                             TypeErrors ->
                             Warnings ->
                             Int ->
                             DictionaryEnvironment ->
                             ImportEnvironment ->
                             (IO ()) ->
                             Monos ->
                             Names ->
                             Int ->
                             Bool ->
                             OrderedTypeSynonyms ->
                             InfoTree ->
                             ([Warning]) ->
                             FixpointSubstitution ->
                             (M.Map Int (Scheme Predicates)) ->
                             Int ->
                             Int ->
                             ( Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSets,DictionaryEnvironment,Bool,InfoTrees,(IO ()),([Warning]),GuardedExpressions,Names,Int,Int)
sem_GuardedExpressions_Cons :: T_GuardedExpression  ->
                               T_GuardedExpressions  ->
                               T_GuardedExpressions 
sem_GuardedExpressions_Cons hd_ tl_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsInumberOfGuards
       _lhsIopen
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraintslist :: ConstraintSets
              _lhsOinfoTrees :: InfoTrees
              _lhsOfallthrough :: Bool
              _tlOopen :: Bool
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: GuardedExpressions
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _hdOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _hdOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _hdOavailablePredicates :: Predicates
              _hdObetaRight :: Tp
              _hdObetaUnique :: Int
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectErrors :: TypeErrors
              _hdOcollectWarnings :: Warnings
              _hdOcurrentChunk :: Int
              _hdOdictionaryEnvironment :: DictionaryEnvironment
              _hdOimportEnvironment :: ImportEnvironment
              _hdOmatchIO :: (IO ())
              _hdOmonos :: Monos
              _hdOnamesInScope :: Names
              _hdOnumberOfGuards :: Int
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOparentTree :: InfoTree
              _hdOpatternMatchWarnings :: ([Warning])
              _hdOsubstitution :: FixpointSubstitution
              _hdOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _hdOuniqueChunk :: Int
              _hdOuniqueSecondRound :: Int
              _tlOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _tlOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _tlOavailablePredicates :: Predicates
              _tlObetaRight :: Tp
              _tlObetaUnique :: Int
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectErrors :: TypeErrors
              _tlOcollectWarnings :: Warnings
              _tlOcurrentChunk :: Int
              _tlOdictionaryEnvironment :: DictionaryEnvironment
              _tlOimportEnvironment :: ImportEnvironment
              _tlOmatchIO :: (IO ())
              _tlOmonos :: Monos
              _tlOnamesInScope :: Names
              _tlOnumberOfGuards :: Int
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOparentTree :: InfoTree
              _tlOpatternMatchWarnings :: ([Warning])
              _tlOsubstitution :: FixpointSubstitution
              _tlOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _tlOuniqueChunk :: Int
              _tlOuniqueSecondRound :: Int
              _hdIassumptions :: Assumptions
              _hdIbetaUnique :: Int
              _hdIcollectErrors :: TypeErrors
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectWarnings :: Warnings
              _hdIconstraints :: ConstraintSet
              _hdIdictionaryEnvironment :: DictionaryEnvironment
              _hdIfallthrough :: Bool
              _hdIinfoTrees :: InfoTrees
              _hdImatchIO :: (IO ())
              _hdIpatternMatchWarnings :: ([Warning])
              _hdIrange :: Range
              _hdIself :: GuardedExpression
              _hdIunboundNames :: Names
              _hdIuniqueChunk :: Int
              _hdIuniqueSecondRound :: Int
              _hdIunrwar :: Warning
              _tlIassumptions :: Assumptions
              _tlIbetaUnique :: Int
              _tlIcollectErrors :: TypeErrors
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectWarnings :: Warnings
              _tlIconstraintslist :: ConstraintSets
              _tlIdictionaryEnvironment :: DictionaryEnvironment
              _tlIfallthrough :: Bool
              _tlIinfoTrees :: InfoTrees
              _tlImatchIO :: (IO ())
              _tlIpatternMatchWarnings :: ([Warning])
              _tlIself :: GuardedExpressions
              _tlIunboundNames :: Names
              _tlIuniqueChunk :: Int
              _tlIuniqueSecondRound :: Int
              _lhsOassumptions =
                  _hdIassumptions `combine` _tlIassumptions
              _lhsOconstraintslist =
                  _hdIconstraints : _tlIconstraintslist
              _lhsOinfoTrees =
                  _hdIinfoTrees ++ _tlIinfoTrees
              _lhsOfallthrough =
                  _hdIfallthrough && _tlIfallthrough
              _tlOopen =
                  _hdIfallthrough && _lhsIopen
              _lhsOpatternMatchWarnings =
                  (if not _lhsIopen then [_hdIunrwar] else [])
                  ++ _tlIpatternMatchWarnings
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _tlIbetaUnique
              _lhsOcollectErrors =
                  _tlIcollectErrors
              _lhsOcollectWarnings =
                  _tlIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _tlIdictionaryEnvironment
              _lhsOmatchIO =
                  _tlImatchIO
              _lhsOuniqueChunk =
                  _tlIuniqueChunk
              _lhsOuniqueSecondRound =
                  _tlIuniqueSecondRound
              _hdOallPatterns =
                  _lhsIallPatterns
              _hdOallTypeSchemes =
                  _lhsIallTypeSchemes
              _hdOavailablePredicates =
                  _lhsIavailablePredicates
              _hdObetaRight =
                  _lhsIbetaRight
              _hdObetaUnique =
                  _lhsIbetaUnique
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectErrors =
                  _lhsIcollectErrors
              _hdOcollectWarnings =
                  _lhsIcollectWarnings
              _hdOcurrentChunk =
                  _lhsIcurrentChunk
              _hdOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _hdOimportEnvironment =
                  _lhsIimportEnvironment
              _hdOmatchIO =
                  _lhsImatchIO
              _hdOmonos =
                  _lhsImonos
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOnumberOfGuards =
                  _lhsInumberOfGuards
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOparentTree =
                  _lhsIparentTree
              _hdOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _hdOsubstitution =
                  _lhsIsubstitution
              _hdOtypeschemeMap =
                  _lhsItypeschemeMap
              _hdOuniqueChunk =
                  _lhsIuniqueChunk
              _hdOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _tlOallPatterns =
                  _lhsIallPatterns
              _tlOallTypeSchemes =
                  _lhsIallTypeSchemes
              _tlOavailablePredicates =
                  _lhsIavailablePredicates
              _tlObetaRight =
                  _lhsIbetaRight
              _tlObetaUnique =
                  _hdIbetaUnique
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectErrors =
                  _hdIcollectErrors
              _tlOcollectWarnings =
                  _hdIcollectWarnings
              _tlOcurrentChunk =
                  _lhsIcurrentChunk
              _tlOdictionaryEnvironment =
                  _hdIdictionaryEnvironment
              _tlOimportEnvironment =
                  _lhsIimportEnvironment
              _tlOmatchIO =
                  _hdImatchIO
              _tlOmonos =
                  _lhsImonos
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOnumberOfGuards =
                  _lhsInumberOfGuards
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOparentTree =
                  _lhsIparentTree
              _tlOpatternMatchWarnings =
                  _hdIpatternMatchWarnings
              _tlOsubstitution =
                  _lhsIsubstitution
              _tlOtypeschemeMap =
                  _lhsItypeschemeMap
              _tlOuniqueChunk =
                  _hdIuniqueChunk
              _tlOuniqueSecondRound =
                  _hdIuniqueSecondRound
              ( _hdIassumptions,_hdIbetaUnique,_hdIcollectErrors,_hdIcollectInstances,_hdIcollectWarnings,_hdIconstraints,_hdIdictionaryEnvironment,_hdIfallthrough,_hdIinfoTrees,_hdImatchIO,_hdIpatternMatchWarnings,_hdIrange,_hdIself,_hdIunboundNames,_hdIuniqueChunk,_hdIuniqueSecondRound,_hdIunrwar) =
                  (hd_ _hdOallPatterns _hdOallTypeSchemes _hdOavailablePredicates _hdObetaRight _hdObetaUnique _hdOclassEnvironment _hdOcollectErrors _hdOcollectWarnings _hdOcurrentChunk _hdOdictionaryEnvironment _hdOimportEnvironment _hdOmatchIO _hdOmonos _hdOnamesInScope _hdOnumberOfGuards _hdOorderedTypeSynonyms _hdOparentTree _hdOpatternMatchWarnings _hdOsubstitution _hdOtypeschemeMap _hdOuniqueChunk _hdOuniqueSecondRound )
              ( _tlIassumptions,_tlIbetaUnique,_tlIcollectErrors,_tlIcollectInstances,_tlIcollectWarnings,_tlIconstraintslist,_tlIdictionaryEnvironment,_tlIfallthrough,_tlIinfoTrees,_tlImatchIO,_tlIpatternMatchWarnings,_tlIself,_tlIunboundNames,_tlIuniqueChunk,_tlIuniqueSecondRound) =
                  (tl_ _tlOallPatterns _tlOallTypeSchemes _tlOavailablePredicates _tlObetaRight _tlObetaUnique _tlOclassEnvironment _tlOcollectErrors _tlOcollectWarnings _tlOcurrentChunk _tlOdictionaryEnvironment _tlOimportEnvironment _tlOmatchIO _tlOmonos _tlOnamesInScope _tlOnumberOfGuards _tlOopen _tlOorderedTypeSynonyms _tlOparentTree _tlOpatternMatchWarnings _tlOsubstitution _tlOtypeschemeMap _tlOuniqueChunk _tlOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraintslist,_lhsOdictionaryEnvironment,_lhsOfallthrough,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_GuardedExpressions_Nil :: T_GuardedExpressions 
sem_GuardedExpressions_Nil  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsInumberOfGuards
       _lhsIopen
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraintslist :: ConstraintSets
              _lhsOinfoTrees :: InfoTrees
              _lhsOfallthrough :: Bool
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: GuardedExpressions
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _lhsOassumptions =
                  noAssumptions
              _lhsOconstraintslist =
                  []
              _lhsOinfoTrees =
                  []
              _lhsOfallthrough =
                  True
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              _lhsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraintslist,_lhsOdictionaryEnvironment,_lhsOfallthrough,_lhsOinfoTrees,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
-- Import ------------------------------------------------------
-- cata
sem_Import :: Import  ->
              T_Import 
sem_Import (Import_TypeOrClass _range _name _names )  =
    (sem_Import_TypeOrClass (sem_Range _range ) (sem_Name _name ) (sem_MaybeNames _names ) )
sem_Import (Import_TypeOrClassComplete _range _name )  =
    (sem_Import_TypeOrClassComplete (sem_Range _range ) (sem_Name _name ) )
sem_Import (Import_Variable _range _name )  =
    (sem_Import_Variable (sem_Range _range ) (sem_Name _name ) )
-- semantic domain
type T_Import  = ( Import)
sem_Import_TypeOrClass :: T_Range  ->
                          T_Name  ->
                          T_MaybeNames  ->
                          T_Import 
sem_Import_TypeOrClass range_ name_ names_  =
    (let _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _namesIself :: MaybeNames
         _self =
             Import_TypeOrClass _rangeIself _nameIself _namesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _namesIself) =
             (names_ )
     in  ( _lhsOself))
sem_Import_TypeOrClassComplete :: T_Range  ->
                                  T_Name  ->
                                  T_Import 
sem_Import_TypeOrClassComplete range_ name_  =
    (let _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Import_TypeOrClassComplete _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_Import_Variable :: T_Range  ->
                       T_Name  ->
                       T_Import 
sem_Import_Variable range_ name_  =
    (let _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Import_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
-- ImportDeclaration -------------------------------------------
-- cata
sem_ImportDeclaration :: ImportDeclaration  ->
                         T_ImportDeclaration 
sem_ImportDeclaration (ImportDeclaration_Empty _range )  =
    (sem_ImportDeclaration_Empty (sem_Range _range ) )
sem_ImportDeclaration (ImportDeclaration_Import _range _qualified _name _asname _importspecification )  =
    (sem_ImportDeclaration_Import (sem_Range _range ) _qualified (sem_Name _name ) (sem_MaybeName _asname ) (sem_MaybeImportSpecification _importspecification ) )
-- semantic domain
type T_ImportDeclaration  = ( ImportDeclaration)
sem_ImportDeclaration_Empty :: T_Range  ->
                               T_ImportDeclaration 
sem_ImportDeclaration_Empty range_  =
    (let _lhsOself :: ImportDeclaration
         _rangeIself :: Range
         _self =
             ImportDeclaration_Empty _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOself))
sem_ImportDeclaration_Import :: T_Range  ->
                                Bool ->
                                T_Name  ->
                                T_MaybeName  ->
                                T_MaybeImportSpecification  ->
                                T_ImportDeclaration 
sem_ImportDeclaration_Import range_ qualified_ name_ asname_ importspecification_  =
    (let _lhsOself :: ImportDeclaration
         _rangeIself :: Range
         _nameIself :: Name
         _asnameIself :: MaybeName
         _importspecificationIself :: MaybeImportSpecification
         _self =
             ImportDeclaration_Import _rangeIself qualified_ _nameIself _asnameIself _importspecificationIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _asnameIself) =
             (asname_ )
         ( _importspecificationIself) =
             (importspecification_ )
     in  ( _lhsOself))
-- ImportDeclarations ------------------------------------------
-- cata
sem_ImportDeclarations :: ImportDeclarations  ->
                          T_ImportDeclarations 
sem_ImportDeclarations list  =
    (Prelude.foldr sem_ImportDeclarations_Cons sem_ImportDeclarations_Nil (Prelude.map sem_ImportDeclaration list) )
-- semantic domain
type T_ImportDeclarations  = ( ImportDeclarations)
sem_ImportDeclarations_Cons :: T_ImportDeclaration  ->
                               T_ImportDeclarations  ->
                               T_ImportDeclarations 
sem_ImportDeclarations_Cons hd_ tl_  =
    (let _lhsOself :: ImportDeclarations
         _hdIself :: ImportDeclaration
         _tlIself :: ImportDeclarations
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_ImportDeclarations_Nil :: T_ImportDeclarations 
sem_ImportDeclarations_Nil  =
    (let _lhsOself :: ImportDeclarations
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- ImportSpecification -----------------------------------------
-- cata
sem_ImportSpecification :: ImportSpecification  ->
                           T_ImportSpecification 
sem_ImportSpecification (ImportSpecification_Import _range _hiding _imports )  =
    (sem_ImportSpecification_Import (sem_Range _range ) _hiding (sem_Imports _imports ) )
-- semantic domain
type T_ImportSpecification  = ( ImportSpecification)
sem_ImportSpecification_Import :: T_Range  ->
                                  Bool ->
                                  T_Imports  ->
                                  T_ImportSpecification 
sem_ImportSpecification_Import range_ hiding_ imports_  =
    (let _lhsOself :: ImportSpecification
         _rangeIself :: Range
         _importsIself :: Imports
         _self =
             ImportSpecification_Import _rangeIself hiding_ _importsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _importsIself) =
             (imports_ )
     in  ( _lhsOself))
-- Imports -----------------------------------------------------
-- cata
sem_Imports :: Imports  ->
               T_Imports 
sem_Imports list  =
    (Prelude.foldr sem_Imports_Cons sem_Imports_Nil (Prelude.map sem_Import list) )
-- semantic domain
type T_Imports  = ( Imports)
sem_Imports_Cons :: T_Import  ->
                    T_Imports  ->
                    T_Imports 
sem_Imports_Cons hd_ tl_  =
    (let _lhsOself :: Imports
         _hdIself :: Import
         _tlIself :: Imports
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Imports_Nil :: T_Imports 
sem_Imports_Nil  =
    (let _lhsOself :: Imports
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- LeftHandSide ------------------------------------------------
-- cata
sem_LeftHandSide :: LeftHandSide  ->
                    T_LeftHandSide 
sem_LeftHandSide (LeftHandSide_Function _range _name _patterns )  =
    (sem_LeftHandSide_Function (sem_Range _range ) (sem_Name _name ) (sem_Patterns _patterns ) )
sem_LeftHandSide (LeftHandSide_Infix _range _leftPattern _operator _rightPattern )  =
    (sem_LeftHandSide_Infix (sem_Range _range ) (sem_Pattern _leftPattern ) (sem_Name _operator ) (sem_Pattern _rightPattern ) )
sem_LeftHandSide (LeftHandSide_Parenthesized _range _lefthandside _patterns )  =
    (sem_LeftHandSide_Parenthesized (sem_Range _range ) (sem_LeftHandSide _lefthandside ) (sem_Patterns _patterns ) )
-- semantic domain
type T_LeftHandSide  = Int ->
                       ImportEnvironment ->
                       Monos ->
                       Names ->
                       InfoTree ->
                       ([Warning]) ->
                       ( Int,Int,Tps,ConstraintSet,(  [PatternElement]        ),PatternAssumptions,InfoTrees,Name,Int,Names,([Warning]),LeftHandSide,Names)
sem_LeftHandSide_Function :: T_Range  ->
                             T_Name  ->
                             T_Patterns  ->
                             T_LeftHandSide 
sem_LeftHandSide_Function range_ name_ patterns_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsOname :: Name
              _lhsOinfoTrees :: InfoTrees
              _lhsOelements :: (  [PatternElement]        )
              _lhsOargcount :: Int
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: LeftHandSide
              _lhsObetaUnique :: Int
              _lhsObetas :: Tps
              _lhsOconstraints :: ConstraintSet
              _lhsOenvironment :: PatternAssumptions
              _lhsOnumberOfPatterns :: Int
              _lhsOpatternMatchWarnings :: ([Warning])
              _patternsObetaUnique :: Int
              _patternsOimportEnvironment :: ImportEnvironment
              _patternsOmonos :: Monos
              _patternsOnamesInScope :: Names
              _patternsOparentTree :: InfoTree
              _patternsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _patternsIbetaUnique :: Int
              _patternsIbetas :: Tps
              _patternsIconstraintslist :: ConstraintSets
              _patternsIelementss :: ([ [PatternElement]       ])
              _patternsIenvironment :: PatternAssumptions
              _patternsIinfoTrees :: InfoTrees
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIpatternMatchWarnings :: ([Warning])
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _lhsOname =
                  _nameIself
              _constraints =
                  Node _patternsIconstraintslist
              _lhsOinfoTrees =
                  _patternsIinfoTrees
              _lhsOelements =
                  concat _patternsIelementss
              _lhsOargcount =
                  length _patternsIself
              _lhsOpatVarNames =
                  _patternsIpatVarNames
              _lhsOunboundNames =
                  _patternsIunboundNames
              _self =
                  LeftHandSide_Function _rangeIself _nameIself _patternsIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _patternsIbetaUnique
              _lhsObetas =
                  _patternsIbetas
              _lhsOconstraints =
                  _constraints
              _lhsOenvironment =
                  _patternsIenvironment
              _lhsOnumberOfPatterns =
                  _patternsInumberOfPatterns
              _lhsOpatternMatchWarnings =
                  _patternsIpatternMatchWarnings
              _patternsObetaUnique =
                  _lhsIbetaUnique
              _patternsOimportEnvironment =
                  _lhsIimportEnvironment
              _patternsOmonos =
                  _lhsImonos
              _patternsOnamesInScope =
                  _lhsInamesInScope
              _patternsOparentTree =
                  _lhsIparentTree
              _patternsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternsIbetaUnique,_patternsIbetas,_patternsIconstraintslist,_patternsIelementss,_patternsIenvironment,_patternsIinfoTrees,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIpatternMatchWarnings,_patternsIself,_patternsIunboundNames) =
                  (patterns_ _patternsObetaUnique _patternsOimportEnvironment _patternsOmonos _patternsOnamesInScope _patternsOparentTree _patternsOpatternMatchWarnings )
          in  ( _lhsOargcount,_lhsObetaUnique,_lhsObetas,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTrees,_lhsOname,_lhsOnumberOfPatterns,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_LeftHandSide_Infix :: T_Range  ->
                          T_Pattern  ->
                          T_Name  ->
                          T_Pattern  ->
                          T_LeftHandSide 
sem_LeftHandSide_Infix range_ leftPattern_ operator_ rightPattern_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsOnumberOfPatterns :: Int
              _lhsOenvironment :: PatternAssumptions
              _lhsObetas :: Tps
              _lhsOname :: Name
              _lhsOinfoTrees :: InfoTrees
              _lhsOelements :: (  [PatternElement]        )
              _lhsOargcount :: Int
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: LeftHandSide
              _lhsObetaUnique :: Int
              _lhsOconstraints :: ConstraintSet
              _lhsOpatternMatchWarnings :: ([Warning])
              _leftPatternObetaUnique :: Int
              _leftPatternOimportEnvironment :: ImportEnvironment
              _leftPatternOmonos :: Monos
              _leftPatternOnamesInScope :: Names
              _leftPatternOparentTree :: InfoTree
              _leftPatternOpatternMatchWarnings :: ([Warning])
              _rightPatternObetaUnique :: Int
              _rightPatternOimportEnvironment :: ImportEnvironment
              _rightPatternOmonos :: Monos
              _rightPatternOnamesInScope :: Names
              _rightPatternOparentTree :: InfoTree
              _rightPatternOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _leftPatternIbeta :: Tp
              _leftPatternIbetaUnique :: Int
              _leftPatternIconstraints :: ConstraintSet
              _leftPatternIelements :: (  [PatternElement]        )
              _leftPatternIenvironment :: PatternAssumptions
              _leftPatternIinfoTree :: InfoTree
              _leftPatternIpatVarNames :: Names
              _leftPatternIpatternMatchWarnings :: ([Warning])
              _leftPatternIself :: Pattern
              _leftPatternIunboundNames :: Names
              _operatorIself :: Name
              _rightPatternIbeta :: Tp
              _rightPatternIbetaUnique :: Int
              _rightPatternIconstraints :: ConstraintSet
              _rightPatternIelements :: (  [PatternElement]        )
              _rightPatternIenvironment :: PatternAssumptions
              _rightPatternIinfoTree :: InfoTree
              _rightPatternIpatVarNames :: Names
              _rightPatternIpatternMatchWarnings :: ([Warning])
              _rightPatternIself :: Pattern
              _rightPatternIunboundNames :: Names
              _lhsOnumberOfPatterns =
                  2
              _lhsOenvironment =
                  _leftPatternIenvironment `M.union` _rightPatternIenvironment
              _lhsObetas =
                  [_leftPatternIbeta,_rightPatternIbeta]
              _lhsOname =
                  _operatorIself
              _constraints =
                  Node [ _leftPatternIconstraints
                       , _rightPatternIconstraints
                       ]
              _lhsOinfoTrees =
                  [_leftPatternIinfoTree, _rightPatternIinfoTree]
              _lhsOelements =
                  _leftPatternIelements ++ _rightPatternIelements
              _lhsOargcount =
                  2
              _lhsOpatVarNames =
                  _leftPatternIpatVarNames ++ _rightPatternIpatVarNames
              _lhsOunboundNames =
                  _leftPatternIunboundNames ++ _rightPatternIunboundNames
              _self =
                  LeftHandSide_Infix _rangeIself _leftPatternIself _operatorIself _rightPatternIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _rightPatternIbetaUnique
              _lhsOconstraints =
                  _constraints
              _lhsOpatternMatchWarnings =
                  _rightPatternIpatternMatchWarnings
              _leftPatternObetaUnique =
                  _lhsIbetaUnique
              _leftPatternOimportEnvironment =
                  _lhsIimportEnvironment
              _leftPatternOmonos =
                  _lhsImonos
              _leftPatternOnamesInScope =
                  _lhsInamesInScope
              _leftPatternOparentTree =
                  _lhsIparentTree
              _leftPatternOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _rightPatternObetaUnique =
                  _leftPatternIbetaUnique
              _rightPatternOimportEnvironment =
                  _lhsIimportEnvironment
              _rightPatternOmonos =
                  _lhsImonos
              _rightPatternOnamesInScope =
                  _lhsInamesInScope
              _rightPatternOparentTree =
                  _lhsIparentTree
              _rightPatternOpatternMatchWarnings =
                  _leftPatternIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _leftPatternIbeta,_leftPatternIbetaUnique,_leftPatternIconstraints,_leftPatternIelements,_leftPatternIenvironment,_leftPatternIinfoTree,_leftPatternIpatVarNames,_leftPatternIpatternMatchWarnings,_leftPatternIself,_leftPatternIunboundNames) =
                  (leftPattern_ _leftPatternObetaUnique _leftPatternOimportEnvironment _leftPatternOmonos _leftPatternOnamesInScope _leftPatternOparentTree _leftPatternOpatternMatchWarnings )
              ( _operatorIself) =
                  (operator_ )
              ( _rightPatternIbeta,_rightPatternIbetaUnique,_rightPatternIconstraints,_rightPatternIelements,_rightPatternIenvironment,_rightPatternIinfoTree,_rightPatternIpatVarNames,_rightPatternIpatternMatchWarnings,_rightPatternIself,_rightPatternIunboundNames) =
                  (rightPattern_ _rightPatternObetaUnique _rightPatternOimportEnvironment _rightPatternOmonos _rightPatternOnamesInScope _rightPatternOparentTree _rightPatternOpatternMatchWarnings )
          in  ( _lhsOargcount,_lhsObetaUnique,_lhsObetas,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTrees,_lhsOname,_lhsOnumberOfPatterns,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_LeftHandSide_Parenthesized :: T_Range  ->
                                  T_LeftHandSide  ->
                                  T_Patterns  ->
                                  T_LeftHandSide 
sem_LeftHandSide_Parenthesized range_ lefthandside_ patterns_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsOnumberOfPatterns :: Int
              _lhsOenvironment :: PatternAssumptions
              _lhsObetas :: Tps
              _lhsOinfoTrees :: InfoTrees
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: LeftHandSide
              _lhsOargcount :: Int
              _lhsObetaUnique :: Int
              _lhsOconstraints :: ConstraintSet
              _lhsOelements :: (  [PatternElement]        )
              _lhsOname :: Name
              _lhsOpatternMatchWarnings :: ([Warning])
              _lefthandsideObetaUnique :: Int
              _lefthandsideOimportEnvironment :: ImportEnvironment
              _lefthandsideOmonos :: Monos
              _lefthandsideOnamesInScope :: Names
              _lefthandsideOparentTree :: InfoTree
              _lefthandsideOpatternMatchWarnings :: ([Warning])
              _patternsObetaUnique :: Int
              _patternsOimportEnvironment :: ImportEnvironment
              _patternsOmonos :: Monos
              _patternsOnamesInScope :: Names
              _patternsOparentTree :: InfoTree
              _patternsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _lefthandsideIargcount :: Int
              _lefthandsideIbetaUnique :: Int
              _lefthandsideIbetas :: Tps
              _lefthandsideIconstraints :: ConstraintSet
              _lefthandsideIelements :: (  [PatternElement]        )
              _lefthandsideIenvironment :: PatternAssumptions
              _lefthandsideIinfoTrees :: InfoTrees
              _lefthandsideIname :: Name
              _lefthandsideInumberOfPatterns :: Int
              _lefthandsideIpatVarNames :: Names
              _lefthandsideIpatternMatchWarnings :: ([Warning])
              _lefthandsideIself :: LeftHandSide
              _lefthandsideIunboundNames :: Names
              _patternsIbetaUnique :: Int
              _patternsIbetas :: Tps
              _patternsIconstraintslist :: ConstraintSets
              _patternsIelementss :: ([ [PatternElement]       ])
              _patternsIenvironment :: PatternAssumptions
              _patternsIinfoTrees :: InfoTrees
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIpatternMatchWarnings :: ([Warning])
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _lhsOnumberOfPatterns =
                  _lefthandsideInumberOfPatterns + _patternsInumberOfPatterns
              _lhsOenvironment =
                  _lefthandsideIenvironment `M.union` _patternsIenvironment
              _lhsObetas =
                  _lefthandsideIbetas ++ _patternsIbetas
              _constraints =
                  Node ( _lefthandsideIconstraints : _patternsIconstraintslist )
              _lhsOinfoTrees =
                  _lefthandsideIinfoTrees ++ _patternsIinfoTrees
              _lhsOpatVarNames =
                  _lefthandsideIpatVarNames ++ _patternsIpatVarNames
              _lhsOunboundNames =
                  _lefthandsideIunboundNames ++ _patternsIunboundNames
              _self =
                  LeftHandSide_Parenthesized _rangeIself _lefthandsideIself _patternsIself
              _lhsOself =
                  _self
              _lhsOargcount =
                  _lefthandsideIargcount
              _lhsObetaUnique =
                  _patternsIbetaUnique
              _lhsOconstraints =
                  _constraints
              _lhsOelements =
                  _lefthandsideIelements
              _lhsOname =
                  _lefthandsideIname
              _lhsOpatternMatchWarnings =
                  _patternsIpatternMatchWarnings
              _lefthandsideObetaUnique =
                  _lhsIbetaUnique
              _lefthandsideOimportEnvironment =
                  _lhsIimportEnvironment
              _lefthandsideOmonos =
                  _lhsImonos
              _lefthandsideOnamesInScope =
                  _lhsInamesInScope
              _lefthandsideOparentTree =
                  _lhsIparentTree
              _lefthandsideOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _patternsObetaUnique =
                  _lefthandsideIbetaUnique
              _patternsOimportEnvironment =
                  _lhsIimportEnvironment
              _patternsOmonos =
                  _lhsImonos
              _patternsOnamesInScope =
                  _lhsInamesInScope
              _patternsOparentTree =
                  _lhsIparentTree
              _patternsOpatternMatchWarnings =
                  _lefthandsideIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _lefthandsideIargcount,_lefthandsideIbetaUnique,_lefthandsideIbetas,_lefthandsideIconstraints,_lefthandsideIelements,_lefthandsideIenvironment,_lefthandsideIinfoTrees,_lefthandsideIname,_lefthandsideInumberOfPatterns,_lefthandsideIpatVarNames,_lefthandsideIpatternMatchWarnings,_lefthandsideIself,_lefthandsideIunboundNames) =
                  (lefthandside_ _lefthandsideObetaUnique _lefthandsideOimportEnvironment _lefthandsideOmonos _lefthandsideOnamesInScope _lefthandsideOparentTree _lefthandsideOpatternMatchWarnings )
              ( _patternsIbetaUnique,_patternsIbetas,_patternsIconstraintslist,_patternsIelementss,_patternsIenvironment,_patternsIinfoTrees,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIpatternMatchWarnings,_patternsIself,_patternsIunboundNames) =
                  (patterns_ _patternsObetaUnique _patternsOimportEnvironment _patternsOmonos _patternsOnamesInScope _patternsOparentTree _patternsOpatternMatchWarnings )
          in  ( _lhsOargcount,_lhsObetaUnique,_lhsObetas,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTrees,_lhsOname,_lhsOnumberOfPatterns,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
-- Literal -----------------------------------------------------
-- cata
sem_Literal :: Literal  ->
               T_Literal 
sem_Literal (Literal_Char _range _value )  =
    (sem_Literal_Char (sem_Range _range ) _value )
sem_Literal (Literal_Float _range _value )  =
    (sem_Literal_Float (sem_Range _range ) _value )
sem_Literal (Literal_Int _range _value )  =
    (sem_Literal_Int (sem_Range _range ) _value )
sem_Literal (Literal_String _range _value )  =
    (sem_Literal_String (sem_Range _range ) _value )
-- semantic domain
type T_Literal  = ( (  [PatternElement]        ),Tp,Literal)
sem_Literal_Char :: T_Range  ->
                    String ->
                    T_Literal 
sem_Literal_Char range_ value_  =
    (let _lhsOliteralType :: Tp
         _lhsOelements :: (  [PatternElement]        )
         _lhsOself :: Literal
         _rangeIself :: Range
         _lhsOliteralType =
             charType
         _lhsOelements =
             [InfiniteElement value_]
         _self =
             Literal_Char _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOelements,_lhsOliteralType,_lhsOself))
sem_Literal_Float :: T_Range  ->
                     String ->
                     T_Literal 
sem_Literal_Float range_ value_  =
    (let _lhsOliteralType :: Tp
         _lhsOelements :: (  [PatternElement]        )
         _lhsOself :: Literal
         _rangeIself :: Range
         _lhsOliteralType =
             floatType
         _lhsOelements =
             [InfiniteElement value_]
         _self =
             Literal_Float _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOelements,_lhsOliteralType,_lhsOself))
sem_Literal_Int :: T_Range  ->
                   String ->
                   T_Literal 
sem_Literal_Int range_ value_  =
    (let _lhsOliteralType :: Tp
         _lhsOelements :: (  [PatternElement]        )
         _lhsOself :: Literal
         _rangeIself :: Range
         _lhsOliteralType =
             intType
         _lhsOelements =
             [InfiniteElement value_]
         _self =
             Literal_Int _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOelements,_lhsOliteralType,_lhsOself))
sem_Literal_String :: T_Range  ->
                      String ->
                      T_Literal 
sem_Literal_String range_ value_  =
    (let _lhsOliteralType :: Tp
         _lhsOelements :: (  [PatternElement]        )
         _lhsOself :: Literal
         _rangeIself :: Range
         _lhsOliteralType =
             stringType
         _lhsOelements =
             stringPat value_
         _self =
             Literal_String _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
     in  ( _lhsOelements,_lhsOliteralType,_lhsOself))
-- MaybeDeclarations -------------------------------------------
-- cata
sem_MaybeDeclarations :: MaybeDeclarations  ->
                         T_MaybeDeclarations 
sem_MaybeDeclarations (MaybeDeclarations_Just _declarations )  =
    (sem_MaybeDeclarations_Just (sem_Declarations _declarations ) )
sem_MaybeDeclarations (MaybeDeclarations_Nothing )  =
    (sem_MaybeDeclarations_Nothing )
-- semantic domain
type T_MaybeDeclarations  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                            (M.Map NameWithRange TpScheme) ->
                            Assumptions ->
                            Predicates ->
                            Int ->
                            ClassEnvironment ->
                            TypeErrors ->
                            Warnings ->
                            ConstraintSet ->
                            Int ->
                            DictionaryEnvironment ->
                            ImportEnvironment ->
                            (IO ()) ->
                            Monos ->
                            Names ->
                            OrderedTypeSynonyms ->
                            InfoTree ->
                            ([Warning]) ->
                            FixpointSubstitution ->
                            (M.Map Int (Scheme Predicates)) ->
                            Names ->
                            Int ->
                            ( Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,Names,DictionaryEnvironment,InfoTrees,(M.Map NameWithRange TpScheme),(IO ()),Names,([Warning]),MaybeDeclarations,Names,Int)
sem_MaybeDeclarations_Just :: T_Declarations  ->
                              T_MaybeDeclarations 
sem_MaybeDeclarations_Just declarations_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk ->
         (let _declarationsObindingGroups :: BindingGroups
              _lhsOassumptions :: Assumptions
              _lhsOconstraints :: ConstraintSet
              _lhsObetaUnique :: Int
              _lhsOcollectWarnings :: Warnings
              _lhsOcollectErrors :: TypeErrors
              _lhsOlocalTypes :: (M.Map NameWithRange TpScheme)
              _declarationsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _lhsOinfoTrees :: InfoTrees
              _declarationsOparentTree :: InfoTree
              _lhsOunboundNames :: Names
              _lhsOdeclVarNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: MaybeDeclarations
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _declarationsOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _declarationsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _declarationsOavailablePredicates :: Predicates
              _declarationsObetaUnique :: Int
              _declarationsOclassEnvironment :: ClassEnvironment
              _declarationsOcollectErrors :: TypeErrors
              _declarationsOcollectWarnings :: Warnings
              _declarationsOcurrentChunk :: Int
              _declarationsOdictionaryEnvironment :: DictionaryEnvironment
              _declarationsOimportEnvironment :: ImportEnvironment
              _declarationsOinheritedBDG :: InheritedBDG
              _declarationsOmatchIO :: (IO ())
              _declarationsOmonos :: Monos
              _declarationsOnamesInScope :: Names
              _declarationsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _declarationsOpatternMatchWarnings :: ([Warning])
              _declarationsOsubstitution :: FixpointSubstitution
              _declarationsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _declarationsOuniqueChunk :: Int
              _declarationsIbetaUnique :: Int
              _declarationsIbindingGroups :: BindingGroups
              _declarationsIcollectErrors :: TypeErrors
              _declarationsIcollectInstances :: ([(Name, Instance)])
              _declarationsIcollectWarnings :: Warnings
              _declarationsIdeclVarNames :: Names
              _declarationsIdictionaryEnvironment :: DictionaryEnvironment
              _declarationsIinfoTrees :: InfoTrees
              _declarationsImatchIO :: (IO ())
              _declarationsIpatternMatchWarnings :: ([Warning])
              _declarationsIrestrictedNames :: Names
              _declarationsIself :: Declarations
              _declarationsIsimplePatNames :: Names
              _declarationsItypeSignatures :: TypeEnvironment
              _declarationsIunboundNames :: Names
              _declarationsIuniqueChunk :: Int
              _declarationsObindingGroups =
                  []
              __tup37 =
                  let inputBDG   = (False, _lhsIcurrentChunk, _declarationsIuniqueChunk, _lhsImonos, _declarationsItypeSignatures, mybdggroup, _declarationsIbetaUnique)
                      mybdggroup = Just (_lhsIassumptions, [_lhsIconstraints])
                  in performBindingGroup inputBDG _declarationsIbindingGroups
              (_lhsOassumptions,_,_,_,_,_) =
                  __tup37
              (_,_lhsOconstraints,_,_,_,_) =
                  __tup37
              (_,_,_inheritedBDG,_,_,_) =
                  __tup37
              (_,_,_,_chunkNr,_,_) =
                  __tup37
              (_,_,_,_,_lhsObetaUnique,_) =
                  __tup37
              (_,_,_,_,_,_implicitsFM) =
                  __tup37
              _inferredTypes =
                  findInferredTypes _lhsItypeschemeMap _implicitsFM
              _lhsOcollectWarnings =
                  missingTypeSignature False _declarationsIsimplePatNames _inferredTypes
                  ++ _declarationsIcollectWarnings
              _lhsOcollectErrors =
                  restrictedNameErrors _inferredTypes _declarationsIrestrictedNames
                  ++ _declarationsIcollectErrors
              _lhsOlocalTypes =
                  makeLocalTypeEnv (_declarationsItypeSignatures `M.union` _inferredTypes) _declarationsIbindingGroups
              _declarationsOtypeSignatures =
                  M.empty
              _lhsOuniqueChunk =
                  _chunkNr
              _declInfo =
                  LocalInfo { self = UHA_Decls _declarationsIself
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _theNode =
                  node _lhsIparentTree _declInfo _declarationsIinfoTrees
              _lhsOinfoTrees =
                  [_theNode]
              _declarationsOparentTree =
                  _theNode
              __tup38 =
                  internalError "PartialSyntax.ag" "n/a" "toplevel MaybeDeclaration"
              (_collectTypeConstructors,_,_,_,_,_) =
                  __tup38
              (_,_collectValueConstructors,_,_,_,_) =
                  __tup38
              (_,_,_collectTypeSynonyms,_,_,_) =
                  __tup38
              (_,_,_,_collectConstructorEnv,_,_) =
                  __tup38
              (_,_,_,_,_derivedFunctions,_) =
                  __tup38
              (_,_,_,_,_,_operatorFixities) =
                  __tup38
              __tup39 =
                  changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup39
              (_,_unboundNames,_) =
                  __tup39
              (_,_,_scopeInfo) =
                  __tup39
              _lhsOunboundNames =
                  _unboundNames
              _lhsOdeclVarNames =
                  _declarationsIdeclVarNames
              _lhsOcollectInstances =
                  _declarationsIcollectInstances
              _self =
                  MaybeDeclarations_Just _declarationsIself
              _lhsOself =
                  _self
              _lhsOdictionaryEnvironment =
                  _declarationsIdictionaryEnvironment
              _lhsOmatchIO =
                  _declarationsImatchIO
              _lhsOnamesInScope =
                  _namesInScope
              _lhsOpatternMatchWarnings =
                  _declarationsIpatternMatchWarnings
              _declarationsOallPatterns =
                  _lhsIallPatterns
              _declarationsOallTypeSchemes =
                  _lhsIallTypeSchemes
              _declarationsOavailablePredicates =
                  _lhsIavailablePredicates
              _declarationsObetaUnique =
                  _lhsIbetaUnique
              _declarationsOclassEnvironment =
                  _lhsIclassEnvironment
              _declarationsOcollectErrors =
                  _lhsIcollectErrors
              _declarationsOcollectWarnings =
                  _lhsIcollectWarnings
              _declarationsOcurrentChunk =
                  _lhsIcurrentChunk
              _declarationsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _declarationsOimportEnvironment =
                  _lhsIimportEnvironment
              _declarationsOinheritedBDG =
                  _inheritedBDG
              _declarationsOmatchIO =
                  _lhsImatchIO
              _declarationsOmonos =
                  _lhsImonos
              _declarationsOnamesInScope =
                  _namesInScope
              _declarationsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _declarationsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _declarationsOsubstitution =
                  _lhsIsubstitution
              _declarationsOtypeschemeMap =
                  _lhsItypeschemeMap
              _declarationsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _declarationsIbetaUnique,_declarationsIbindingGroups,_declarationsIcollectErrors,_declarationsIcollectInstances,_declarationsIcollectWarnings,_declarationsIdeclVarNames,_declarationsIdictionaryEnvironment,_declarationsIinfoTrees,_declarationsImatchIO,_declarationsIpatternMatchWarnings,_declarationsIrestrictedNames,_declarationsIself,_declarationsIsimplePatNames,_declarationsItypeSignatures,_declarationsIunboundNames,_declarationsIuniqueChunk) =
                  (declarations_ _declarationsOallPatterns _declarationsOallTypeSchemes _declarationsOavailablePredicates _declarationsObetaUnique _declarationsObindingGroups _declarationsOclassEnvironment _declarationsOcollectErrors _declarationsOcollectWarnings _declarationsOcurrentChunk _declarationsOdictionaryEnvironment _declarationsOimportEnvironment _declarationsOinheritedBDG _declarationsOmatchIO _declarationsOmonos _declarationsOnamesInScope _declarationsOorderedTypeSynonyms _declarationsOparentTree _declarationsOpatternMatchWarnings _declarationsOsubstitution _declarationsOtypeSignatures _declarationsOtypeschemeMap _declarationsOuniqueChunk )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOlocalTypes,_lhsOmatchIO,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_MaybeDeclarations_Nothing :: T_MaybeDeclarations 
sem_MaybeDeclarations_Nothing  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk ->
         (let _lhsOlocalTypes :: (M.Map NameWithRange TpScheme)
              _lhsOinfoTrees :: InfoTrees
              _lhsOdeclVarNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: MaybeDeclarations
              _lhsOassumptions :: Assumptions
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOunboundNames :: Names
              _lhsOuniqueChunk :: Int
              _lhsOlocalTypes =
                  M.empty
              _lhsOinfoTrees =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOcollectInstances =
                  []
              _self =
                  MaybeDeclarations_Nothing
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _lhsIassumptions
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOconstraints =
                  _lhsIconstraints
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOunboundNames =
                  _lhsIunboundNames
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdeclVarNames,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOlocalTypes,_lhsOmatchIO,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk)))
-- MaybeExports ------------------------------------------------
-- cata
sem_MaybeExports :: MaybeExports  ->
                    T_MaybeExports 
sem_MaybeExports (MaybeExports_Just _exports )  =
    (sem_MaybeExports_Just (sem_Exports _exports ) )
sem_MaybeExports (MaybeExports_Nothing )  =
    (sem_MaybeExports_Nothing )
-- semantic domain
type T_MaybeExports  = ( MaybeExports)
sem_MaybeExports_Just :: T_Exports  ->
                         T_MaybeExports 
sem_MaybeExports_Just exports_  =
    (let _lhsOself :: MaybeExports
         _exportsIself :: Exports
         _self =
             MaybeExports_Just _exportsIself
         _lhsOself =
             _self
         ( _exportsIself) =
             (exports_ )
     in  ( _lhsOself))
sem_MaybeExports_Nothing :: T_MaybeExports 
sem_MaybeExports_Nothing  =
    (let _lhsOself :: MaybeExports
         _self =
             MaybeExports_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MaybeExpression ---------------------------------------------
-- cata
sem_MaybeExpression :: MaybeExpression  ->
                       T_MaybeExpression 
sem_MaybeExpression (MaybeExpression_Just _expression )  =
    (sem_MaybeExpression_Just (sem_Expression _expression ) )
sem_MaybeExpression (MaybeExpression_Nothing )  =
    (sem_MaybeExpression_Nothing )
-- semantic domain
type T_MaybeExpression  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                          (M.Map NameWithRange TpScheme) ->
                          Predicates ->
                          Int ->
                          ClassEnvironment ->
                          TypeErrors ->
                          Warnings ->
                          Int ->
                          DictionaryEnvironment ->
                          ImportEnvironment ->
                          (IO ()) ->
                          Monos ->
                          Names ->
                          OrderedTypeSynonyms ->
                          InfoTree ->
                          ([Warning]) ->
                          FixpointSubstitution ->
                          ([(MaybeExpression, [String])]) ->
                          (M.Map Int (Scheme Predicates)) ->
                          Int ->
                          Int ->
                          ( Assumptions,Tp,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,DictionaryEnvironment,InfoTrees,(IO ()),([Maybe MetaVariableTable]),([Warning]),Bool,MaybeExpression,Names,Int,Int)
sem_MaybeExpression_Just :: T_Expression  ->
                            T_MaybeExpression 
sem_MaybeExpression_Just expression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOsection :: Bool
              _lhsOinfoTrees :: InfoTrees
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: MaybeExpression
              _lhsOassumptions :: Assumptions
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionObetaUnique :: Int
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _lhsOsection =
                  False
              _lhsOinfoTrees =
                  [_expressionIinfoTree]
              __tup40 =
                  match1' match_MaybeExpression_Just _lhsItryPatterns [] [_expressionImatches]
              (_expressionOtryPatterns,_,_,_,_,_) =
                  __tup40
              (_,_lhsOmatches,_,_,_,_) =
                  __tup40
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  MaybeExpression_Just _expressionIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _expressionIassumptions
              _lhsObeta =
                  _expressionIbeta
              _lhsObetaUnique =
                  _expressionIbetaUnique
              _lhsOcollectErrors =
                  _expressionIcollectErrors
              _lhsOcollectWarnings =
                  _expressionIcollectWarnings
              _lhsOconstraints =
                  _expressionIconstraints
              _lhsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _lhsOmatchIO =
                  _expressionImatchIO
              _lhsOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _expressionIuniqueChunk
              _lhsOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionObetaUnique =
                  _lhsIbetaUnique
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _lhsIparentTree
              _expressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOsection,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_MaybeExpression_Nothing :: T_MaybeExpression 
sem_MaybeExpression_Nothing  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItryPatterns
       _lhsItypeschemeMap
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOsection :: Bool
              _lhsObetaUnique :: Int
              _lhsOassumptions :: Assumptions
              _lhsOconstraints :: ConstraintSet
              _lhsOinfoTrees :: InfoTrees
              _lhsOmatches :: ([Maybe MetaVariableTable])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: MaybeExpression
              _lhsObeta :: Tp
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _lhsOsection =
                  True
              _lhsObetaUnique =
                  _lhsIbetaUnique + 1
              _lhsOassumptions =
                  noAssumptions
              _lhsOconstraints =
                  emptyTree
              _beta =
                  TVar _lhsIbetaUnique
              _lhsOinfoTrees =
                  []
              __tup41 =
                  match0' match_MaybeExpression_Nothing _lhsItryPatterns [] []
              (__tup42,_,_,_,_,_) =
                  __tup41
              (_,_lhsOmatches,_,_,_,_) =
                  __tup41
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  MaybeExpression_Nothing
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              _lhsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
          in  ( _lhsOassumptions,_lhsObeta,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOmatches,_lhsOpatternMatchWarnings,_lhsOsection,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
-- MaybeImportSpecification ------------------------------------
-- cata
sem_MaybeImportSpecification :: MaybeImportSpecification  ->
                                T_MaybeImportSpecification 
sem_MaybeImportSpecification (MaybeImportSpecification_Just _importspecification )  =
    (sem_MaybeImportSpecification_Just (sem_ImportSpecification _importspecification ) )
sem_MaybeImportSpecification (MaybeImportSpecification_Nothing )  =
    (sem_MaybeImportSpecification_Nothing )
-- semantic domain
type T_MaybeImportSpecification  = ( MaybeImportSpecification)
sem_MaybeImportSpecification_Just :: T_ImportSpecification  ->
                                     T_MaybeImportSpecification 
sem_MaybeImportSpecification_Just importspecification_  =
    (let _lhsOself :: MaybeImportSpecification
         _importspecificationIself :: ImportSpecification
         _self =
             MaybeImportSpecification_Just _importspecificationIself
         _lhsOself =
             _self
         ( _importspecificationIself) =
             (importspecification_ )
     in  ( _lhsOself))
sem_MaybeImportSpecification_Nothing :: T_MaybeImportSpecification 
sem_MaybeImportSpecification_Nothing  =
    (let _lhsOself :: MaybeImportSpecification
         _self =
             MaybeImportSpecification_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MaybeInt ----------------------------------------------------
-- cata
sem_MaybeInt :: MaybeInt  ->
                T_MaybeInt 
sem_MaybeInt (MaybeInt_Just _int )  =
    (sem_MaybeInt_Just _int )
sem_MaybeInt (MaybeInt_Nothing )  =
    (sem_MaybeInt_Nothing )
-- semantic domain
type T_MaybeInt  = ( MaybeInt)
sem_MaybeInt_Just :: Int ->
                     T_MaybeInt 
sem_MaybeInt_Just int_  =
    (let _lhsOself :: MaybeInt
         _self =
             MaybeInt_Just int_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_MaybeInt_Nothing :: T_MaybeInt 
sem_MaybeInt_Nothing  =
    (let _lhsOself :: MaybeInt
         _self =
             MaybeInt_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MaybeName ---------------------------------------------------
-- cata
sem_MaybeName :: MaybeName  ->
                 T_MaybeName 
sem_MaybeName (MaybeName_Just _name )  =
    (sem_MaybeName_Just (sem_Name _name ) )
sem_MaybeName (MaybeName_Nothing )  =
    (sem_MaybeName_Nothing )
-- semantic domain
type T_MaybeName  = ( MaybeName)
sem_MaybeName_Just :: T_Name  ->
                      T_MaybeName 
sem_MaybeName_Just name_  =
    (let _lhsOself :: MaybeName
         _nameIself :: Name
         _self =
             MaybeName_Just _nameIself
         _lhsOself =
             _self
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_MaybeName_Nothing :: T_MaybeName 
sem_MaybeName_Nothing  =
    (let _lhsOself :: MaybeName
         _self =
             MaybeName_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MaybeNames --------------------------------------------------
-- cata
sem_MaybeNames :: MaybeNames  ->
                  T_MaybeNames 
sem_MaybeNames (MaybeNames_Just _names )  =
    (sem_MaybeNames_Just (sem_Names _names ) )
sem_MaybeNames (MaybeNames_Nothing )  =
    (sem_MaybeNames_Nothing )
-- semantic domain
type T_MaybeNames  = ( MaybeNames)
sem_MaybeNames_Just :: T_Names  ->
                       T_MaybeNames 
sem_MaybeNames_Just names_  =
    (let _lhsOself :: MaybeNames
         _namesIself :: Names
         _self =
             MaybeNames_Just _namesIself
         _lhsOself =
             _self
         ( _namesIself) =
             (names_ )
     in  ( _lhsOself))
sem_MaybeNames_Nothing :: T_MaybeNames 
sem_MaybeNames_Nothing  =
    (let _lhsOself :: MaybeNames
         _self =
             MaybeNames_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Module ------------------------------------------------------
-- cata
sem_Module :: Module  ->
              T_Module 
sem_Module (Module_Module _range _name _exports _body )  =
    (sem_Module_Module (sem_Range _range ) (sem_MaybeName _name ) (sem_MaybeExports _exports ) (sem_Body _body ) )
-- semantic domain
type T_Module  = ImportEnvironment ->
                 ([Option]) ->
                 ( Assumptions,DictionaryEnvironment,InfoTree,LogEntries,Module,(SolveResult ConstraintInfo),TypeEnvironment,TypeErrors,Warnings)
sem_Module_Module :: T_Range  ->
                     T_MaybeName  ->
                     T_MaybeExports  ->
                     T_Body  ->
                     T_Module 
sem_Module_Module range_ name_ exports_ body_  =
    (\ _lhsIimportEnvironment
       _lhsIoptions ->
         (let _lhsOwarnings :: Warnings
              _bodyOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _bodyObetaUnique :: Int
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _bodyOdictionaryEnvironment :: DictionaryEnvironment
              _bodyOclassEnvironment :: ClassEnvironment
              _bodyOavailablePredicates :: Predicates
              _bodyOcollectWarnings :: Warnings
              _bodyOcollectErrors :: TypeErrors
              _bodyOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _bodyOcurrentChunk :: Int
              _bodyOuniqueChunk :: Int
              _bodyOmatchIO :: (IO ())
              _bodyOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _bodyOpatternMatchWarnings :: ([Warning])
              _lhsOself :: Module
              _lhsOassumptions :: Assumptions
              _lhsOinfoTree :: InfoTree
              _lhsOlogEntries :: LogEntries
              _lhsOsolveResult :: (SolveResult ConstraintInfo)
              _lhsOtoplevelTypes :: TypeEnvironment
              _lhsOtypeErrors :: TypeErrors
              _bodyOimportEnvironment :: ImportEnvironment
              _bodyOmonos :: Monos
              _bodyOnamesInScope :: Names
              _bodyOorderedTypeSynonyms :: OrderedTypeSynonyms
              _bodyOsubstitution :: FixpointSubstitution
              _rangeIself :: Range
              _nameIself :: MaybeName
              _exportsIself :: MaybeExports
              _bodyIassumptions :: Assumptions
              _bodyIbetaUnique :: Int
              _bodyIcollectErrors :: TypeErrors
              _bodyIcollectInstances :: ([(Name, Instance)])
              _bodyIcollectWarnings :: Warnings
              _bodyIconstraints :: ConstraintSet
              _bodyIdeclVarNames :: Names
              _bodyIdictionaryEnvironment :: DictionaryEnvironment
              _bodyIinfoTree :: InfoTree
              _bodyImatchIO :: (IO ())
              _bodyIpatternMatchWarnings :: ([Warning])
              _bodyIself :: Body
              _bodyItoplevelTypes :: TypeEnvironment
              _bodyIunboundNames :: Names
              _bodyIuniqueChunk :: Int
              _lhsOwarnings =
                  _warnings     ++ _bodyIpatternMatchWarnings
              (SolveResult _betaUniqueAtTheEnd _substitution _typeschemeMap _ _solveErrors ) =
                  _solveResult
              __tup43 =
                  (selectConstraintSolver _lhsIoptions _lhsIimportEnvironment)
                     _classEnv
                     _orderedTypeSynonyms
                     _bodyIbetaUnique
                     _bodyIconstraints
              (_solveResult,_) =
                  __tup43
              (_,_logEntries) =
                  __tup43
              _orderedTypeSynonyms =
                  getOrderedTypeSynonyms _lhsIimportEnvironment
              _classEnv =
                  foldr (\(n, i) -> insertInstance (show n) i)
                        (createClassEnvironment _lhsIimportEnvironment)
                        _bodyIcollectInstances
              _typeErrors =
                  case makeTypeErrors _classEnv _orderedTypeSynonyms _substitution _solveErrors of
                     []   -> _bodyIcollectErrors
                     errs -> reverse errs
              _warnings =
                  _bodyIcollectWarnings
              _assumptions =
                  let f xs = [ (n, _substitution |-> tp) | (n, tp) <- xs ]
                  in M.map f _bodyIassumptions
              _initialScope =
                  M.keys (typeEnvironment _lhsIimportEnvironment)
              _monos =
                  map TVar _monomorphics
              _monomorphics =
                  ftv (  (M.elems $ valueConstructors _lhsIimportEnvironment)
                      ++ (M.elems $ typeEnvironment   _lhsIimportEnvironment)
                      )
              _bodyOtypeschemeMap =
                  M.fromList (M.assocs _typeschemeMap)
              _bodyObetaUnique =
                  if null _monomorphics
                    then 0
                    else maximum _monomorphics + 1
              _lhsOdictionaryEnvironment =
                  if Overloading `elem` _lhsIoptions
                    then _bodyIdictionaryEnvironment
                    else emptyDictionaryEnvironment
              _bodyOdictionaryEnvironment =
                  emptyDictionaryEnvironment
              _bodyOclassEnvironment =
                  _classEnv
              _bodyOavailablePredicates =
                  []
              _bodyOcollectWarnings =
                  []
              _bodyOcollectErrors =
                  []
              _bodyOallTypeSchemes =
                  M.fromList [ (NameWithRange name, scheme) | (name, scheme) <- M.assocs (typeEnvironment _lhsIimportEnvironment) ]
              _bodyOcurrentChunk =
                  0
              _bodyOuniqueChunk =
                  1
              __tup44 =
                  changeOfScope (_initialScope ++ _bodyIdeclVarNames) _bodyIunboundNames []
              (_namesInScope,_,_) =
                  __tup44
              (_,_unboundNames,_) =
                  __tup44
              (_,_,_scopeInfo) =
                  __tup44
              _bodyOmatchIO =
                  return ()
              _bodyOallPatterns =
                  [ (matchInfo, typingStrategy)
                  | typingStrategy <- typingStrategies _lhsIimportEnvironment
                  , matchInfo      <- matchInformation
                                       _lhsIimportEnvironment
                                       typingStrategy
                  ]
              _bodyOpatternMatchWarnings =
                  []
              _self =
                  Module_Module _rangeIself _nameIself _exportsIself _bodyIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _assumptions
              _lhsOinfoTree =
                  _bodyIinfoTree
              _lhsOlogEntries =
                  _logEntries
              _lhsOsolveResult =
                  _solveResult
              _lhsOtoplevelTypes =
                  _bodyItoplevelTypes
              _lhsOtypeErrors =
                  _typeErrors
              _bodyOimportEnvironment =
                  _lhsIimportEnvironment
              _bodyOmonos =
                  _monos
              _bodyOnamesInScope =
                  _namesInScope
              _bodyOorderedTypeSynonyms =
                  _orderedTypeSynonyms
              _bodyOsubstitution =
                  _substitution
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _exportsIself) =
                  (exports_ )
              ( _bodyIassumptions,_bodyIbetaUnique,_bodyIcollectErrors,_bodyIcollectInstances,_bodyIcollectWarnings,_bodyIconstraints,_bodyIdeclVarNames,_bodyIdictionaryEnvironment,_bodyIinfoTree,_bodyImatchIO,_bodyIpatternMatchWarnings,_bodyIself,_bodyItoplevelTypes,_bodyIunboundNames,_bodyIuniqueChunk) =
                  (body_ _bodyOallPatterns _bodyOallTypeSchemes _bodyOavailablePredicates _bodyObetaUnique _bodyOclassEnvironment _bodyOcollectErrors _bodyOcollectWarnings _bodyOcurrentChunk _bodyOdictionaryEnvironment _bodyOimportEnvironment _bodyOmatchIO _bodyOmonos _bodyOnamesInScope _bodyOorderedTypeSynonyms _bodyOpatternMatchWarnings _bodyOsubstitution _bodyOtypeschemeMap _bodyOuniqueChunk )
          in  ( _lhsOassumptions,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOlogEntries,_lhsOself,_lhsOsolveResult,_lhsOtoplevelTypes,_lhsOtypeErrors,_lhsOwarnings)))
-- Name --------------------------------------------------------
-- cata
sem_Name :: Name  ->
            T_Name 
sem_Name (Name_Identifier _range _module _name )  =
    (sem_Name_Identifier (sem_Range _range ) (sem_Strings _module ) _name )
sem_Name (Name_Operator _range _module _name )  =
    (sem_Name_Operator (sem_Range _range ) (sem_Strings _module ) _name )
sem_Name (Name_Special _range _module _name )  =
    (sem_Name_Special (sem_Range _range ) (sem_Strings _module ) _name )
-- semantic domain
type T_Name  = ( Name)
sem_Name_Identifier :: T_Range  ->
                       T_Strings  ->
                       String ->
                       T_Name 
sem_Name_Identifier range_ module_ name_  =
    (let _lhsOself :: Name
         _rangeIself :: Range
         _moduleIself :: Strings
         _self =
             Name_Identifier _rangeIself _moduleIself name_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _moduleIself) =
             (module_ )
     in  ( _lhsOself))
sem_Name_Operator :: T_Range  ->
                     T_Strings  ->
                     String ->
                     T_Name 
sem_Name_Operator range_ module_ name_  =
    (let _lhsOself :: Name
         _rangeIself :: Range
         _moduleIself :: Strings
         _self =
             Name_Operator _rangeIself _moduleIself name_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _moduleIself) =
             (module_ )
     in  ( _lhsOself))
sem_Name_Special :: T_Range  ->
                    T_Strings  ->
                    String ->
                    T_Name 
sem_Name_Special range_ module_ name_  =
    (let _lhsOself :: Name
         _rangeIself :: Range
         _moduleIself :: Strings
         _self =
             Name_Special _rangeIself _moduleIself name_
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _moduleIself) =
             (module_ )
     in  ( _lhsOself))
-- Names -------------------------------------------------------
-- cata
sem_Names :: Names  ->
             T_Names 
sem_Names list  =
    (Prelude.foldr sem_Names_Cons sem_Names_Nil (Prelude.map sem_Name list) )
-- semantic domain
type T_Names  = ( Names)
sem_Names_Cons :: T_Name  ->
                  T_Names  ->
                  T_Names 
sem_Names_Cons hd_ tl_  =
    (let _lhsOself :: Names
         _hdIself :: Name
         _tlIself :: Names
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Names_Nil :: T_Names 
sem_Names_Nil  =
    (let _lhsOself :: Names
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Pattern -----------------------------------------------------
-- cata
sem_Pattern :: Pattern  ->
               T_Pattern 
sem_Pattern (Pattern_As _range _name _pattern )  =
    (sem_Pattern_As (sem_Range _range ) (sem_Name _name ) (sem_Pattern _pattern ) )
sem_Pattern (Pattern_Constructor _range _name _patterns )  =
    (sem_Pattern_Constructor (sem_Range _range ) (sem_Name _name ) (sem_Patterns _patterns ) )
sem_Pattern (Pattern_InfixConstructor _range _leftPattern _constructorOperator _rightPattern )  =
    (sem_Pattern_InfixConstructor (sem_Range _range ) (sem_Pattern _leftPattern ) (sem_Name _constructorOperator ) (sem_Pattern _rightPattern ) )
sem_Pattern (Pattern_Irrefutable _range _pattern )  =
    (sem_Pattern_Irrefutable (sem_Range _range ) (sem_Pattern _pattern ) )
sem_Pattern (Pattern_List _range _patterns )  =
    (sem_Pattern_List (sem_Range _range ) (sem_Patterns _patterns ) )
sem_Pattern (Pattern_Literal _range _literal )  =
    (sem_Pattern_Literal (sem_Range _range ) (sem_Literal _literal ) )
sem_Pattern (Pattern_Negate _range _literal )  =
    (sem_Pattern_Negate (sem_Range _range ) (sem_Literal _literal ) )
sem_Pattern (Pattern_NegateFloat _range _literal )  =
    (sem_Pattern_NegateFloat (sem_Range _range ) (sem_Literal _literal ) )
sem_Pattern (Pattern_Parenthesized _range _pattern )  =
    (sem_Pattern_Parenthesized (sem_Range _range ) (sem_Pattern _pattern ) )
sem_Pattern (Pattern_Record _range _name _recordPatternBindings )  =
    (sem_Pattern_Record (sem_Range _range ) (sem_Name _name ) (sem_RecordPatternBindings _recordPatternBindings ) )
sem_Pattern (Pattern_Successor _range _name _literal )  =
    (sem_Pattern_Successor (sem_Range _range ) (sem_Name _name ) (sem_Literal _literal ) )
sem_Pattern (Pattern_Tuple _range _patterns )  =
    (sem_Pattern_Tuple (sem_Range _range ) (sem_Patterns _patterns ) )
sem_Pattern (Pattern_Variable _range _name )  =
    (sem_Pattern_Variable (sem_Range _range ) (sem_Name _name ) )
sem_Pattern (Pattern_Wildcard _range )  =
    (sem_Pattern_Wildcard (sem_Range _range ) )
-- semantic domain
type T_Pattern  = Int ->
                  ImportEnvironment ->
                  Monos ->
                  Names ->
                  InfoTree ->
                  ([Warning]) ->
                  ( Tp,Int,ConstraintSet,(  [PatternElement]        ),PatternAssumptions,InfoTree,Names,([Warning]),Pattern,Names)
sem_Pattern_As :: T_Range  ->
                  T_Name  ->
                  T_Pattern  ->
                  T_Pattern 
sem_Pattern_As range_ name_ pattern_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsOenvironment :: PatternAssumptions
              _patternObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOconstraints :: ConstraintSet
              _lhsOelements :: (  [PatternElement]        )
              _lhsOpatternMatchWarnings :: ([Warning])
              _patternOimportEnvironment :: ImportEnvironment
              _patternOmonos :: Monos
              _patternOnamesInScope :: Names
              _patternOparentTree :: InfoTree
              _patternOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _patternIbeta :: Tp
              _patternIbetaUnique :: Int
              _patternIconstraints :: ConstraintSet
              _patternIelements :: (  [PatternElement]        )
              _patternIenvironment :: PatternAssumptions
              _patternIinfoTree :: InfoTree
              _patternIpatVarNames :: Names
              _patternIpatternMatchWarnings :: ([Warning])
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _lhsOenvironment =
                  M.insert _nameIself _beta _patternIenvironment
              _patternObetaUnique =
                  _lhsIbetaUnique + 1
              _constraints =
                  _newcon .>.
                  Node [ Receive _lhsIbetaUnique
                       , _patternIconstraints
                       ]
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  [ (_beta .==. _patternIbeta) _cinfo ]
              _cinfo =
                  specialConstraint "as pattern" _parentTree
                     (self _localInfo, Just $ nameToUHA_Pat _nameIself)
                     []
              _localInfo =
                  LocalInfo { self = UHA_Pat _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo [_patternIinfoTree]
              _lhsOinfoTree =
                  _parentTree
              _lhsOpatVarNames =
                  _nameIself : _patternIpatVarNames
              _lhsOunboundNames =
                  _patternIunboundNames
              _self =
                  Pattern_As _rangeIself _nameIself _patternIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _patternIbetaUnique
              _lhsOconstraints =
                  _constraints
              _lhsOelements =
                  _patternIelements
              _lhsOpatternMatchWarnings =
                  _patternIpatternMatchWarnings
              _patternOimportEnvironment =
                  _lhsIimportEnvironment
              _patternOmonos =
                  _lhsImonos
              _patternOnamesInScope =
                  _lhsInamesInScope
              _patternOparentTree =
                  _parentTree
              _patternOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternIbeta,_patternIbetaUnique,_patternIconstraints,_patternIelements,_patternIenvironment,_patternIinfoTree,_patternIpatVarNames,_patternIpatternMatchWarnings,_patternIself,_patternIunboundNames) =
                  (pattern_ _patternObetaUnique _patternOimportEnvironment _patternOmonos _patternOnamesInScope _patternOparentTree _patternOpatternMatchWarnings )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_Constructor :: T_Range  ->
                           T_Name  ->
                           T_Patterns  ->
                           T_Pattern 
sem_Pattern_Constructor range_ name_ patterns_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _patternsObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _lhsOelements :: (  [PatternElement]        )
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOconstraints :: ConstraintSet
              _lhsOenvironment :: PatternAssumptions
              _lhsOpatternMatchWarnings :: ([Warning])
              _patternsOimportEnvironment :: ImportEnvironment
              _patternsOmonos :: Monos
              _patternsOnamesInScope :: Names
              _patternsOparentTree :: InfoTree
              _patternsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _patternsIbetaUnique :: Int
              _patternsIbetas :: Tps
              _patternsIconstraintslist :: ConstraintSets
              _patternsIelementss :: ([ [PatternElement]       ])
              _patternsIenvironment :: PatternAssumptions
              _patternsIinfoTrees :: InfoTrees
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIpatternMatchWarnings :: ([Warning])
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _patternsObetaUnique =
                  _lhsIbetaUnique + 2
              _constraints =
                  _conApply .>.
                  Node [ listTree _conConstructor
                       , Node _patternsIconstraintslist
                       ]
              _beta =
                  TVar (_lhsIbetaUnique)
              _betaCon =
                  TVar (_lhsIbetaUnique + 1)
              _conApply =
                  [ (_betaCon .==. foldr (.->.) _beta _patternsIbetas)
                    (if _patternsInumberOfPatterns == 0  then _cinfoEmpty else _cinfoApply) ]
              _conConstructor =
                  case M.lookup _nameIself (valueConstructors _lhsIimportEnvironment) of
                     Nothing  -> []
                     Just ctp -> [ (_betaCon .::. ctp) _cinfoConstructor ]
              _cinfoConstructor =
                  resultConstraint "pattern constructor" _parentTree
                     [ FolkloreConstraint, HasTrustFactor 10.0 ]
              _cinfoApply =
                  specialConstraint "pattern application" _parentTree
                     (self _localInfo, Just $ nameToUHA_Pat _nameIself)
                     [ ApplicationEdge False (map attribute _patternsIinfoTrees) ]
              _cinfoEmpty =
                  resultConstraint "pattern constructor" _parentTree
                     [ HasTrustFactor 10.0 ]
              _localInfo =
                  LocalInfo { self = UHA_Pat _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo _patternsIinfoTrees
              _lhsOinfoTree =
                  _parentTree
              _lhsOelements =
                  FiniteElement (getNameName _nameIself) : concat _patternsIelementss
              _lhsOpatVarNames =
                  _patternsIpatVarNames
              _lhsOunboundNames =
                  _patternsIunboundNames
              _self =
                  Pattern_Constructor _rangeIself _nameIself _patternsIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _patternsIbetaUnique
              _lhsOconstraints =
                  _constraints
              _lhsOenvironment =
                  _patternsIenvironment
              _lhsOpatternMatchWarnings =
                  _patternsIpatternMatchWarnings
              _patternsOimportEnvironment =
                  _lhsIimportEnvironment
              _patternsOmonos =
                  _lhsImonos
              _patternsOnamesInScope =
                  _lhsInamesInScope
              _patternsOparentTree =
                  _parentTree
              _patternsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternsIbetaUnique,_patternsIbetas,_patternsIconstraintslist,_patternsIelementss,_patternsIenvironment,_patternsIinfoTrees,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIpatternMatchWarnings,_patternsIself,_patternsIunboundNames) =
                  (patterns_ _patternsObetaUnique _patternsOimportEnvironment _patternsOmonos _patternsOnamesInScope _patternsOparentTree _patternsOpatternMatchWarnings )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_InfixConstructor :: T_Range  ->
                                T_Pattern  ->
                                T_Name  ->
                                T_Pattern  ->
                                T_Pattern 
sem_Pattern_InfixConstructor range_ leftPattern_ constructorOperator_ rightPattern_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsOenvironment :: PatternAssumptions
              _leftPatternObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _lhsOelements :: (  [PatternElement]        )
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOconstraints :: ConstraintSet
              _lhsOpatternMatchWarnings :: ([Warning])
              _leftPatternOimportEnvironment :: ImportEnvironment
              _leftPatternOmonos :: Monos
              _leftPatternOnamesInScope :: Names
              _leftPatternOparentTree :: InfoTree
              _leftPatternOpatternMatchWarnings :: ([Warning])
              _rightPatternObetaUnique :: Int
              _rightPatternOimportEnvironment :: ImportEnvironment
              _rightPatternOmonos :: Monos
              _rightPatternOnamesInScope :: Names
              _rightPatternOparentTree :: InfoTree
              _rightPatternOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _leftPatternIbeta :: Tp
              _leftPatternIbetaUnique :: Int
              _leftPatternIconstraints :: ConstraintSet
              _leftPatternIelements :: (  [PatternElement]        )
              _leftPatternIenvironment :: PatternAssumptions
              _leftPatternIinfoTree :: InfoTree
              _leftPatternIpatVarNames :: Names
              _leftPatternIpatternMatchWarnings :: ([Warning])
              _leftPatternIself :: Pattern
              _leftPatternIunboundNames :: Names
              _constructorOperatorIself :: Name
              _rightPatternIbeta :: Tp
              _rightPatternIbetaUnique :: Int
              _rightPatternIconstraints :: ConstraintSet
              _rightPatternIelements :: (  [PatternElement]        )
              _rightPatternIenvironment :: PatternAssumptions
              _rightPatternIinfoTree :: InfoTree
              _rightPatternIpatVarNames :: Names
              _rightPatternIpatternMatchWarnings :: ([Warning])
              _rightPatternIself :: Pattern
              _rightPatternIunboundNames :: Names
              _lhsOenvironment =
                  _leftPatternIenvironment `M.union` _rightPatternIenvironment
              _leftPatternObetaUnique =
                  _lhsIbetaUnique + 2
              _constraints =
                  _conApply .>.
                  Node [ listTree _conConstructor
                       , _leftPatternIconstraints
                       , _rightPatternIconstraints
                       ]
              _beta =
                  TVar _lhsIbetaUnique
              _betaCon =
                  TVar (_lhsIbetaUnique + 1)
              _conApply =
                  [ (_betaCon .==. _leftPatternIbeta .->. _rightPatternIbeta .->. _beta) _cinfoApply ]
              _conConstructor =
                  case M.lookup _constructorOperatorIself (valueConstructors _lhsIimportEnvironment) of
                     Nothing  -> []
                     Just ctp -> [ (_betaCon .::. ctp) _cinfoConstructor ]
              _cinfoConstructor =
                  variableConstraint "pattern constructor" (nameToUHA_Pat _constructorOperatorIself)
                     [ FolkloreConstraint, HasTrustFactor 10.0 ]
              _cinfoApply =
                  specialConstraint "infix pattern application" _parentTree
                     (self _localInfo, Just $ nameToUHA_Pat  _constructorOperatorIself)
                     [ ApplicationEdge True (map attribute [_leftPatternIinfoTree, _rightPatternIinfoTree]) ]
              _localInfo =
                  LocalInfo { self = UHA_Pat _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo [_leftPatternIinfoTree, _rightPatternIinfoTree]
              _lhsOinfoTree =
                  _parentTree
              _lhsOelements =
                  FiniteElement (getNameName _constructorOperatorIself) : _leftPatternIelements ++ _rightPatternIelements
              _lhsOpatVarNames =
                  _leftPatternIpatVarNames ++ _rightPatternIpatVarNames
              _lhsOunboundNames =
                  _leftPatternIunboundNames ++ _rightPatternIunboundNames
              _self =
                  Pattern_InfixConstructor _rangeIself _leftPatternIself _constructorOperatorIself _rightPatternIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _rightPatternIbetaUnique
              _lhsOconstraints =
                  _constraints
              _lhsOpatternMatchWarnings =
                  _rightPatternIpatternMatchWarnings
              _leftPatternOimportEnvironment =
                  _lhsIimportEnvironment
              _leftPatternOmonos =
                  _lhsImonos
              _leftPatternOnamesInScope =
                  _lhsInamesInScope
              _leftPatternOparentTree =
                  _parentTree
              _leftPatternOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _rightPatternObetaUnique =
                  _leftPatternIbetaUnique
              _rightPatternOimportEnvironment =
                  _lhsIimportEnvironment
              _rightPatternOmonos =
                  _lhsImonos
              _rightPatternOnamesInScope =
                  _lhsInamesInScope
              _rightPatternOparentTree =
                  _parentTree
              _rightPatternOpatternMatchWarnings =
                  _leftPatternIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _leftPatternIbeta,_leftPatternIbetaUnique,_leftPatternIconstraints,_leftPatternIelements,_leftPatternIenvironment,_leftPatternIinfoTree,_leftPatternIpatVarNames,_leftPatternIpatternMatchWarnings,_leftPatternIself,_leftPatternIunboundNames) =
                  (leftPattern_ _leftPatternObetaUnique _leftPatternOimportEnvironment _leftPatternOmonos _leftPatternOnamesInScope _leftPatternOparentTree _leftPatternOpatternMatchWarnings )
              ( _constructorOperatorIself) =
                  (constructorOperator_ )
              ( _rightPatternIbeta,_rightPatternIbetaUnique,_rightPatternIconstraints,_rightPatternIelements,_rightPatternIenvironment,_rightPatternIinfoTree,_rightPatternIpatVarNames,_rightPatternIpatternMatchWarnings,_rightPatternIself,_rightPatternIunboundNames) =
                  (rightPattern_ _rightPatternObetaUnique _rightPatternOimportEnvironment _rightPatternOmonos _rightPatternOnamesInScope _rightPatternOparentTree _rightPatternOpatternMatchWarnings )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_Irrefutable :: T_Range  ->
                           T_Pattern  ->
                           T_Pattern 
sem_Pattern_Irrefutable range_ pattern_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOconstraints :: ConstraintSet
              _lhsOelements :: (  [PatternElement]        )
              _lhsOenvironment :: PatternAssumptions
              _lhsOinfoTree :: InfoTree
              _lhsOpatternMatchWarnings :: ([Warning])
              _patternObetaUnique :: Int
              _patternOimportEnvironment :: ImportEnvironment
              _patternOmonos :: Monos
              _patternOnamesInScope :: Names
              _patternOparentTree :: InfoTree
              _patternOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _patternIbeta :: Tp
              _patternIbetaUnique :: Int
              _patternIconstraints :: ConstraintSet
              _patternIelements :: (  [PatternElement]        )
              _patternIenvironment :: PatternAssumptions
              _patternIinfoTree :: InfoTree
              _patternIpatVarNames :: Names
              _patternIpatternMatchWarnings :: ([Warning])
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _lhsOpatVarNames =
                  _patternIpatVarNames
              _lhsOunboundNames =
                  _patternIunboundNames
              _self =
                  Pattern_Irrefutable _rangeIself _patternIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _patternIbeta
              _lhsObetaUnique =
                  _patternIbetaUnique
              _lhsOconstraints =
                  _patternIconstraints
              _lhsOelements =
                  _patternIelements
              _lhsOenvironment =
                  _patternIenvironment
              _lhsOinfoTree =
                  _patternIinfoTree
              _lhsOpatternMatchWarnings =
                  _patternIpatternMatchWarnings
              _patternObetaUnique =
                  _lhsIbetaUnique
              _patternOimportEnvironment =
                  _lhsIimportEnvironment
              _patternOmonos =
                  _lhsImonos
              _patternOnamesInScope =
                  _lhsInamesInScope
              _patternOparentTree =
                  _lhsIparentTree
              _patternOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternIbeta,_patternIbetaUnique,_patternIconstraints,_patternIelements,_patternIenvironment,_patternIinfoTree,_patternIpatVarNames,_patternIpatternMatchWarnings,_patternIself,_patternIunboundNames) =
                  (pattern_ _patternObetaUnique _patternOimportEnvironment _patternOmonos _patternOnamesInScope _patternOparentTree _patternOpatternMatchWarnings )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_List :: T_Range  ->
                    T_Patterns  ->
                    T_Pattern 
sem_Pattern_List range_ patterns_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _patternsObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _lhsOelements :: (  [PatternElement]        )
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOconstraints :: ConstraintSet
              _lhsOenvironment :: PatternAssumptions
              _lhsOpatternMatchWarnings :: ([Warning])
              _patternsOimportEnvironment :: ImportEnvironment
              _patternsOmonos :: Monos
              _patternsOnamesInScope :: Names
              _patternsOparentTree :: InfoTree
              _patternsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _patternsIbetaUnique :: Int
              _patternsIbetas :: Tps
              _patternsIconstraintslist :: ConstraintSets
              _patternsIelementss :: ([ [PatternElement]       ])
              _patternsIenvironment :: PatternAssumptions
              _patternsIinfoTrees :: InfoTrees
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIpatternMatchWarnings :: ([Warning])
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _patternsObetaUnique =
                  _lhsIbetaUnique + 2
              _constraints =
                  _newcon .>.
                  Node (zipWith3 _zipf _patternsIbetas [0..] _patternsIconstraintslist)
              _beta =
                  TVar _lhsIbetaUnique
              _beta' =
                  TVar (_lhsIbetaUnique + 1)
              _newcon =
                  [ (listType _beta' .==. _beta) _cinfoResult ]
              _zipf =
                  \tp elemNr ctree -> [ (tp .==. _beta') (_cinfoElem elemNr) ] .<. ctree
              _cinfoElem =
                  \elemNr ->
                  childConstraint elemNr "element of pattern list" _parentTree $
                     [ HasTrustFactor 10.0 | length _patternsIconstraintslist < 2 ] ++
                     [ Unifier (head (ftv _beta')) ("pattern list", _localInfo, ordinal False (elemNr+1) ++ " element") ]
              _cinfoResult =
                  resultConstraint "pattern list" _parentTree
                     [ FolkloreConstraint ]
              _localInfo =
                  LocalInfo { self = UHA_Pat _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo _patternsIinfoTrees
              _lhsOinfoTree =
                  _parentTree
              _lhsOelements =
                  listPat _patternsIelementss
              _lhsOpatVarNames =
                  _patternsIpatVarNames
              _lhsOunboundNames =
                  _patternsIunboundNames
              _self =
                  Pattern_List _rangeIself _patternsIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _patternsIbetaUnique
              _lhsOconstraints =
                  _constraints
              _lhsOenvironment =
                  _patternsIenvironment
              _lhsOpatternMatchWarnings =
                  _patternsIpatternMatchWarnings
              _patternsOimportEnvironment =
                  _lhsIimportEnvironment
              _patternsOmonos =
                  _lhsImonos
              _patternsOnamesInScope =
                  _lhsInamesInScope
              _patternsOparentTree =
                  _parentTree
              _patternsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternsIbetaUnique,_patternsIbetas,_patternsIconstraintslist,_patternsIelementss,_patternsIenvironment,_patternsIinfoTrees,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIpatternMatchWarnings,_patternsIself,_patternsIunboundNames) =
                  (patterns_ _patternsObetaUnique _patternsOimportEnvironment _patternsOmonos _patternsOnamesInScope _patternsOparentTree _patternsOpatternMatchWarnings )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_Literal :: T_Range  ->
                       T_Literal  ->
                       T_Pattern 
sem_Pattern_Literal range_ literal_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsObetaUnique :: Int
              _lhsOenvironment :: PatternAssumptions
              _lhsOinfoTree :: InfoTree
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsOconstraints :: ConstraintSet
              _lhsOelements :: (  [PatternElement]        )
              _lhsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _literalIelements :: (  [PatternElement]        )
              _literalIliteralType :: Tp
              _literalIself :: Literal
              _lhsObetaUnique =
                  _lhsIbetaUnique + 1
              _lhsOenvironment =
                  noAssumptions
              _constraints =
                  unitTree ((_literalIliteralType .==. _beta) _cinfo)
              _beta =
                  TVar _lhsIbetaUnique
              _cinfo =
                  resultConstraint "literal pattern" _parentTree
                     [ FolkloreConstraint, HasTrustFactor 10.0 ]
              _localInfo =
                  LocalInfo { self = UHA_Pat _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo []
              _lhsOinfoTree =
                  _parentTree
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_Literal _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsOconstraints =
                  _constraints
              _lhsOelements =
                  _literalIelements
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _literalIelements,_literalIliteralType,_literalIself) =
                  (literal_ )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_Negate :: T_Range  ->
                      T_Literal  ->
                      T_Pattern 
sem_Pattern_Negate range_ literal_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsObetaUnique :: Int
              _lhsOenvironment :: PatternAssumptions
              _lhsOinfoTree :: InfoTree
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsOconstraints :: ConstraintSet
              _lhsOelements :: (  [PatternElement]        )
              _lhsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _literalIelements :: (  [PatternElement]        )
              _literalIliteralType :: Tp
              _literalIself :: Literal
              _lhsObetaUnique =
                  _lhsIbetaUnique + 1
              _lhsOenvironment =
                  noAssumptions
              _constraints =
                  listTree _newcon
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  let standard = makeScheme [] [Predicate "Num" (TVar 0)] (TVar 0 .->. TVar 0)
                      tpscheme = M.findWithDefault standard (nameFromString "negate") (typeEnvironment _lhsIimportEnvironment)
                  in [ (_literalIliteralType .->. _beta .::. tpscheme) _cinfo]
              _cinfo =
                  resultConstraint "pattern negation" _parentTree
                     [ FolkloreConstraint ]
              _localInfo =
                  LocalInfo { self = UHA_Pat _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo []
              _lhsOinfoTree =
                  _parentTree
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_Negate _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsOconstraints =
                  _constraints
              _lhsOelements =
                  _literalIelements
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _literalIelements,_literalIliteralType,_literalIself) =
                  (literal_ )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_NegateFloat :: T_Range  ->
                           T_Literal  ->
                           T_Pattern 
sem_Pattern_NegateFloat range_ literal_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsObetaUnique :: Int
              _lhsOenvironment :: PatternAssumptions
              _lhsOinfoTree :: InfoTree
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsOconstraints :: ConstraintSet
              _lhsOelements :: (  [PatternElement]        )
              _lhsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _literalIelements :: (  [PatternElement]        )
              _literalIliteralType :: Tp
              _literalIself :: Literal
              _lhsObetaUnique =
                  _lhsIbetaUnique + 1
              _lhsOenvironment =
                  noAssumptions
              _constraints =
                  listTree _newcon
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  [ (floatType .==. _beta) _cinfo ]
              _cinfo =
                  resultConstraint "pattern negation" _parentTree
                     [ FolkloreConstraint ]
              _localInfo =
                  LocalInfo { self = UHA_Pat _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo []
              _lhsOinfoTree =
                  _parentTree
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_NegateFloat _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsOconstraints =
                  _constraints
              _lhsOelements =
                  _literalIelements
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _literalIelements,_literalIliteralType,_literalIself) =
                  (literal_ )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_Parenthesized :: T_Range  ->
                             T_Pattern  ->
                             T_Pattern 
sem_Pattern_Parenthesized range_ pattern_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOconstraints :: ConstraintSet
              _lhsOelements :: (  [PatternElement]        )
              _lhsOenvironment :: PatternAssumptions
              _lhsOinfoTree :: InfoTree
              _lhsOpatternMatchWarnings :: ([Warning])
              _patternObetaUnique :: Int
              _patternOimportEnvironment :: ImportEnvironment
              _patternOmonos :: Monos
              _patternOnamesInScope :: Names
              _patternOparentTree :: InfoTree
              _patternOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _patternIbeta :: Tp
              _patternIbetaUnique :: Int
              _patternIconstraints :: ConstraintSet
              _patternIelements :: (  [PatternElement]        )
              _patternIenvironment :: PatternAssumptions
              _patternIinfoTree :: InfoTree
              _patternIpatVarNames :: Names
              _patternIpatternMatchWarnings :: ([Warning])
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _lhsOpatVarNames =
                  _patternIpatVarNames
              _lhsOunboundNames =
                  _patternIunboundNames
              _self =
                  Pattern_Parenthesized _rangeIself _patternIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _patternIbeta
              _lhsObetaUnique =
                  _patternIbetaUnique
              _lhsOconstraints =
                  _patternIconstraints
              _lhsOelements =
                  _patternIelements
              _lhsOenvironment =
                  _patternIenvironment
              _lhsOinfoTree =
                  _patternIinfoTree
              _lhsOpatternMatchWarnings =
                  _patternIpatternMatchWarnings
              _patternObetaUnique =
                  _lhsIbetaUnique
              _patternOimportEnvironment =
                  _lhsIimportEnvironment
              _patternOmonos =
                  _lhsImonos
              _patternOnamesInScope =
                  _lhsInamesInScope
              _patternOparentTree =
                  _lhsIparentTree
              _patternOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternIbeta,_patternIbetaUnique,_patternIconstraints,_patternIelements,_patternIenvironment,_patternIinfoTree,_patternIpatVarNames,_patternIpatternMatchWarnings,_patternIself,_patternIunboundNames) =
                  (pattern_ _patternObetaUnique _patternOimportEnvironment _patternOmonos _patternOnamesInScope _patternOparentTree _patternOpatternMatchWarnings )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_Record :: T_Range  ->
                      T_Name  ->
                      T_RecordPatternBindings  ->
                      T_Pattern 
sem_Pattern_Record range_ name_ recordPatternBindings_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsOelements :: (  [PatternElement]        )
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOconstraints :: ConstraintSet
              _lhsOenvironment :: PatternAssumptions
              _lhsOinfoTree :: InfoTree
              _lhsOpatternMatchWarnings :: ([Warning])
              _recordPatternBindingsOnamesInScope :: Names
              _recordPatternBindingsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _recordPatternBindingsIpatternMatchWarnings :: ([Warning])
              _recordPatternBindingsIself :: RecordPatternBindings
              _recordPatternBindingsIunboundNames :: Names
              _infoTree =
                  globalInfoError
              __tup45 =
                  internalError "PartialSyntax.ag" "n/a" "Pattern.Record"
              (_beta,_,_) =
                  __tup45
              (_,_constraints,_) =
                  __tup45
              (_,_,_environment) =
                  __tup45
              _lhsOelements =
                  pmError "Pattern_Record.elements" "Records are not supported"
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  _recordPatternBindingsIunboundNames
              _self =
                  Pattern_Record _rangeIself _nameIself _recordPatternBindingsIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOconstraints =
                  _constraints
              _lhsOenvironment =
                  _environment
              _lhsOinfoTree =
                  _infoTree
              _lhsOpatternMatchWarnings =
                  _recordPatternBindingsIpatternMatchWarnings
              _recordPatternBindingsOnamesInScope =
                  _lhsInamesInScope
              _recordPatternBindingsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _recordPatternBindingsIpatternMatchWarnings,_recordPatternBindingsIself,_recordPatternBindingsIunboundNames) =
                  (recordPatternBindings_ _recordPatternBindingsOnamesInScope _recordPatternBindingsOpatternMatchWarnings )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_Successor :: T_Range  ->
                         T_Name  ->
                         T_Literal  ->
                         T_Pattern 
sem_Pattern_Successor range_ name_ literal_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsOelements :: (  [PatternElement]        )
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOconstraints :: ConstraintSet
              _lhsOenvironment :: PatternAssumptions
              _lhsOinfoTree :: InfoTree
              _lhsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _literalIelements :: (  [PatternElement]        )
              _literalIliteralType :: Tp
              _literalIself :: Literal
              _infoTree =
                  globalInfoError
              __tup46 =
                  internalError "PartialSyntax.ag" "n/a" "Pattern.Successor"
              (_beta,_,_) =
                  __tup46
              (_,_constraints,_) =
                  __tup46
              (_,_,_environment) =
                  __tup46
              _lhsOelements =
                  pmError "Pattern_Successor.elements" "Successors are not supported"
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_Successor _rangeIself _nameIself _literalIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOconstraints =
                  _constraints
              _lhsOenvironment =
                  _environment
              _lhsOinfoTree =
                  _infoTree
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _literalIelements,_literalIliteralType,_literalIself) =
                  (literal_ )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_Tuple :: T_Range  ->
                     T_Patterns  ->
                     T_Pattern 
sem_Pattern_Tuple range_ patterns_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _patternsObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _lhsOelements :: (  [PatternElement]        )
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsObetaUnique :: Int
              _lhsOconstraints :: ConstraintSet
              _lhsOenvironment :: PatternAssumptions
              _lhsOpatternMatchWarnings :: ([Warning])
              _patternsOimportEnvironment :: ImportEnvironment
              _patternsOmonos :: Monos
              _patternsOnamesInScope :: Names
              _patternsOparentTree :: InfoTree
              _patternsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _patternsIbetaUnique :: Int
              _patternsIbetas :: Tps
              _patternsIconstraintslist :: ConstraintSets
              _patternsIelementss :: ([ [PatternElement]       ])
              _patternsIenvironment :: PatternAssumptions
              _patternsIinfoTrees :: InfoTrees
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIpatternMatchWarnings :: ([Warning])
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _patternsObetaUnique =
                  _lhsIbetaUnique + 1
              _constraints =
                  _newcon .>. Node _patternsIconstraintslist
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  [ (tupleType _patternsIbetas .==. _beta) _cinfo ]
              _cinfo =
                  resultConstraint "pattern tuple" _parentTree
                  [ FolkloreConstraint ]
              _localInfo =
                  LocalInfo { self = UHA_Pat _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo _patternsIinfoTrees
              _lhsOinfoTree =
                  _parentTree
              _lhsOelements =
                  FiniteElement ("(" ++ replicate (length $ tail _patternsIself) ',' ++ ")") : concat _patternsIelementss
              _lhsOpatVarNames =
                  _patternsIpatVarNames
              _lhsOunboundNames =
                  _patternsIunboundNames
              _self =
                  Pattern_Tuple _rangeIself _patternsIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsObetaUnique =
                  _patternsIbetaUnique
              _lhsOconstraints =
                  _constraints
              _lhsOenvironment =
                  _patternsIenvironment
              _lhsOpatternMatchWarnings =
                  _patternsIpatternMatchWarnings
              _patternsOimportEnvironment =
                  _lhsIimportEnvironment
              _patternsOmonos =
                  _lhsImonos
              _patternsOnamesInScope =
                  _lhsInamesInScope
              _patternsOparentTree =
                  _parentTree
              _patternsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternsIbetaUnique,_patternsIbetas,_patternsIconstraintslist,_patternsIelementss,_patternsIenvironment,_patternsIinfoTrees,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIpatternMatchWarnings,_patternsIself,_patternsIunboundNames) =
                  (patterns_ _patternsObetaUnique _patternsOimportEnvironment _patternsOmonos _patternsOnamesInScope _patternsOparentTree _patternsOpatternMatchWarnings )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_Variable :: T_Range  ->
                        T_Name  ->
                        T_Pattern 
sem_Pattern_Variable range_ name_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsObetaUnique :: Int
              _lhsOenvironment :: PatternAssumptions
              _lhsOinfoTree :: InfoTree
              _lhsOpatVarNames :: Names
              _lhsOelements :: (  [PatternElement]        )
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsOconstraints :: ConstraintSet
              _lhsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _lhsObetaUnique =
                  _lhsIbetaUnique + 1
              _lhsOenvironment =
                  M.singleton _nameIself _beta
              _constraints =
                  Receive _lhsIbetaUnique
              _beta =
                  TVar _lhsIbetaUnique
              _localInfo =
                  LocalInfo { self = UHA_Pat _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo []
              _lhsOinfoTree =
                  _parentTree
              _lhsOpatVarNames =
                  [ _nameIself ]
              _lhsOelements =
                  [WildcardElement]
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_Variable _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsOconstraints =
                  _constraints
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Pattern_Wildcard :: T_Range  ->
                        T_Pattern 
sem_Pattern_Wildcard range_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsObetaUnique :: Int
              _lhsOenvironment :: PatternAssumptions
              _lhsOinfoTree :: InfoTree
              _lhsOelements :: (  [PatternElement]        )
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsObeta :: Tp
              _lhsOconstraints :: ConstraintSet
              _lhsOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _lhsObetaUnique =
                  _lhsIbetaUnique + 1
              _lhsOenvironment =
                  noAssumptions
              _constraints =
                  emptyTree
              _beta =
                  TVar _lhsIbetaUnique
              _localInfo =
                  LocalInfo { self = UHA_Pat _self
                            , assignedType = Just _beta
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo []
              _lhsOinfoTree =
                  _parentTree
              _lhsOelements =
                  [WildcardElement]
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_Wildcard _rangeIself
              _lhsOself =
                  _self
              _lhsObeta =
                  _beta
              _lhsOconstraints =
                  _constraints
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsObeta,_lhsObetaUnique,_lhsOconstraints,_lhsOelements,_lhsOenvironment,_lhsOinfoTree,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
-- Patterns ----------------------------------------------------
-- cata
sem_Patterns :: Patterns  ->
                T_Patterns 
sem_Patterns list  =
    (Prelude.foldr sem_Patterns_Cons sem_Patterns_Nil (Prelude.map sem_Pattern list) )
-- semantic domain
type T_Patterns  = Int ->
                   ImportEnvironment ->
                   Monos ->
                   Names ->
                   InfoTree ->
                   ([Warning]) ->
                   ( Int,Tps,ConstraintSets,([ [PatternElement]       ]),PatternAssumptions,InfoTrees,Int,Names,([Warning]),Patterns,Names)
sem_Patterns_Cons :: T_Pattern  ->
                     T_Patterns  ->
                     T_Patterns 
sem_Patterns_Cons hd_ tl_  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsObetas :: Tps
              _lhsOenvironment :: PatternAssumptions
              _lhsOnumberOfPatterns :: Int
              _lhsOconstraintslist :: ConstraintSets
              _lhsOinfoTrees :: InfoTrees
              _lhsOelementss :: ([ [PatternElement]       ])
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Patterns
              _lhsObetaUnique :: Int
              _lhsOpatternMatchWarnings :: ([Warning])
              _hdObetaUnique :: Int
              _hdOimportEnvironment :: ImportEnvironment
              _hdOmonos :: Monos
              _hdOnamesInScope :: Names
              _hdOparentTree :: InfoTree
              _hdOpatternMatchWarnings :: ([Warning])
              _tlObetaUnique :: Int
              _tlOimportEnvironment :: ImportEnvironment
              _tlOmonos :: Monos
              _tlOnamesInScope :: Names
              _tlOparentTree :: InfoTree
              _tlOpatternMatchWarnings :: ([Warning])
              _hdIbeta :: Tp
              _hdIbetaUnique :: Int
              _hdIconstraints :: ConstraintSet
              _hdIelements :: (  [PatternElement]        )
              _hdIenvironment :: PatternAssumptions
              _hdIinfoTree :: InfoTree
              _hdIpatVarNames :: Names
              _hdIpatternMatchWarnings :: ([Warning])
              _hdIself :: Pattern
              _hdIunboundNames :: Names
              _tlIbetaUnique :: Int
              _tlIbetas :: Tps
              _tlIconstraintslist :: ConstraintSets
              _tlIelementss :: ([ [PatternElement]       ])
              _tlIenvironment :: PatternAssumptions
              _tlIinfoTrees :: InfoTrees
              _tlInumberOfPatterns :: Int
              _tlIpatVarNames :: Names
              _tlIpatternMatchWarnings :: ([Warning])
              _tlIself :: Patterns
              _tlIunboundNames :: Names
              _lhsObetas =
                  _hdIbeta : _tlIbetas
              _lhsOenvironment =
                  _hdIenvironment `M.union` _tlIenvironment
              _lhsOnumberOfPatterns =
                  1 + _tlInumberOfPatterns
              _lhsOconstraintslist =
                  _hdIconstraints : _tlIconstraintslist
              _lhsOinfoTrees =
                  _hdIinfoTree : _tlIinfoTrees
              _lhsOelementss =
                  _hdIelements : _tlIelementss
              _lhsOpatVarNames =
                  _hdIpatVarNames ++ _tlIpatVarNames
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _tlIbetaUnique
              _lhsOpatternMatchWarnings =
                  _tlIpatternMatchWarnings
              _hdObetaUnique =
                  _lhsIbetaUnique
              _hdOimportEnvironment =
                  _lhsIimportEnvironment
              _hdOmonos =
                  _lhsImonos
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOparentTree =
                  _lhsIparentTree
              _hdOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _tlObetaUnique =
                  _hdIbetaUnique
              _tlOimportEnvironment =
                  _lhsIimportEnvironment
              _tlOmonos =
                  _lhsImonos
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOparentTree =
                  _lhsIparentTree
              _tlOpatternMatchWarnings =
                  _hdIpatternMatchWarnings
              ( _hdIbeta,_hdIbetaUnique,_hdIconstraints,_hdIelements,_hdIenvironment,_hdIinfoTree,_hdIpatVarNames,_hdIpatternMatchWarnings,_hdIself,_hdIunboundNames) =
                  (hd_ _hdObetaUnique _hdOimportEnvironment _hdOmonos _hdOnamesInScope _hdOparentTree _hdOpatternMatchWarnings )
              ( _tlIbetaUnique,_tlIbetas,_tlIconstraintslist,_tlIelementss,_tlIenvironment,_tlIinfoTrees,_tlInumberOfPatterns,_tlIpatVarNames,_tlIpatternMatchWarnings,_tlIself,_tlIunboundNames) =
                  (tl_ _tlObetaUnique _tlOimportEnvironment _tlOmonos _tlOnamesInScope _tlOparentTree _tlOpatternMatchWarnings )
          in  ( _lhsObetaUnique,_lhsObetas,_lhsOconstraintslist,_lhsOelementss,_lhsOenvironment,_lhsOinfoTrees,_lhsOnumberOfPatterns,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_Patterns_Nil :: T_Patterns 
sem_Patterns_Nil  =
    (\ _lhsIbetaUnique
       _lhsIimportEnvironment
       _lhsImonos
       _lhsInamesInScope
       _lhsIparentTree
       _lhsIpatternMatchWarnings ->
         (let _lhsObetas :: Tps
              _lhsOenvironment :: PatternAssumptions
              _lhsOnumberOfPatterns :: Int
              _lhsOconstraintslist :: ConstraintSets
              _lhsOinfoTrees :: InfoTrees
              _lhsOelementss :: ([ [PatternElement]       ])
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Patterns
              _lhsObetaUnique :: Int
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsObetas =
                  []
              _lhsOenvironment =
                  noAssumptions
              _lhsOnumberOfPatterns =
                  0
              _lhsOconstraintslist =
                  []
              _lhsOinfoTrees =
                  []
              _lhsOelementss =
                  []
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
          in  ( _lhsObetaUnique,_lhsObetas,_lhsOconstraintslist,_lhsOelementss,_lhsOenvironment,_lhsOinfoTrees,_lhsOnumberOfPatterns,_lhsOpatVarNames,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
-- Position ----------------------------------------------------
-- cata
sem_Position :: Position  ->
                T_Position 
sem_Position (Position_Position _filename _line _column )  =
    (sem_Position_Position _filename _line _column )
sem_Position (Position_Unknown )  =
    (sem_Position_Unknown )
-- semantic domain
type T_Position  = ( Position)
sem_Position_Position :: String ->
                         Int ->
                         Int ->
                         T_Position 
sem_Position_Position filename_ line_ column_  =
    (let _lhsOself :: Position
         _self =
             Position_Position filename_ line_ column_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Position_Unknown :: T_Position 
sem_Position_Unknown  =
    (let _lhsOself :: Position
         _self =
             Position_Unknown
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Qualifier ---------------------------------------------------
-- cata
sem_Qualifier :: Qualifier  ->
                 T_Qualifier 
sem_Qualifier (Qualifier_Empty _range )  =
    (sem_Qualifier_Empty (sem_Range _range ) )
sem_Qualifier (Qualifier_Generator _range _pattern _expression )  =
    (sem_Qualifier_Generator (sem_Range _range ) (sem_Pattern _pattern ) (sem_Expression _expression ) )
sem_Qualifier (Qualifier_Guard _range _guard )  =
    (sem_Qualifier_Guard (sem_Range _range ) (sem_Expression _guard ) )
sem_Qualifier (Qualifier_Let _range _declarations )  =
    (sem_Qualifier_Let (sem_Range _range ) (sem_Declarations _declarations ) )
-- semantic domain
type T_Qualifier  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                    (M.Map NameWithRange TpScheme) ->
                    Assumptions ->
                    Predicates ->
                    Int ->
                    ClassEnvironment ->
                    TypeErrors ->
                    Warnings ->
                    ConstraintSet ->
                    Int ->
                    DictionaryEnvironment ->
                    ImportEnvironment ->
                    (IO ()) ->
                    Monos ->
                    Names ->
                    OrderedTypeSynonyms ->
                    InfoTree ->
                    ([Warning]) ->
                    FixpointSubstitution ->
                    (M.Map Int (Scheme Predicates)) ->
                    Names ->
                    Int ->
                    Int ->
                    ( Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,DictionaryEnvironment,InfoTree,(IO ()),Monos,Names,([Warning]),Qualifier,Names,Int,Int)
sem_Qualifier_Empty :: T_Range  ->
                       T_Qualifier 
sem_Qualifier_Empty range_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOinfoTree :: InfoTree
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifier
              _lhsOassumptions :: Assumptions
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOmonos :: Monos
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOunboundNames :: Names
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _rangeIself :: Range
              _localInfo =
                  LocalInfo { self = UHA_Qual _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo []
              _lhsOinfoTree =
                  _parentTree
              _lhsOcollectInstances =
                  []
              _self =
                  Qualifier_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _lhsIassumptions
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOconstraints =
                  _lhsIconstraints
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOmonos =
                  _lhsImonos
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOunboundNames =
                  _lhsIunboundNames
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              _lhsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmonos,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Qualifier_Generator :: T_Range  ->
                           T_Pattern  ->
                           T_Expression  ->
                           T_Qualifier 
sem_Qualifier_Generator range_ pattern_ expression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraints :: ConstraintSet
              _lhsOmonos :: Monos
              _lhsOinfoTree :: InfoTree
              _lhsOnamesInScope :: Names
              _lhsOunboundNames :: Names
              _expressionOnamesInScope :: Names
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifier
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _patternObetaUnique :: Int
              _patternOimportEnvironment :: ImportEnvironment
              _patternOmonos :: Monos
              _patternOnamesInScope :: Names
              _patternOparentTree :: InfoTree
              _patternOpatternMatchWarnings :: ([Warning])
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionObetaUnique :: Int
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _patternIbeta :: Tp
              _patternIbetaUnique :: Int
              _patternIconstraints :: ConstraintSet
              _patternIelements :: (  [PatternElement]        )
              _patternIenvironment :: PatternAssumptions
              _patternIinfoTree :: InfoTree
              _patternIpatVarNames :: Names
              _patternIpatternMatchWarnings :: ([Warning])
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _lhsOassumptions =
                  _assumptions' `combine` _expressionIassumptions
              _lhsOconstraints =
                  _locConstraints
              _lhsOmonos =
                  M.elems _patternIenvironment ++ getMonos _csetBinds ++ _lhsImonos
              _locConstraints =
                  _newcon .>. _csetBinds .>>.
                     Node [ _patternIconstraints
                          , _expressionIconstraints
                          , _lhsIconstraints
                          ]
              __tup47 =
                  (_patternIenvironment .===. _lhsIassumptions) _cinfoBind
              (_csetBinds,_) =
                  __tup47
              (_,_assumptions') =
                  __tup47
              _newcon =
                  [ (_expressionIbeta .==. listType _patternIbeta) _cinfoResult ]
              _cinfoResult =
                  childConstraint 1 "generator" _parentTree
                     []
              _cinfoBind =
                  \name -> variableConstraint "variable" (nameToUHA_Expr name)
                     [ FolkloreConstraint
                     , makeUnifier name "generator" _patternIenvironment _parentTree
                     ]
              _localInfo =
                  LocalInfo { self = UHA_Qual _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo [_patternIinfoTree, _expressionIinfoTree]
              _lhsOinfoTree =
                  _parentTree
              __tup48 =
                  changeOfScope _patternIpatVarNames (_expressionIunboundNames  ++ _lhsIunboundNames)  _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup48
              (_,_unboundNames,_) =
                  __tup48
              (_,_,_scopeInfo) =
                  __tup48
              _lhsOnamesInScope =
                  _namesInScope
              _lhsOunboundNames =
                  _unboundNames
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOtryPatterns =
                  []
              _lhsOpatternMatchWarnings =
                  patternMatchWarnings _lhsIimportEnvironment
                                       _lhsIsubstitution
                                       _patternIbeta
                                       (:[])
                                       [(_patternIelements, False)]
                                       _rangeIself
                                       Nothing
                                       False
                                       []
                                       "generator"
                                       "<-"
                  ++ _expressionIpatternMatchWarnings
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _self =
                  Qualifier_Generator _rangeIself _patternIself _expressionIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _expressionIbetaUnique
              _lhsOcollectErrors =
                  _expressionIcollectErrors
              _lhsOcollectWarnings =
                  _expressionIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _lhsOmatchIO =
                  _expressionImatchIO
              _lhsOuniqueChunk =
                  _expressionIuniqueChunk
              _lhsOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              _patternObetaUnique =
                  _lhsIbetaUnique
              _patternOimportEnvironment =
                  _lhsIimportEnvironment
              _patternOmonos =
                  _lhsImonos
              _patternOnamesInScope =
                  _namesInScope
              _patternOparentTree =
                  _parentTree
              _patternOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionObetaUnique =
                  _patternIbetaUnique
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _parentTree
              _expressionOpatternMatchWarnings =
                  _patternIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _patternIbeta,_patternIbetaUnique,_patternIconstraints,_patternIelements,_patternIenvironment,_patternIinfoTree,_patternIpatVarNames,_patternIpatternMatchWarnings,_patternIself,_patternIunboundNames) =
                  (pattern_ _patternObetaUnique _patternOimportEnvironment _patternOmonos _patternOnamesInScope _patternOparentTree _patternOpatternMatchWarnings )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmonos,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Qualifier_Guard :: T_Range  ->
                       T_Expression  ->
                       T_Qualifier 
sem_Qualifier_Guard range_ guard_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraints :: ConstraintSet
              _lhsOinfoTree :: InfoTree
              _lhsOunboundNames :: Names
              _guardOtryPatterns :: ([(Expression     , [String])])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifier
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOmonos :: Monos
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _guardOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _guardOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _guardOavailablePredicates :: Predicates
              _guardObetaUnique :: Int
              _guardOclassEnvironment :: ClassEnvironment
              _guardOcollectErrors :: TypeErrors
              _guardOcollectWarnings :: Warnings
              _guardOcurrentChunk :: Int
              _guardOdictionaryEnvironment :: DictionaryEnvironment
              _guardOimportEnvironment :: ImportEnvironment
              _guardOmatchIO :: (IO ())
              _guardOmonos :: Monos
              _guardOnamesInScope :: Names
              _guardOorderedTypeSynonyms :: OrderedTypeSynonyms
              _guardOparentTree :: InfoTree
              _guardOpatternMatchWarnings :: ([Warning])
              _guardOsubstitution :: FixpointSubstitution
              _guardOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _guardOuniqueChunk :: Int
              _guardOuniqueSecondRound :: Int
              _rangeIself :: Range
              _guardIassumptions :: Assumptions
              _guardIbeta :: Tp
              _guardIbetaUnique :: Int
              _guardIcollectErrors :: TypeErrors
              _guardIcollectInstances :: ([(Name, Instance)])
              _guardIcollectWarnings :: Warnings
              _guardIconstraints :: ConstraintSet
              _guardIdictionaryEnvironment :: DictionaryEnvironment
              _guardIinfoTree :: InfoTree
              _guardImatchIO :: (IO ())
              _guardImatches :: ([Maybe MetaVariableTable])
              _guardIpatternMatchWarnings :: ([Warning])
              _guardIself :: Expression
              _guardIunboundNames :: Names
              _guardIuniqueChunk :: Int
              _guardIuniqueSecondRound :: Int
              _lhsOassumptions =
                  _lhsIassumptions `combine` _guardIassumptions
              _lhsOconstraints =
                  _locConstraints
              _locConstraints =
                  Node [ _newcon .<. _guardIconstraints
                       , _lhsIconstraints
                       ]
              _newcon =
                  [ (_guardIbeta .==. boolType) _cinfo ]
              _cinfo =
                  orphanConstraint 0 "boolean qualifier" _parentTree
                     []
              _localInfo =
                  LocalInfo { self = UHA_Qual _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo [_guardIinfoTree]
              _lhsOinfoTree =
                  _parentTree
              _lhsOunboundNames =
                  _guardIunboundNames ++ _lhsIunboundNames
              _guardOtryPatterns =
                  []
              _lhsOcollectInstances =
                  _guardIcollectInstances
              _self =
                  Qualifier_Guard _rangeIself _guardIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _guardIbetaUnique
              _lhsOcollectErrors =
                  _guardIcollectErrors
              _lhsOcollectWarnings =
                  _guardIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _guardIdictionaryEnvironment
              _lhsOmatchIO =
                  _guardImatchIO
              _lhsOmonos =
                  _lhsImonos
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOpatternMatchWarnings =
                  _guardIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _guardIuniqueChunk
              _lhsOuniqueSecondRound =
                  _guardIuniqueSecondRound
              _guardOallPatterns =
                  _lhsIallPatterns
              _guardOallTypeSchemes =
                  _lhsIallTypeSchemes
              _guardOavailablePredicates =
                  _lhsIavailablePredicates
              _guardObetaUnique =
                  _lhsIbetaUnique
              _guardOclassEnvironment =
                  _lhsIclassEnvironment
              _guardOcollectErrors =
                  _lhsIcollectErrors
              _guardOcollectWarnings =
                  _lhsIcollectWarnings
              _guardOcurrentChunk =
                  _lhsIcurrentChunk
              _guardOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _guardOimportEnvironment =
                  _lhsIimportEnvironment
              _guardOmatchIO =
                  _lhsImatchIO
              _guardOmonos =
                  _lhsImonos
              _guardOnamesInScope =
                  _lhsInamesInScope
              _guardOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _guardOparentTree =
                  _parentTree
              _guardOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _guardOsubstitution =
                  _lhsIsubstitution
              _guardOtypeschemeMap =
                  _lhsItypeschemeMap
              _guardOuniqueChunk =
                  _lhsIuniqueChunk
              _guardOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _guardIassumptions,_guardIbeta,_guardIbetaUnique,_guardIcollectErrors,_guardIcollectInstances,_guardIcollectWarnings,_guardIconstraints,_guardIdictionaryEnvironment,_guardIinfoTree,_guardImatchIO,_guardImatches,_guardIpatternMatchWarnings,_guardIself,_guardIunboundNames,_guardIuniqueChunk,_guardIuniqueSecondRound) =
                  (guard_ _guardOallPatterns _guardOallTypeSchemes _guardOavailablePredicates _guardObetaUnique _guardOclassEnvironment _guardOcollectErrors _guardOcollectWarnings _guardOcurrentChunk _guardOdictionaryEnvironment _guardOimportEnvironment _guardOmatchIO _guardOmonos _guardOnamesInScope _guardOorderedTypeSynonyms _guardOparentTree _guardOpatternMatchWarnings _guardOsubstitution _guardOtryPatterns _guardOtypeschemeMap _guardOuniqueChunk _guardOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmonos,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Qualifier_Let :: T_Range  ->
                     T_Declarations  ->
                     T_Qualifier 
sem_Qualifier_Let range_ declarations_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _declarationsObindingGroups :: BindingGroups
              _lhsOassumptions :: Assumptions
              _lhsOconstraints :: ConstraintSet
              _lhsObetaUnique :: Int
              _lhsOcollectWarnings :: Warnings
              _lhsOcollectErrors :: TypeErrors
              _declarationsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _lhsOinfoTree :: InfoTree
              _declarationsOparentTree :: InfoTree
              _lhsOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifier
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOmonos :: Monos
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueSecondRound :: Int
              _declarationsOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _declarationsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _declarationsOavailablePredicates :: Predicates
              _declarationsObetaUnique :: Int
              _declarationsOclassEnvironment :: ClassEnvironment
              _declarationsOcollectErrors :: TypeErrors
              _declarationsOcollectWarnings :: Warnings
              _declarationsOcurrentChunk :: Int
              _declarationsOdictionaryEnvironment :: DictionaryEnvironment
              _declarationsOimportEnvironment :: ImportEnvironment
              _declarationsOinheritedBDG :: InheritedBDG
              _declarationsOmatchIO :: (IO ())
              _declarationsOmonos :: Monos
              _declarationsOnamesInScope :: Names
              _declarationsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _declarationsOpatternMatchWarnings :: ([Warning])
              _declarationsOsubstitution :: FixpointSubstitution
              _declarationsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _declarationsOuniqueChunk :: Int
              _rangeIself :: Range
              _declarationsIbetaUnique :: Int
              _declarationsIbindingGroups :: BindingGroups
              _declarationsIcollectErrors :: TypeErrors
              _declarationsIcollectInstances :: ([(Name, Instance)])
              _declarationsIcollectWarnings :: Warnings
              _declarationsIdeclVarNames :: Names
              _declarationsIdictionaryEnvironment :: DictionaryEnvironment
              _declarationsIinfoTrees :: InfoTrees
              _declarationsImatchIO :: (IO ())
              _declarationsIpatternMatchWarnings :: ([Warning])
              _declarationsIrestrictedNames :: Names
              _declarationsIself :: Declarations
              _declarationsIsimplePatNames :: Names
              _declarationsItypeSignatures :: TypeEnvironment
              _declarationsIunboundNames :: Names
              _declarationsIuniqueChunk :: Int
              _declarationsObindingGroups =
                  []
              __tup49 =
                  let inputBDG   = (False, _lhsIcurrentChunk, _declarationsIuniqueChunk, _lhsImonos, _declarationsItypeSignatures, mybdggroup, _declarationsIbetaUnique)
                      mybdggroup = Just (_lhsIassumptions, [_lhsIconstraints])
                  in performBindingGroup inputBDG _declarationsIbindingGroups
              (_lhsOassumptions,_,_,_,_,_) =
                  __tup49
              (_,_lhsOconstraints,_,_,_,_) =
                  __tup49
              (_,_,_inheritedBDG,_,_,_) =
                  __tup49
              (_,_,_,_chunkNr,_,_) =
                  __tup49
              (_,_,_,_,_lhsObetaUnique,_) =
                  __tup49
              (_,_,_,_,_,_implicitsFM) =
                  __tup49
              _inferredTypes =
                  findInferredTypes _lhsItypeschemeMap _implicitsFM
              _lhsOcollectWarnings =
                  missingTypeSignature False _declarationsIsimplePatNames _inferredTypes
                  ++ _declarationsIcollectWarnings
              _lhsOcollectErrors =
                  restrictedNameErrors _inferredTypes _declarationsIrestrictedNames
                  ++ _declarationsIcollectErrors
              _allTypeSchemes =
                  _localTypes `M.union` _lhsIallTypeSchemes
              _localTypes =
                  makeLocalTypeEnv (_declarationsItypeSignatures `M.union` _inferredTypes) _declarationsIbindingGroups
              _declarationsOtypeSignatures =
                  M.empty
              _lhsOuniqueChunk =
                  _chunkNr
              _localInfo =
                  LocalInfo { self = UHA_Qual _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _declInfo =
                  LocalInfo { self = UHA_Decls _declarationsIself
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _thisTree =
                  node _lhsIparentTree _localInfo [_declTree]
              _declTree =
                  node _thisTree _declInfo _declarationsIinfoTrees
              _lhsOinfoTree =
                  _thisTree
              _declarationsOparentTree =
                  _declTree
              __tup50 =
                  internalError "PartialSyntax.ag" "n/a" "toplevel Qualifier"
              (_collectTypeConstructors,_,_,_,_,_) =
                  __tup50
              (_,_collectValueConstructors,_,_,_,_) =
                  __tup50
              (_,_,_collectTypeSynonyms,_,_,_) =
                  __tup50
              (_,_,_,_collectConstructorEnv,_,_) =
                  __tup50
              (_,_,_,_,_derivedFunctions,_) =
                  __tup50
              (_,_,_,_,_,_operatorFixities) =
                  __tup50
              __tup51 =
                  changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup51
              (_,_unboundNames,_) =
                  __tup51
              (_,_,_scopeInfo) =
                  __tup51
              _lhsOunboundNames =
                  _unboundNames
              _lhsOcollectInstances =
                  _declarationsIcollectInstances
              _self =
                  Qualifier_Let _rangeIself _declarationsIself
              _lhsOself =
                  _self
              _lhsOdictionaryEnvironment =
                  _declarationsIdictionaryEnvironment
              _lhsOmatchIO =
                  _declarationsImatchIO
              _lhsOmonos =
                  _lhsImonos
              _lhsOnamesInScope =
                  _namesInScope
              _lhsOpatternMatchWarnings =
                  _declarationsIpatternMatchWarnings
              _lhsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _declarationsOallPatterns =
                  _lhsIallPatterns
              _declarationsOallTypeSchemes =
                  _allTypeSchemes
              _declarationsOavailablePredicates =
                  _lhsIavailablePredicates
              _declarationsObetaUnique =
                  _lhsIbetaUnique
              _declarationsOclassEnvironment =
                  _lhsIclassEnvironment
              _declarationsOcollectErrors =
                  _lhsIcollectErrors
              _declarationsOcollectWarnings =
                  _lhsIcollectWarnings
              _declarationsOcurrentChunk =
                  _lhsIcurrentChunk
              _declarationsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _declarationsOimportEnvironment =
                  _lhsIimportEnvironment
              _declarationsOinheritedBDG =
                  _inheritedBDG
              _declarationsOmatchIO =
                  _lhsImatchIO
              _declarationsOmonos =
                  _lhsImonos
              _declarationsOnamesInScope =
                  _namesInScope
              _declarationsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _declarationsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _declarationsOsubstitution =
                  _lhsIsubstitution
              _declarationsOtypeschemeMap =
                  _lhsItypeschemeMap
              _declarationsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIbetaUnique,_declarationsIbindingGroups,_declarationsIcollectErrors,_declarationsIcollectInstances,_declarationsIcollectWarnings,_declarationsIdeclVarNames,_declarationsIdictionaryEnvironment,_declarationsIinfoTrees,_declarationsImatchIO,_declarationsIpatternMatchWarnings,_declarationsIrestrictedNames,_declarationsIself,_declarationsIsimplePatNames,_declarationsItypeSignatures,_declarationsIunboundNames,_declarationsIuniqueChunk) =
                  (declarations_ _declarationsOallPatterns _declarationsOallTypeSchemes _declarationsOavailablePredicates _declarationsObetaUnique _declarationsObindingGroups _declarationsOclassEnvironment _declarationsOcollectErrors _declarationsOcollectWarnings _declarationsOcurrentChunk _declarationsOdictionaryEnvironment _declarationsOimportEnvironment _declarationsOinheritedBDG _declarationsOmatchIO _declarationsOmonos _declarationsOnamesInScope _declarationsOorderedTypeSynonyms _declarationsOparentTree _declarationsOpatternMatchWarnings _declarationsOsubstitution _declarationsOtypeSignatures _declarationsOtypeschemeMap _declarationsOuniqueChunk )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTree,_lhsOmatchIO,_lhsOmonos,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
-- Qualifiers --------------------------------------------------
-- cata
sem_Qualifiers :: Qualifiers  ->
                  T_Qualifiers 
sem_Qualifiers list  =
    (Prelude.foldr sem_Qualifiers_Cons sem_Qualifiers_Nil (Prelude.map sem_Qualifier list) )
-- semantic domain
type T_Qualifiers  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                     (M.Map NameWithRange TpScheme) ->
                     Assumptions ->
                     Predicates ->
                     Int ->
                     ClassEnvironment ->
                     TypeErrors ->
                     Warnings ->
                     ConstraintSet ->
                     Int ->
                     DictionaryEnvironment ->
                     ImportEnvironment ->
                     (IO ()) ->
                     Monos ->
                     Names ->
                     OrderedTypeSynonyms ->
                     InfoTree ->
                     ([Warning]) ->
                     FixpointSubstitution ->
                     (M.Map Int (Scheme Predicates)) ->
                     Names ->
                     Int ->
                     Int ->
                     ( Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,DictionaryEnvironment,InfoTrees,(IO ()),Monos,Names,([Warning]),Qualifiers,Names,Int,Int)
sem_Qualifiers_Cons :: T_Qualifier  ->
                       T_Qualifiers  ->
                       T_Qualifiers 
sem_Qualifiers_Cons hd_ tl_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraints :: ConstraintSet
              _hdOassumptions :: Assumptions
              _hdOconstraints :: ConstraintSet
              _tlOassumptions :: Assumptions
              _tlOconstraints :: ConstraintSet
              _lhsOinfoTrees :: InfoTrees
              _lhsOunboundNames :: Names
              _tlOunboundNames :: Names
              _hdOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifiers
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOmonos :: Monos
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _hdOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _hdOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _hdOavailablePredicates :: Predicates
              _hdObetaUnique :: Int
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectErrors :: TypeErrors
              _hdOcollectWarnings :: Warnings
              _hdOcurrentChunk :: Int
              _hdOdictionaryEnvironment :: DictionaryEnvironment
              _hdOimportEnvironment :: ImportEnvironment
              _hdOmatchIO :: (IO ())
              _hdOmonos :: Monos
              _hdOnamesInScope :: Names
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOparentTree :: InfoTree
              _hdOpatternMatchWarnings :: ([Warning])
              _hdOsubstitution :: FixpointSubstitution
              _hdOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _hdOuniqueChunk :: Int
              _hdOuniqueSecondRound :: Int
              _tlOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _tlOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _tlOavailablePredicates :: Predicates
              _tlObetaUnique :: Int
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectErrors :: TypeErrors
              _tlOcollectWarnings :: Warnings
              _tlOcurrentChunk :: Int
              _tlOdictionaryEnvironment :: DictionaryEnvironment
              _tlOimportEnvironment :: ImportEnvironment
              _tlOmatchIO :: (IO ())
              _tlOmonos :: Monos
              _tlOnamesInScope :: Names
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOparentTree :: InfoTree
              _tlOpatternMatchWarnings :: ([Warning])
              _tlOsubstitution :: FixpointSubstitution
              _tlOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _tlOuniqueChunk :: Int
              _tlOuniqueSecondRound :: Int
              _hdIassumptions :: Assumptions
              _hdIbetaUnique :: Int
              _hdIcollectErrors :: TypeErrors
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectWarnings :: Warnings
              _hdIconstraints :: ConstraintSet
              _hdIdictionaryEnvironment :: DictionaryEnvironment
              _hdIinfoTree :: InfoTree
              _hdImatchIO :: (IO ())
              _hdImonos :: Monos
              _hdInamesInScope :: Names
              _hdIpatternMatchWarnings :: ([Warning])
              _hdIself :: Qualifier
              _hdIunboundNames :: Names
              _hdIuniqueChunk :: Int
              _hdIuniqueSecondRound :: Int
              _tlIassumptions :: Assumptions
              _tlIbetaUnique :: Int
              _tlIcollectErrors :: TypeErrors
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectWarnings :: Warnings
              _tlIconstraints :: ConstraintSet
              _tlIdictionaryEnvironment :: DictionaryEnvironment
              _tlIinfoTrees :: InfoTrees
              _tlImatchIO :: (IO ())
              _tlImonos :: Monos
              _tlInamesInScope :: Names
              _tlIpatternMatchWarnings :: ([Warning])
              _tlIself :: Qualifiers
              _tlIunboundNames :: Names
              _tlIuniqueChunk :: Int
              _tlIuniqueSecondRound :: Int
              _lhsOassumptions =
                  _hdIassumptions
              _lhsOconstraints =
                  _hdIconstraints
              _hdOassumptions =
                  _tlIassumptions
              _hdOconstraints =
                  _tlIconstraints
              _tlOassumptions =
                  _lhsIassumptions
              _tlOconstraints =
                  _lhsIconstraints
              _lhsOinfoTrees =
                  _hdIinfoTree : _tlIinfoTrees
              _lhsOunboundNames =
                  _hdIunboundNames
              _tlOunboundNames =
                  _lhsIunboundNames
              _hdOunboundNames =
                  _tlIunboundNames
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _tlIbetaUnique
              _lhsOcollectErrors =
                  _tlIcollectErrors
              _lhsOcollectWarnings =
                  _tlIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _tlIdictionaryEnvironment
              _lhsOmatchIO =
                  _tlImatchIO
              _lhsOmonos =
                  _tlImonos
              _lhsOnamesInScope =
                  _tlInamesInScope
              _lhsOpatternMatchWarnings =
                  _tlIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _tlIuniqueChunk
              _lhsOuniqueSecondRound =
                  _tlIuniqueSecondRound
              _hdOallPatterns =
                  _lhsIallPatterns
              _hdOallTypeSchemes =
                  _lhsIallTypeSchemes
              _hdOavailablePredicates =
                  _lhsIavailablePredicates
              _hdObetaUnique =
                  _lhsIbetaUnique
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectErrors =
                  _lhsIcollectErrors
              _hdOcollectWarnings =
                  _lhsIcollectWarnings
              _hdOcurrentChunk =
                  _lhsIcurrentChunk
              _hdOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _hdOimportEnvironment =
                  _lhsIimportEnvironment
              _hdOmatchIO =
                  _lhsImatchIO
              _hdOmonos =
                  _lhsImonos
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOparentTree =
                  _lhsIparentTree
              _hdOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _hdOsubstitution =
                  _lhsIsubstitution
              _hdOtypeschemeMap =
                  _lhsItypeschemeMap
              _hdOuniqueChunk =
                  _lhsIuniqueChunk
              _hdOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _tlOallPatterns =
                  _lhsIallPatterns
              _tlOallTypeSchemes =
                  _lhsIallTypeSchemes
              _tlOavailablePredicates =
                  _lhsIavailablePredicates
              _tlObetaUnique =
                  _hdIbetaUnique
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectErrors =
                  _hdIcollectErrors
              _tlOcollectWarnings =
                  _hdIcollectWarnings
              _tlOcurrentChunk =
                  _lhsIcurrentChunk
              _tlOdictionaryEnvironment =
                  _hdIdictionaryEnvironment
              _tlOimportEnvironment =
                  _lhsIimportEnvironment
              _tlOmatchIO =
                  _hdImatchIO
              _tlOmonos =
                  _hdImonos
              _tlOnamesInScope =
                  _hdInamesInScope
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOparentTree =
                  _lhsIparentTree
              _tlOpatternMatchWarnings =
                  _hdIpatternMatchWarnings
              _tlOsubstitution =
                  _lhsIsubstitution
              _tlOtypeschemeMap =
                  _lhsItypeschemeMap
              _tlOuniqueChunk =
                  _hdIuniqueChunk
              _tlOuniqueSecondRound =
                  _hdIuniqueSecondRound
              ( _hdIassumptions,_hdIbetaUnique,_hdIcollectErrors,_hdIcollectInstances,_hdIcollectWarnings,_hdIconstraints,_hdIdictionaryEnvironment,_hdIinfoTree,_hdImatchIO,_hdImonos,_hdInamesInScope,_hdIpatternMatchWarnings,_hdIself,_hdIunboundNames,_hdIuniqueChunk,_hdIuniqueSecondRound) =
                  (hd_ _hdOallPatterns _hdOallTypeSchemes _hdOassumptions _hdOavailablePredicates _hdObetaUnique _hdOclassEnvironment _hdOcollectErrors _hdOcollectWarnings _hdOconstraints _hdOcurrentChunk _hdOdictionaryEnvironment _hdOimportEnvironment _hdOmatchIO _hdOmonos _hdOnamesInScope _hdOorderedTypeSynonyms _hdOparentTree _hdOpatternMatchWarnings _hdOsubstitution _hdOtypeschemeMap _hdOunboundNames _hdOuniqueChunk _hdOuniqueSecondRound )
              ( _tlIassumptions,_tlIbetaUnique,_tlIcollectErrors,_tlIcollectInstances,_tlIcollectWarnings,_tlIconstraints,_tlIdictionaryEnvironment,_tlIinfoTrees,_tlImatchIO,_tlImonos,_tlInamesInScope,_tlIpatternMatchWarnings,_tlIself,_tlIunboundNames,_tlIuniqueChunk,_tlIuniqueSecondRound) =
                  (tl_ _tlOallPatterns _tlOallTypeSchemes _tlOassumptions _tlOavailablePredicates _tlObetaUnique _tlOclassEnvironment _tlOcollectErrors _tlOcollectWarnings _tlOconstraints _tlOcurrentChunk _tlOdictionaryEnvironment _tlOimportEnvironment _tlOmatchIO _tlOmonos _tlOnamesInScope _tlOorderedTypeSynonyms _tlOparentTree _tlOpatternMatchWarnings _tlOsubstitution _tlOtypeschemeMap _tlOunboundNames _tlOuniqueChunk _tlOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOmonos,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Qualifiers_Nil :: T_Qualifiers 
sem_Qualifiers_Nil  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOinfoTrees :: InfoTrees
              _lhsOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifiers
              _lhsOassumptions :: Assumptions
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOmonos :: Monos
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _lhsOinfoTrees =
                  []
              _lhsOunboundNames =
                  _lhsIunboundNames
              _lhsOcollectInstances =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _lhsIassumptions
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOconstraints =
                  _lhsIconstraints
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOmonos =
                  _lhsImonos
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              _lhsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOinfoTrees,_lhsOmatchIO,_lhsOmonos,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
-- Range -------------------------------------------------------
-- cata
sem_Range :: Range  ->
             T_Range 
sem_Range (Range_Range _start _stop )  =
    (sem_Range_Range (sem_Position _start ) (sem_Position _stop ) )
-- semantic domain
type T_Range  = ( Range)
sem_Range_Range :: T_Position  ->
                   T_Position  ->
                   T_Range 
sem_Range_Range start_ stop_  =
    (let _lhsOself :: Range
         _startIself :: Position
         _stopIself :: Position
         _self =
             Range_Range _startIself _stopIself
         _lhsOself =
             _self
         ( _startIself) =
             (start_ )
         ( _stopIself) =
             (stop_ )
     in  ( _lhsOself))
-- RecordExpressionBinding -------------------------------------
-- cata
sem_RecordExpressionBinding :: RecordExpressionBinding  ->
                               T_RecordExpressionBinding 
sem_RecordExpressionBinding (RecordExpressionBinding_RecordExpressionBinding _range _name _expression )  =
    (sem_RecordExpressionBinding_RecordExpressionBinding (sem_Range _range ) (sem_Name _name ) (sem_Expression _expression ) )
-- semantic domain
type T_RecordExpressionBinding  = (M.Map NameWithRange TpScheme) ->
                                  Predicates ->
                                  ClassEnvironment ->
                                  TypeErrors ->
                                  Warnings ->
                                  Int ->
                                  DictionaryEnvironment ->
                                  ImportEnvironment ->
                                  Names ->
                                  OrderedTypeSynonyms ->
                                  ([Warning]) ->
                                  FixpointSubstitution ->
                                  (M.Map Int (Scheme Predicates)) ->
                                  Int ->
                                  ( TypeErrors,([(Name, Instance)]),Warnings,DictionaryEnvironment,([Warning]),RecordExpressionBinding,Names,Int)
sem_RecordExpressionBinding_RecordExpressionBinding :: T_Range  ->
                                                       T_Name  ->
                                                       T_Expression  ->
                                                       T_RecordExpressionBinding 
sem_RecordExpressionBinding_RecordExpressionBinding range_ name_ expression_  =
    (\ _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: RecordExpressionBinding
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionObetaUnique :: Int
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _nameIself :: Name
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _parentTree =
                  globalInfoError
              __tup52 =
                  internalError "PartialSyntax.ag" "n/a" "RecordExpressionBinding.RecordExpressionBinding"
              (_monos,_,_,_,_,_,_,_,_,_,_) =
                  __tup52
              (_,_constructorenv,_,_,_,_,_,_,_,_,_) =
                  __tup52
              (_,_,_betaUnique,_,_,_,_,_,_,_,_) =
                  __tup52
              (_,_,_,_miscerrors,_,_,_,_,_,_,_) =
                  __tup52
              (_,_,_,_,_warnings,_,_,_,_,_,_) =
                  __tup52
              (_,_,_,_,_,_kindErrors,_,_,_,_,_) =
                  __tup52
              (_,_,_,_,_,_,_valueConstructors,_,_,_,_) =
                  __tup52
              (_,_,_,_,_,_,_,_allValueConstructors,_,_,_) =
                  __tup52
              (_,_,_,_,_,_,_,_,_typeConstructors,_,_) =
                  __tup52
              (_,_,_,_,_,_,_,_,_,_allTypeConstructors,_) =
                  __tup52
              (_,_,_,_,_,_,_,_,_,_,_importEnvironment) =
                  __tup52
              __tup53 =
                  internalError "TS_PatternMatching.ag" "n/a" "RecordExpressionBinding is not supported"
              (_allPatterns,_,_,_) =
                  __tup53
              (_,_tryPatterns,_,_) =
                  __tup53
              (_,_,_matchIO,_) =
                  __tup53
              (_,_,_,_uniqueSecondRound) =
                  __tup53
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  RecordExpressionBinding_RecordExpressionBinding _rangeIself _nameIself _expressionIself
              _lhsOself =
                  _self
              _lhsOcollectErrors =
                  _expressionIcollectErrors
              _lhsOcollectWarnings =
                  _expressionIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _lhsOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _expressionIuniqueChunk
              _expressionOallPatterns =
                  _allPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionObetaUnique =
                  _betaUnique
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _importEnvironment
              _expressionOmatchIO =
                  _matchIO
              _expressionOmonos =
                  _monos
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _parentTree
              _expressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtryPatterns =
                  _tryPatterns
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _uniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
          in  ( _lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdictionaryEnvironment,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk)))
-- RecordExpressionBindings ------------------------------------
-- cata
sem_RecordExpressionBindings :: RecordExpressionBindings  ->
                                T_RecordExpressionBindings 
sem_RecordExpressionBindings list  =
    (Prelude.foldr sem_RecordExpressionBindings_Cons sem_RecordExpressionBindings_Nil (Prelude.map sem_RecordExpressionBinding list) )
-- semantic domain
type T_RecordExpressionBindings  = (M.Map NameWithRange TpScheme) ->
                                   Predicates ->
                                   ClassEnvironment ->
                                   TypeErrors ->
                                   Warnings ->
                                   Int ->
                                   DictionaryEnvironment ->
                                   ImportEnvironment ->
                                   Names ->
                                   OrderedTypeSynonyms ->
                                   ([Warning]) ->
                                   FixpointSubstitution ->
                                   (M.Map Int (Scheme Predicates)) ->
                                   Int ->
                                   ( TypeErrors,([(Name, Instance)]),Warnings,DictionaryEnvironment,([Warning]),RecordExpressionBindings,Names,Int)
sem_RecordExpressionBindings_Cons :: T_RecordExpressionBinding  ->
                                     T_RecordExpressionBindings  ->
                                     T_RecordExpressionBindings 
sem_RecordExpressionBindings_Cons hd_ tl_  =
    (\ _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: RecordExpressionBindings
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _hdOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _hdOavailablePredicates :: Predicates
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectErrors :: TypeErrors
              _hdOcollectWarnings :: Warnings
              _hdOcurrentChunk :: Int
              _hdOdictionaryEnvironment :: DictionaryEnvironment
              _hdOimportEnvironment :: ImportEnvironment
              _hdOnamesInScope :: Names
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOpatternMatchWarnings :: ([Warning])
              _hdOsubstitution :: FixpointSubstitution
              _hdOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _hdOuniqueChunk :: Int
              _tlOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _tlOavailablePredicates :: Predicates
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectErrors :: TypeErrors
              _tlOcollectWarnings :: Warnings
              _tlOcurrentChunk :: Int
              _tlOdictionaryEnvironment :: DictionaryEnvironment
              _tlOimportEnvironment :: ImportEnvironment
              _tlOnamesInScope :: Names
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOpatternMatchWarnings :: ([Warning])
              _tlOsubstitution :: FixpointSubstitution
              _tlOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _tlOuniqueChunk :: Int
              _hdIcollectErrors :: TypeErrors
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectWarnings :: Warnings
              _hdIdictionaryEnvironment :: DictionaryEnvironment
              _hdIpatternMatchWarnings :: ([Warning])
              _hdIself :: RecordExpressionBinding
              _hdIunboundNames :: Names
              _hdIuniqueChunk :: Int
              _tlIcollectErrors :: TypeErrors
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectWarnings :: Warnings
              _tlIdictionaryEnvironment :: DictionaryEnvironment
              _tlIpatternMatchWarnings :: ([Warning])
              _tlIself :: RecordExpressionBindings
              _tlIunboundNames :: Names
              _tlIuniqueChunk :: Int
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcollectErrors =
                  _tlIcollectErrors
              _lhsOcollectWarnings =
                  _tlIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _tlIdictionaryEnvironment
              _lhsOpatternMatchWarnings =
                  _tlIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _tlIuniqueChunk
              _hdOallTypeSchemes =
                  _lhsIallTypeSchemes
              _hdOavailablePredicates =
                  _lhsIavailablePredicates
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectErrors =
                  _lhsIcollectErrors
              _hdOcollectWarnings =
                  _lhsIcollectWarnings
              _hdOcurrentChunk =
                  _lhsIcurrentChunk
              _hdOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _hdOimportEnvironment =
                  _lhsIimportEnvironment
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _hdOsubstitution =
                  _lhsIsubstitution
              _hdOtypeschemeMap =
                  _lhsItypeschemeMap
              _hdOuniqueChunk =
                  _lhsIuniqueChunk
              _tlOallTypeSchemes =
                  _lhsIallTypeSchemes
              _tlOavailablePredicates =
                  _lhsIavailablePredicates
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectErrors =
                  _hdIcollectErrors
              _tlOcollectWarnings =
                  _hdIcollectWarnings
              _tlOcurrentChunk =
                  _lhsIcurrentChunk
              _tlOdictionaryEnvironment =
                  _hdIdictionaryEnvironment
              _tlOimportEnvironment =
                  _lhsIimportEnvironment
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOpatternMatchWarnings =
                  _hdIpatternMatchWarnings
              _tlOsubstitution =
                  _lhsIsubstitution
              _tlOtypeschemeMap =
                  _lhsItypeschemeMap
              _tlOuniqueChunk =
                  _hdIuniqueChunk
              ( _hdIcollectErrors,_hdIcollectInstances,_hdIcollectWarnings,_hdIdictionaryEnvironment,_hdIpatternMatchWarnings,_hdIself,_hdIunboundNames,_hdIuniqueChunk) =
                  (hd_ _hdOallTypeSchemes _hdOavailablePredicates _hdOclassEnvironment _hdOcollectErrors _hdOcollectWarnings _hdOcurrentChunk _hdOdictionaryEnvironment _hdOimportEnvironment _hdOnamesInScope _hdOorderedTypeSynonyms _hdOpatternMatchWarnings _hdOsubstitution _hdOtypeschemeMap _hdOuniqueChunk )
              ( _tlIcollectErrors,_tlIcollectInstances,_tlIcollectWarnings,_tlIdictionaryEnvironment,_tlIpatternMatchWarnings,_tlIself,_tlIunboundNames,_tlIuniqueChunk) =
                  (tl_ _tlOallTypeSchemes _tlOavailablePredicates _tlOclassEnvironment _tlOcollectErrors _tlOcollectWarnings _tlOcurrentChunk _tlOdictionaryEnvironment _tlOimportEnvironment _tlOnamesInScope _tlOorderedTypeSynonyms _tlOpatternMatchWarnings _tlOsubstitution _tlOtypeschemeMap _tlOuniqueChunk )
          in  ( _lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdictionaryEnvironment,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_RecordExpressionBindings_Nil :: T_RecordExpressionBindings 
sem_RecordExpressionBindings_Nil  =
    (\ _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: RecordExpressionBindings
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
          in  ( _lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOdictionaryEnvironment,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk)))
-- RecordPatternBinding ----------------------------------------
-- cata
sem_RecordPatternBinding :: RecordPatternBinding  ->
                            T_RecordPatternBinding 
sem_RecordPatternBinding (RecordPatternBinding_RecordPatternBinding _range _name _pattern )  =
    (sem_RecordPatternBinding_RecordPatternBinding (sem_Range _range ) (sem_Name _name ) (sem_Pattern _pattern ) )
-- semantic domain
type T_RecordPatternBinding  = Names ->
                               ([Warning]) ->
                               ( ([Warning]),RecordPatternBinding,Names)
sem_RecordPatternBinding_RecordPatternBinding :: T_Range  ->
                                                 T_Name  ->
                                                 T_Pattern  ->
                                                 T_RecordPatternBinding 
sem_RecordPatternBinding_RecordPatternBinding range_ name_ pattern_  =
    (\ _lhsInamesInScope
       _lhsIpatternMatchWarnings ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: RecordPatternBinding
              _lhsOpatternMatchWarnings :: ([Warning])
              _patternObetaUnique :: Int
              _patternOimportEnvironment :: ImportEnvironment
              _patternOmonos :: Monos
              _patternOnamesInScope :: Names
              _patternOparentTree :: InfoTree
              _patternOpatternMatchWarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _patternIbeta :: Tp
              _patternIbetaUnique :: Int
              _patternIconstraints :: ConstraintSet
              _patternIelements :: (  [PatternElement]        )
              _patternIenvironment :: PatternAssumptions
              _patternIinfoTree :: InfoTree
              _patternIpatVarNames :: Names
              _patternIpatternMatchWarnings :: ([Warning])
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _parentTree =
                  globalInfoError
              __tup54 =
                  internalError "PartialSyntax.ag" "n/a" "RecordPatternBinding.RecordPatternBinding"
              (_monos,_,_,_,_,_,_,_,_,_) =
                  __tup54
              (_,_constructorenv,_,_,_,_,_,_,_,_) =
                  __tup54
              (_,_,_betaUnique,_,_,_,_,_,_,_) =
                  __tup54
              (_,_,_,_miscerrors,_,_,_,_,_,_) =
                  __tup54
              (_,_,_,_,_warnings,_,_,_,_,_) =
                  __tup54
              (_,_,_,_,_,_valueConstructors,_,_,_,_) =
                  __tup54
              (_,_,_,_,_,_,_allValueConstructors,_,_,_) =
                  __tup54
              (_,_,_,_,_,_,_,_typeConstructors,_,_) =
                  __tup54
              (_,_,_,_,_,_,_,_,_allTypeConstructors,_) =
                  __tup54
              (_,_,_,_,_,_,_,_,_,_importEnvironment) =
                  __tup54
              _lhsOunboundNames =
                  _patternIunboundNames
              _self =
                  RecordPatternBinding_RecordPatternBinding _rangeIself _nameIself _patternIself
              _lhsOself =
                  _self
              _lhsOpatternMatchWarnings =
                  _patternIpatternMatchWarnings
              _patternObetaUnique =
                  _betaUnique
              _patternOimportEnvironment =
                  _importEnvironment
              _patternOmonos =
                  _monos
              _patternOnamesInScope =
                  _lhsInamesInScope
              _patternOparentTree =
                  _parentTree
              _patternOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternIbeta,_patternIbetaUnique,_patternIconstraints,_patternIelements,_patternIenvironment,_patternIinfoTree,_patternIpatVarNames,_patternIpatternMatchWarnings,_patternIself,_patternIunboundNames) =
                  (pattern_ _patternObetaUnique _patternOimportEnvironment _patternOmonos _patternOnamesInScope _patternOparentTree _patternOpatternMatchWarnings )
          in  ( _lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
-- RecordPatternBindings ---------------------------------------
-- cata
sem_RecordPatternBindings :: RecordPatternBindings  ->
                             T_RecordPatternBindings 
sem_RecordPatternBindings list  =
    (Prelude.foldr sem_RecordPatternBindings_Cons sem_RecordPatternBindings_Nil (Prelude.map sem_RecordPatternBinding list) )
-- semantic domain
type T_RecordPatternBindings  = Names ->
                                ([Warning]) ->
                                ( ([Warning]),RecordPatternBindings,Names)
sem_RecordPatternBindings_Cons :: T_RecordPatternBinding  ->
                                  T_RecordPatternBindings  ->
                                  T_RecordPatternBindings 
sem_RecordPatternBindings_Cons hd_ tl_  =
    (\ _lhsInamesInScope
       _lhsIpatternMatchWarnings ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: RecordPatternBindings
              _lhsOpatternMatchWarnings :: ([Warning])
              _hdOnamesInScope :: Names
              _hdOpatternMatchWarnings :: ([Warning])
              _tlOnamesInScope :: Names
              _tlOpatternMatchWarnings :: ([Warning])
              _hdIpatternMatchWarnings :: ([Warning])
              _hdIself :: RecordPatternBinding
              _hdIunboundNames :: Names
              _tlIpatternMatchWarnings :: ([Warning])
              _tlIself :: RecordPatternBindings
              _tlIunboundNames :: Names
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOpatternMatchWarnings =
                  _tlIpatternMatchWarnings
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOpatternMatchWarnings =
                  _hdIpatternMatchWarnings
              ( _hdIpatternMatchWarnings,_hdIself,_hdIunboundNames) =
                  (hd_ _hdOnamesInScope _hdOpatternMatchWarnings )
              ( _tlIpatternMatchWarnings,_tlIself,_tlIunboundNames) =
                  (tl_ _tlOnamesInScope _tlOpatternMatchWarnings )
          in  ( _lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
sem_RecordPatternBindings_Nil :: T_RecordPatternBindings 
sem_RecordPatternBindings_Nil  =
    (\ _lhsInamesInScope
       _lhsIpatternMatchWarnings ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: RecordPatternBindings
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
          in  ( _lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames)))
-- RightHandSide -----------------------------------------------
-- cata
sem_RightHandSide :: RightHandSide  ->
                     T_RightHandSide 
sem_RightHandSide (RightHandSide_Expression _range _expression _where )  =
    (sem_RightHandSide_Expression (sem_Range _range ) (sem_Expression _expression ) (sem_MaybeDeclarations _where ) )
sem_RightHandSide (RightHandSide_Guarded _range _guardedexpressions _where )  =
    (sem_RightHandSide_Guarded (sem_Range _range ) (sem_GuardedExpressions _guardedexpressions ) (sem_MaybeDeclarations _where ) )
-- semantic domain
type T_RightHandSide  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                        (M.Map NameWithRange TpScheme) ->
                        Predicates ->
                        Tp ->
                        Int ->
                        ClassEnvironment ->
                        TypeErrors ->
                        Warnings ->
                        Int ->
                        DictionaryEnvironment ->
                        ImportEnvironment ->
                        (IO ()) ->
                        Monos ->
                        Names ->
                        OrderedTypeSynonyms ->
                        InfoTree ->
                        ([Warning]) ->
                        FixpointSubstitution ->
                        (M.Map Int (Scheme Predicates)) ->
                        Int ->
                        ( Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,DictionaryEnvironment,Bool,InfoTree,(IO ()),([Warning]),RightHandSide,Names,Int)
sem_RightHandSide_Expression :: T_Range  ->
                                T_Expression  ->
                                T_MaybeDeclarations  ->
                                T_RightHandSide 
sem_RightHandSide_Expression range_ expression_ where_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraints :: ConstraintSet
              _whereOassumptions :: Assumptions
              _whereOconstraints :: ConstraintSet
              _lhsOinfoTree :: InfoTree
              _lhsOunboundNames :: Names
              _expressionOnamesInScope :: Names
              _whereOunboundNames :: Names
              _expressionOuniqueSecondRound :: Int
              _whereObetaUnique :: Int
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOfallthrough :: Bool
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: RightHandSide
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionObetaUnique :: Int
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _whereOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _whereOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _whereOavailablePredicates :: Predicates
              _whereOclassEnvironment :: ClassEnvironment
              _whereOcollectErrors :: TypeErrors
              _whereOcollectWarnings :: Warnings
              _whereOcurrentChunk :: Int
              _whereOdictionaryEnvironment :: DictionaryEnvironment
              _whereOimportEnvironment :: ImportEnvironment
              _whereOmatchIO :: (IO ())
              _whereOmonos :: Monos
              _whereOnamesInScope :: Names
              _whereOorderedTypeSynonyms :: OrderedTypeSynonyms
              _whereOparentTree :: InfoTree
              _whereOpatternMatchWarnings :: ([Warning])
              _whereOsubstitution :: FixpointSubstitution
              _whereOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _whereOuniqueChunk :: Int
              _rangeIself :: Range
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _whereIassumptions :: Assumptions
              _whereIbetaUnique :: Int
              _whereIcollectErrors :: TypeErrors
              _whereIcollectInstances :: ([(Name, Instance)])
              _whereIcollectWarnings :: Warnings
              _whereIconstraints :: ConstraintSet
              _whereIdeclVarNames :: Names
              _whereIdictionaryEnvironment :: DictionaryEnvironment
              _whereIinfoTrees :: InfoTrees
              _whereIlocalTypes :: (M.Map NameWithRange TpScheme)
              _whereImatchIO :: (IO ())
              _whereInamesInScope :: Names
              _whereIpatternMatchWarnings :: ([Warning])
              _whereIself :: MaybeDeclarations
              _whereIunboundNames :: Names
              _whereIuniqueChunk :: Int
              _lhsOassumptions =
                  _whereIassumptions
              _lhsOconstraints =
                  _whereIconstraints
              _whereOassumptions =
                  _expressionIassumptions
              _whereOconstraints =
                  _newcon .>. _expressionIconstraints
              _newcon =
                  [ (_expressionIbeta .==. _lhsIbetaRight) _cinfo ]
              _allTypeSchemes =
                  _whereIlocalTypes `M.union` _lhsIallTypeSchemes
              _cinfo =
                  orphanConstraint 0 "right-hand side" _parentTree
                     [ Unifier (head (ftv _lhsIbetaRight)) ("right-hand sides", attribute (skip_UHA_FB_RHS _lhsIparentTree), "right-hand side") ]
              _localInfo =
                  LocalInfo { self = UHA_RHS _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo (_expressionIinfoTree : _whereIinfoTrees)
              _lhsOinfoTree =
                  _parentTree
              _lhsOunboundNames =
                  _whereIunboundNames
              _expressionOnamesInScope =
                  _whereInamesInScope
              _whereOunboundNames =
                  _expressionIunboundNames
              _expressionOuniqueSecondRound =
                  _expressionIbetaUnique
              _whereObetaUnique =
                  _expressionIuniqueSecondRound
              _expressionOtryPatterns =
                  []
              _lhsOfallthrough =
                  False
              _lhsOcollectInstances =
                  _expressionIcollectInstances  ++  _whereIcollectInstances
              _self =
                  RightHandSide_Expression _rangeIself _expressionIself _whereIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _whereIbetaUnique
              _lhsOcollectErrors =
                  _whereIcollectErrors
              _lhsOcollectWarnings =
                  _whereIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _whereIdictionaryEnvironment
              _lhsOmatchIO =
                  _whereImatchIO
              _lhsOpatternMatchWarnings =
                  _whereIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _whereIuniqueChunk
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _allTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionObetaUnique =
                  _lhsIbetaUnique
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _parentTree
              _expressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _whereOallPatterns =
                  _lhsIallPatterns
              _whereOallTypeSchemes =
                  _allTypeSchemes
              _whereOavailablePredicates =
                  _lhsIavailablePredicates
              _whereOclassEnvironment =
                  _lhsIclassEnvironment
              _whereOcollectErrors =
                  _expressionIcollectErrors
              _whereOcollectWarnings =
                  _expressionIcollectWarnings
              _whereOcurrentChunk =
                  _lhsIcurrentChunk
              _whereOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _whereOimportEnvironment =
                  _lhsIimportEnvironment
              _whereOmatchIO =
                  _expressionImatchIO
              _whereOmonos =
                  _lhsImonos
              _whereOnamesInScope =
                  _lhsInamesInScope
              _whereOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _whereOparentTree =
                  _parentTree
              _whereOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _whereOsubstitution =
                  _lhsIsubstitution
              _whereOtypeschemeMap =
                  _lhsItypeschemeMap
              _whereOuniqueChunk =
                  _expressionIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
              ( _whereIassumptions,_whereIbetaUnique,_whereIcollectErrors,_whereIcollectInstances,_whereIcollectWarnings,_whereIconstraints,_whereIdeclVarNames,_whereIdictionaryEnvironment,_whereIinfoTrees,_whereIlocalTypes,_whereImatchIO,_whereInamesInScope,_whereIpatternMatchWarnings,_whereIself,_whereIunboundNames,_whereIuniqueChunk) =
                  (where_ _whereOallPatterns _whereOallTypeSchemes _whereOassumptions _whereOavailablePredicates _whereObetaUnique _whereOclassEnvironment _whereOcollectErrors _whereOcollectWarnings _whereOconstraints _whereOcurrentChunk _whereOdictionaryEnvironment _whereOimportEnvironment _whereOmatchIO _whereOmonos _whereOnamesInScope _whereOorderedTypeSynonyms _whereOparentTree _whereOpatternMatchWarnings _whereOsubstitution _whereOtypeschemeMap _whereOunboundNames _whereOuniqueChunk )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOfallthrough,_lhsOinfoTree,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk)))
sem_RightHandSide_Guarded :: T_Range  ->
                             T_GuardedExpressions  ->
                             T_MaybeDeclarations  ->
                             T_RightHandSide 
sem_RightHandSide_Guarded range_ guardedexpressions_ where_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIavailablePredicates
       _lhsIbetaRight
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIuniqueChunk ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraints :: ConstraintSet
              _guardedexpressionsOnumberOfGuards :: Int
              _whereOassumptions :: Assumptions
              _whereOconstraints :: ConstraintSet
              _lhsOinfoTree :: InfoTree
              _lhsOunboundNames :: Names
              _guardedexpressionsOnamesInScope :: Names
              _whereOunboundNames :: Names
              _guardedexpressionsOuniqueSecondRound :: Int
              _whereObetaUnique :: Int
              _lhsOfallthrough :: Bool
              _guardedexpressionsOopen :: Bool
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: RightHandSide
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOuniqueChunk :: Int
              _guardedexpressionsOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _guardedexpressionsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _guardedexpressionsOavailablePredicates :: Predicates
              _guardedexpressionsObetaRight :: Tp
              _guardedexpressionsObetaUnique :: Int
              _guardedexpressionsOclassEnvironment :: ClassEnvironment
              _guardedexpressionsOcollectErrors :: TypeErrors
              _guardedexpressionsOcollectWarnings :: Warnings
              _guardedexpressionsOcurrentChunk :: Int
              _guardedexpressionsOdictionaryEnvironment :: DictionaryEnvironment
              _guardedexpressionsOimportEnvironment :: ImportEnvironment
              _guardedexpressionsOmatchIO :: (IO ())
              _guardedexpressionsOmonos :: Monos
              _guardedexpressionsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _guardedexpressionsOparentTree :: InfoTree
              _guardedexpressionsOpatternMatchWarnings :: ([Warning])
              _guardedexpressionsOsubstitution :: FixpointSubstitution
              _guardedexpressionsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _guardedexpressionsOuniqueChunk :: Int
              _whereOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _whereOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _whereOavailablePredicates :: Predicates
              _whereOclassEnvironment :: ClassEnvironment
              _whereOcollectErrors :: TypeErrors
              _whereOcollectWarnings :: Warnings
              _whereOcurrentChunk :: Int
              _whereOdictionaryEnvironment :: DictionaryEnvironment
              _whereOimportEnvironment :: ImportEnvironment
              _whereOmatchIO :: (IO ())
              _whereOmonos :: Monos
              _whereOnamesInScope :: Names
              _whereOorderedTypeSynonyms :: OrderedTypeSynonyms
              _whereOparentTree :: InfoTree
              _whereOpatternMatchWarnings :: ([Warning])
              _whereOsubstitution :: FixpointSubstitution
              _whereOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _whereOuniqueChunk :: Int
              _rangeIself :: Range
              _guardedexpressionsIassumptions :: Assumptions
              _guardedexpressionsIbetaUnique :: Int
              _guardedexpressionsIcollectErrors :: TypeErrors
              _guardedexpressionsIcollectInstances :: ([(Name, Instance)])
              _guardedexpressionsIcollectWarnings :: Warnings
              _guardedexpressionsIconstraintslist :: ConstraintSets
              _guardedexpressionsIdictionaryEnvironment :: DictionaryEnvironment
              _guardedexpressionsIfallthrough :: Bool
              _guardedexpressionsIinfoTrees :: InfoTrees
              _guardedexpressionsImatchIO :: (IO ())
              _guardedexpressionsIpatternMatchWarnings :: ([Warning])
              _guardedexpressionsIself :: GuardedExpressions
              _guardedexpressionsIunboundNames :: Names
              _guardedexpressionsIuniqueChunk :: Int
              _guardedexpressionsIuniqueSecondRound :: Int
              _whereIassumptions :: Assumptions
              _whereIbetaUnique :: Int
              _whereIcollectErrors :: TypeErrors
              _whereIcollectInstances :: ([(Name, Instance)])
              _whereIcollectWarnings :: Warnings
              _whereIconstraints :: ConstraintSet
              _whereIdeclVarNames :: Names
              _whereIdictionaryEnvironment :: DictionaryEnvironment
              _whereIinfoTrees :: InfoTrees
              _whereIlocalTypes :: (M.Map NameWithRange TpScheme)
              _whereImatchIO :: (IO ())
              _whereInamesInScope :: Names
              _whereIpatternMatchWarnings :: ([Warning])
              _whereIself :: MaybeDeclarations
              _whereIunboundNames :: Names
              _whereIuniqueChunk :: Int
              _lhsOassumptions =
                  _whereIassumptions
              _lhsOconstraints =
                  _whereIconstraints
              _guardedexpressionsOnumberOfGuards =
                  length _guardedexpressionsIconstraintslist
              _whereOassumptions =
                  _guardedexpressionsIassumptions
              _whereOconstraints =
                  Node _guardedexpressionsIconstraintslist
              _allTypeSchemes =
                  _whereIlocalTypes `M.union` _lhsIallTypeSchemes
              _localInfo =
                  LocalInfo { self = UHA_RHS _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo (_guardedexpressionsIinfoTrees ++ _whereIinfoTrees)
              _lhsOinfoTree =
                  _parentTree
              _lhsOunboundNames =
                  _whereIunboundNames
              _guardedexpressionsOnamesInScope =
                  _whereInamesInScope
              _whereOunboundNames =
                  _guardedexpressionsIunboundNames
              _guardedexpressionsOuniqueSecondRound =
                  _guardedexpressionsIbetaUnique
              _whereObetaUnique =
                  _guardedexpressionsIuniqueSecondRound
              _lhsOfallthrough =
                  _guardedexpressionsIfallthrough
              _guardedexpressionsOopen =
                  True
              _lhsOpatternMatchWarnings =
                  (if _guardedexpressionsIfallthrough then [FallThrough _rangeIself] else [])
                  ++ _whereIpatternMatchWarnings
              _lhsOcollectInstances =
                  _guardedexpressionsIcollectInstances  ++  _whereIcollectInstances
              _self =
                  RightHandSide_Guarded _rangeIself _guardedexpressionsIself _whereIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _whereIbetaUnique
              _lhsOcollectErrors =
                  _whereIcollectErrors
              _lhsOcollectWarnings =
                  _whereIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _whereIdictionaryEnvironment
              _lhsOmatchIO =
                  _whereImatchIO
              _lhsOuniqueChunk =
                  _whereIuniqueChunk
              _guardedexpressionsOallPatterns =
                  _lhsIallPatterns
              _guardedexpressionsOallTypeSchemes =
                  _allTypeSchemes
              _guardedexpressionsOavailablePredicates =
                  _lhsIavailablePredicates
              _guardedexpressionsObetaRight =
                  _lhsIbetaRight
              _guardedexpressionsObetaUnique =
                  _lhsIbetaUnique
              _guardedexpressionsOclassEnvironment =
                  _lhsIclassEnvironment
              _guardedexpressionsOcollectErrors =
                  _lhsIcollectErrors
              _guardedexpressionsOcollectWarnings =
                  _lhsIcollectWarnings
              _guardedexpressionsOcurrentChunk =
                  _lhsIcurrentChunk
              _guardedexpressionsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _guardedexpressionsOimportEnvironment =
                  _lhsIimportEnvironment
              _guardedexpressionsOmatchIO =
                  _lhsImatchIO
              _guardedexpressionsOmonos =
                  _lhsImonos
              _guardedexpressionsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _guardedexpressionsOparentTree =
                  _parentTree
              _guardedexpressionsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _guardedexpressionsOsubstitution =
                  _lhsIsubstitution
              _guardedexpressionsOtypeschemeMap =
                  _lhsItypeschemeMap
              _guardedexpressionsOuniqueChunk =
                  _lhsIuniqueChunk
              _whereOallPatterns =
                  _lhsIallPatterns
              _whereOallTypeSchemes =
                  _allTypeSchemes
              _whereOavailablePredicates =
                  _lhsIavailablePredicates
              _whereOclassEnvironment =
                  _lhsIclassEnvironment
              _whereOcollectErrors =
                  _guardedexpressionsIcollectErrors
              _whereOcollectWarnings =
                  _guardedexpressionsIcollectWarnings
              _whereOcurrentChunk =
                  _lhsIcurrentChunk
              _whereOdictionaryEnvironment =
                  _guardedexpressionsIdictionaryEnvironment
              _whereOimportEnvironment =
                  _lhsIimportEnvironment
              _whereOmatchIO =
                  _guardedexpressionsImatchIO
              _whereOmonos =
                  _lhsImonos
              _whereOnamesInScope =
                  _lhsInamesInScope
              _whereOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _whereOparentTree =
                  _parentTree
              _whereOpatternMatchWarnings =
                  _guardedexpressionsIpatternMatchWarnings
              _whereOsubstitution =
                  _lhsIsubstitution
              _whereOtypeschemeMap =
                  _lhsItypeschemeMap
              _whereOuniqueChunk =
                  _guardedexpressionsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _guardedexpressionsIassumptions,_guardedexpressionsIbetaUnique,_guardedexpressionsIcollectErrors,_guardedexpressionsIcollectInstances,_guardedexpressionsIcollectWarnings,_guardedexpressionsIconstraintslist,_guardedexpressionsIdictionaryEnvironment,_guardedexpressionsIfallthrough,_guardedexpressionsIinfoTrees,_guardedexpressionsImatchIO,_guardedexpressionsIpatternMatchWarnings,_guardedexpressionsIself,_guardedexpressionsIunboundNames,_guardedexpressionsIuniqueChunk,_guardedexpressionsIuniqueSecondRound) =
                  (guardedexpressions_ _guardedexpressionsOallPatterns _guardedexpressionsOallTypeSchemes _guardedexpressionsOavailablePredicates _guardedexpressionsObetaRight _guardedexpressionsObetaUnique _guardedexpressionsOclassEnvironment _guardedexpressionsOcollectErrors _guardedexpressionsOcollectWarnings _guardedexpressionsOcurrentChunk _guardedexpressionsOdictionaryEnvironment _guardedexpressionsOimportEnvironment _guardedexpressionsOmatchIO _guardedexpressionsOmonos _guardedexpressionsOnamesInScope _guardedexpressionsOnumberOfGuards _guardedexpressionsOopen _guardedexpressionsOorderedTypeSynonyms _guardedexpressionsOparentTree _guardedexpressionsOpatternMatchWarnings _guardedexpressionsOsubstitution _guardedexpressionsOtypeschemeMap _guardedexpressionsOuniqueChunk _guardedexpressionsOuniqueSecondRound )
              ( _whereIassumptions,_whereIbetaUnique,_whereIcollectErrors,_whereIcollectInstances,_whereIcollectWarnings,_whereIconstraints,_whereIdeclVarNames,_whereIdictionaryEnvironment,_whereIinfoTrees,_whereIlocalTypes,_whereImatchIO,_whereInamesInScope,_whereIpatternMatchWarnings,_whereIself,_whereIunboundNames,_whereIuniqueChunk) =
                  (where_ _whereOallPatterns _whereOallTypeSchemes _whereOassumptions _whereOavailablePredicates _whereObetaUnique _whereOclassEnvironment _whereOcollectErrors _whereOcollectWarnings _whereOconstraints _whereOcurrentChunk _whereOdictionaryEnvironment _whereOimportEnvironment _whereOmatchIO _whereOmonos _whereOnamesInScope _whereOorderedTypeSynonyms _whereOparentTree _whereOpatternMatchWarnings _whereOsubstitution _whereOtypeschemeMap _whereOunboundNames _whereOuniqueChunk )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOfallthrough,_lhsOinfoTree,_lhsOmatchIO,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk)))
-- SimpleType --------------------------------------------------
-- cata
sem_SimpleType :: SimpleType  ->
                  T_SimpleType 
sem_SimpleType (SimpleType_SimpleType _range _name _typevariables )  =
    (sem_SimpleType_SimpleType (sem_Range _range ) (sem_Name _name ) (sem_Names _typevariables ) )
-- semantic domain
type T_SimpleType  = ( Name,SimpleType,Names)
sem_SimpleType_SimpleType :: T_Range  ->
                             T_Name  ->
                             T_Names  ->
                             T_SimpleType 
sem_SimpleType_SimpleType range_ name_ typevariables_  =
    (let _lhsOname :: Name
         _lhsOtypevariables :: Names
         _lhsOself :: SimpleType
         _rangeIself :: Range
         _nameIself :: Name
         _typevariablesIself :: Names
         _lhsOname =
             _nameIself
         _lhsOtypevariables =
             _typevariablesIself
         _self =
             SimpleType_SimpleType _rangeIself _nameIself _typevariablesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
         ( _typevariablesIself) =
             (typevariables_ )
     in  ( _lhsOname,_lhsOself,_lhsOtypevariables))
-- Statement ---------------------------------------------------
-- cata
sem_Statement :: Statement  ->
                 T_Statement 
sem_Statement (Statement_Empty _range )  =
    (sem_Statement_Empty (sem_Range _range ) )
sem_Statement (Statement_Expression _range _expression )  =
    (sem_Statement_Expression (sem_Range _range ) (sem_Expression _expression ) )
sem_Statement (Statement_Generator _range _pattern _expression )  =
    (sem_Statement_Generator (sem_Range _range ) (sem_Pattern _pattern ) (sem_Expression _expression ) )
sem_Statement (Statement_Let _range _declarations )  =
    (sem_Statement_Let (sem_Range _range ) (sem_Declarations _declarations ) )
-- semantic domain
type T_Statement  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                    (M.Map NameWithRange TpScheme) ->
                    Assumptions ->
                    Predicates ->
                    Int ->
                    ClassEnvironment ->
                    TypeErrors ->
                    Warnings ->
                    ConstraintSet ->
                    Int ->
                    DictionaryEnvironment ->
                    (Maybe Tp) ->
                    ImportEnvironment ->
                    (IO ()) ->
                    Monos ->
                    Names ->
                    OrderedTypeSynonyms ->
                    InfoTree ->
                    ([Warning]) ->
                    FixpointSubstitution ->
                    (M.Map Int (Scheme Predicates)) ->
                    Names ->
                    Int ->
                    Int ->
                    ( Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,DictionaryEnvironment,(Maybe Tp),InfoTree,(IO ()),Monos,Names,([Warning]),Statement,Names,Int,Int)
sem_Statement_Empty :: T_Range  ->
                       T_Statement 
sem_Statement_Empty range_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIgeneratorBeta
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOinfoTree :: InfoTree
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statement
              _lhsOassumptions :: Assumptions
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOgeneratorBeta :: (Maybe Tp)
              _lhsOmatchIO :: (IO ())
              _lhsOmonos :: Monos
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOunboundNames :: Names
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _rangeIself :: Range
              _localInfo =
                  LocalInfo { self = UHA_Stat _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo []
              _lhsOinfoTree =
                  _parentTree
              _lhsOcollectInstances =
                  []
              _self =
                  Statement_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _lhsIassumptions
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOconstraints =
                  _lhsIconstraints
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOgeneratorBeta =
                  _lhsIgeneratorBeta
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOmonos =
                  _lhsImonos
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOunboundNames =
                  _lhsIunboundNames
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              _lhsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOgeneratorBeta,_lhsOinfoTree,_lhsOmatchIO,_lhsOmonos,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Statement_Expression :: T_Range  ->
                            T_Expression  ->
                            T_Statement 
sem_Statement_Expression range_ expression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIgeneratorBeta
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOgeneratorBeta :: (Maybe Tp)
              _lhsOassumptions :: Assumptions
              _lhsOconstraints :: ConstraintSet
              _expressionObetaUnique :: Int
              _lhsOinfoTree :: InfoTree
              _lhsOunboundNames :: Names
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statement
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOmonos :: Monos
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOnamesInScope :: Names
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _lhsOgeneratorBeta =
                  Just _beta
              _lhsOassumptions =
                  _lhsIassumptions `combine` _expressionIassumptions
              _lhsOconstraints =
                  _locConstraints
              _expressionObetaUnique =
                  _lhsIbetaUnique + 1
              _locConstraints =
                  Node [ _newcon .<. _expressionIconstraints
                       , _lhsIconstraints
                       ]
              _beta =
                  TVar _lhsIbetaUnique
              _newcon =
                  [ (_expressionIbeta .==. ioType _beta) _cinfo ]
              _cinfo =
                  orphanConstraint 0 "generator" _parentTree
                     []
              _localInfo =
                  LocalInfo { self = UHA_Stat _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo [_expressionIinfoTree]
              _lhsOinfoTree =
                  _parentTree
              _lhsOunboundNames =
                  _expressionIunboundNames ++ _lhsIunboundNames
              _expressionOtryPatterns =
                  []
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _self =
                  Statement_Expression _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _expressionIbetaUnique
              _lhsOcollectErrors =
                  _expressionIcollectErrors
              _lhsOcollectWarnings =
                  _expressionIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _lhsOmatchIO =
                  _expressionImatchIO
              _lhsOmonos =
                  _lhsImonos
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOpatternMatchWarnings =
                  _expressionIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _expressionIuniqueChunk
              _lhsOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _parentTree
              _expressionOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOgeneratorBeta,_lhsOinfoTree,_lhsOmatchIO,_lhsOmonos,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Statement_Generator :: T_Range  ->
                           T_Pattern  ->
                           T_Expression  ->
                           T_Statement 
sem_Statement_Generator range_ pattern_ expression_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIgeneratorBeta
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOgeneratorBeta :: (Maybe Tp)
              _lhsOconstraints :: ConstraintSet
              _lhsOassumptions :: Assumptions
              _lhsOmonos :: Monos
              _lhsOinfoTree :: InfoTree
              _lhsOnamesInScope :: Names
              _lhsOunboundNames :: Names
              _expressionOnamesInScope :: Names
              _expressionOtryPatterns :: ([(Expression     , [String])])
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statement
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _patternObetaUnique :: Int
              _patternOimportEnvironment :: ImportEnvironment
              _patternOmonos :: Monos
              _patternOnamesInScope :: Names
              _patternOparentTree :: InfoTree
              _patternOpatternMatchWarnings :: ([Warning])
              _expressionOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _expressionOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _expressionOavailablePredicates :: Predicates
              _expressionObetaUnique :: Int
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectErrors :: TypeErrors
              _expressionOcollectWarnings :: Warnings
              _expressionOcurrentChunk :: Int
              _expressionOdictionaryEnvironment :: DictionaryEnvironment
              _expressionOimportEnvironment :: ImportEnvironment
              _expressionOmatchIO :: (IO ())
              _expressionOmonos :: Monos
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOparentTree :: InfoTree
              _expressionOpatternMatchWarnings :: ([Warning])
              _expressionOsubstitution :: FixpointSubstitution
              _expressionOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _expressionOuniqueChunk :: Int
              _expressionOuniqueSecondRound :: Int
              _rangeIself :: Range
              _patternIbeta :: Tp
              _patternIbetaUnique :: Int
              _patternIconstraints :: ConstraintSet
              _patternIelements :: (  [PatternElement]        )
              _patternIenvironment :: PatternAssumptions
              _patternIinfoTree :: InfoTree
              _patternIpatVarNames :: Names
              _patternIpatternMatchWarnings :: ([Warning])
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _expressionIassumptions :: Assumptions
              _expressionIbeta :: Tp
              _expressionIbetaUnique :: Int
              _expressionIcollectErrors :: TypeErrors
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectWarnings :: Warnings
              _expressionIconstraints :: ConstraintSet
              _expressionIdictionaryEnvironment :: DictionaryEnvironment
              _expressionIinfoTree :: InfoTree
              _expressionImatchIO :: (IO ())
              _expressionImatches :: ([Maybe MetaVariableTable])
              _expressionIpatternMatchWarnings :: ([Warning])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIuniqueChunk :: Int
              _expressionIuniqueSecondRound :: Int
              _lhsOgeneratorBeta =
                  Nothing
              _lhsOconstraints =
                  _locConstraints
              _lhsOassumptions =
                  _assumptions' `combine` _expressionIassumptions
              _lhsOmonos =
                  M.elems _patternIenvironment ++ getMonos _csetBinds ++ _lhsImonos
              _locConstraints =
                  _newcon .>. _csetBinds .>>.
                     Node [ _patternIconstraints
                          , _expressionIconstraints
                          , _lhsIconstraints
                          ]
              _newcon =
                  [ (_expressionIbeta .==. ioType _patternIbeta) _cinfoResult ]
              __tup55 =
                  (_patternIenvironment .===. _lhsIassumptions) _cinfoBind
              (_csetBinds,_) =
                  __tup55
              (_,_assumptions') =
                  __tup55
              _cinfoResult =
                  childConstraint 1 "generator" _parentTree
                     []
              _cinfoBind =
                  \name -> variableConstraint "variable" (nameToUHA_Expr name)
                     [ FolkloreConstraint
                     , makeUnifier name "generator" _patternIenvironment _parentTree
                     ]
              _localInfo =
                  LocalInfo { self = UHA_Stat _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _parentTree =
                  node _lhsIparentTree _localInfo [_patternIinfoTree, _expressionIinfoTree]
              _lhsOinfoTree =
                  _parentTree
              __tup56 =
                  changeOfScope _patternIpatVarNames (_expressionIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup56
              (_,_unboundNames,_) =
                  __tup56
              (_,_,_scopeInfo) =
                  __tup56
              _lhsOnamesInScope =
                  _namesInScope
              _lhsOunboundNames =
                  _unboundNames
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOtryPatterns =
                  []
              _lhsOpatternMatchWarnings =
                  patternMatchWarnings _lhsIimportEnvironment
                                       _lhsIsubstitution
                                       _patternIbeta
                                       (:[])
                                       [(_patternIelements, False)]
                                       _rangeIself
                                       Nothing
                                       False
                                       []
                                       "generator"
                                       "<-"
                  ++ _expressionIpatternMatchWarnings
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _self =
                  Statement_Generator _rangeIself _patternIself _expressionIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _expressionIbetaUnique
              _lhsOcollectErrors =
                  _expressionIcollectErrors
              _lhsOcollectWarnings =
                  _expressionIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _expressionIdictionaryEnvironment
              _lhsOmatchIO =
                  _expressionImatchIO
              _lhsOuniqueChunk =
                  _expressionIuniqueChunk
              _lhsOuniqueSecondRound =
                  _expressionIuniqueSecondRound
              _patternObetaUnique =
                  _lhsIbetaUnique
              _patternOimportEnvironment =
                  _lhsIimportEnvironment
              _patternOmonos =
                  _lhsImonos
              _patternOnamesInScope =
                  _namesInScope
              _patternOparentTree =
                  _parentTree
              _patternOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _expressionOallPatterns =
                  _lhsIallPatterns
              _expressionOallTypeSchemes =
                  _lhsIallTypeSchemes
              _expressionOavailablePredicates =
                  _lhsIavailablePredicates
              _expressionObetaUnique =
                  _patternIbetaUnique
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectErrors =
                  _lhsIcollectErrors
              _expressionOcollectWarnings =
                  _lhsIcollectWarnings
              _expressionOcurrentChunk =
                  _lhsIcurrentChunk
              _expressionOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _expressionOimportEnvironment =
                  _lhsIimportEnvironment
              _expressionOmatchIO =
                  _lhsImatchIO
              _expressionOmonos =
                  _lhsImonos
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOparentTree =
                  _parentTree
              _expressionOpatternMatchWarnings =
                  _patternIpatternMatchWarnings
              _expressionOsubstitution =
                  _lhsIsubstitution
              _expressionOtypeschemeMap =
                  _lhsItypeschemeMap
              _expressionOuniqueChunk =
                  _lhsIuniqueChunk
              _expressionOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              ( _rangeIself) =
                  (range_ )
              ( _patternIbeta,_patternIbetaUnique,_patternIconstraints,_patternIelements,_patternIenvironment,_patternIinfoTree,_patternIpatVarNames,_patternIpatternMatchWarnings,_patternIself,_patternIunboundNames) =
                  (pattern_ _patternObetaUnique _patternOimportEnvironment _patternOmonos _patternOnamesInScope _patternOparentTree _patternOpatternMatchWarnings )
              ( _expressionIassumptions,_expressionIbeta,_expressionIbetaUnique,_expressionIcollectErrors,_expressionIcollectInstances,_expressionIcollectWarnings,_expressionIconstraints,_expressionIdictionaryEnvironment,_expressionIinfoTree,_expressionImatchIO,_expressionImatches,_expressionIpatternMatchWarnings,_expressionIself,_expressionIunboundNames,_expressionIuniqueChunk,_expressionIuniqueSecondRound) =
                  (expression_ _expressionOallPatterns _expressionOallTypeSchemes _expressionOavailablePredicates _expressionObetaUnique _expressionOclassEnvironment _expressionOcollectErrors _expressionOcollectWarnings _expressionOcurrentChunk _expressionOdictionaryEnvironment _expressionOimportEnvironment _expressionOmatchIO _expressionOmonos _expressionOnamesInScope _expressionOorderedTypeSynonyms _expressionOparentTree _expressionOpatternMatchWarnings _expressionOsubstitution _expressionOtryPatterns _expressionOtypeschemeMap _expressionOuniqueChunk _expressionOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOgeneratorBeta,_lhsOinfoTree,_lhsOmatchIO,_lhsOmonos,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Statement_Let :: T_Range  ->
                     T_Declarations  ->
                     T_Statement 
sem_Statement_Let range_ declarations_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIgeneratorBeta
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOgeneratorBeta :: (Maybe Tp)
              _declarationsObindingGroups :: BindingGroups
              _lhsOassumptions :: Assumptions
              _lhsOconstraints :: ConstraintSet
              _lhsObetaUnique :: Int
              _lhsOcollectWarnings :: Warnings
              _lhsOcollectErrors :: TypeErrors
              _declarationsOtypeSignatures :: TypeEnvironment
              _lhsOuniqueChunk :: Int
              _lhsOinfoTree :: InfoTree
              _declarationsOparentTree :: InfoTree
              _lhsOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statement
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOmatchIO :: (IO ())
              _lhsOmonos :: Monos
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueSecondRound :: Int
              _declarationsOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _declarationsOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _declarationsOavailablePredicates :: Predicates
              _declarationsObetaUnique :: Int
              _declarationsOclassEnvironment :: ClassEnvironment
              _declarationsOcollectErrors :: TypeErrors
              _declarationsOcollectWarnings :: Warnings
              _declarationsOcurrentChunk :: Int
              _declarationsOdictionaryEnvironment :: DictionaryEnvironment
              _declarationsOimportEnvironment :: ImportEnvironment
              _declarationsOinheritedBDG :: InheritedBDG
              _declarationsOmatchIO :: (IO ())
              _declarationsOmonos :: Monos
              _declarationsOnamesInScope :: Names
              _declarationsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _declarationsOpatternMatchWarnings :: ([Warning])
              _declarationsOsubstitution :: FixpointSubstitution
              _declarationsOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _declarationsOuniqueChunk :: Int
              _rangeIself :: Range
              _declarationsIbetaUnique :: Int
              _declarationsIbindingGroups :: BindingGroups
              _declarationsIcollectErrors :: TypeErrors
              _declarationsIcollectInstances :: ([(Name, Instance)])
              _declarationsIcollectWarnings :: Warnings
              _declarationsIdeclVarNames :: Names
              _declarationsIdictionaryEnvironment :: DictionaryEnvironment
              _declarationsIinfoTrees :: InfoTrees
              _declarationsImatchIO :: (IO ())
              _declarationsIpatternMatchWarnings :: ([Warning])
              _declarationsIrestrictedNames :: Names
              _declarationsIself :: Declarations
              _declarationsIsimplePatNames :: Names
              _declarationsItypeSignatures :: TypeEnvironment
              _declarationsIunboundNames :: Names
              _declarationsIuniqueChunk :: Int
              _lhsOgeneratorBeta =
                  Nothing
              _declarationsObindingGroups =
                  []
              __tup57 =
                  let inputBDG    = (False, _lhsIcurrentChunk, _declarationsIuniqueChunk, _lhsImonos, _declarationsItypeSignatures, mybdggroup, _declarationsIbetaUnique)
                      mybdggroup = Just (_lhsIassumptions, [_lhsIconstraints])
                  in performBindingGroup inputBDG _declarationsIbindingGroups
              (_lhsOassumptions,_,_,_,_,_) =
                  __tup57
              (_,_lhsOconstraints,_,_,_,_) =
                  __tup57
              (_,_,_inheritedBDG,_,_,_) =
                  __tup57
              (_,_,_,_chunkNr,_,_) =
                  __tup57
              (_,_,_,_,_lhsObetaUnique,_) =
                  __tup57
              (_,_,_,_,_,_implicitsFM) =
                  __tup57
              _inferredTypes =
                  findInferredTypes _lhsItypeschemeMap _implicitsFM
              _lhsOcollectWarnings =
                  missingTypeSignature False _declarationsIsimplePatNames _inferredTypes
                  ++ _declarationsIcollectWarnings
              _lhsOcollectErrors =
                  restrictedNameErrors _inferredTypes _declarationsIrestrictedNames
                  ++ _declarationsIcollectErrors
              _allTypeSchemes =
                  _localTypes `M.union` _lhsIallTypeSchemes
              _localTypes =
                  makeLocalTypeEnv (_declarationsItypeSignatures `M.union` _inferredTypes) _declarationsIbindingGroups
              _declarationsOtypeSignatures =
                  M.empty
              _lhsOuniqueChunk =
                  _chunkNr
              _localInfo =
                  LocalInfo { self = UHA_Stat _self
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _declInfo =
                  LocalInfo { self = UHA_Decls _declarationsIself
                            , assignedType = Nothing
                            , monos = _lhsImonos
                            }
              _thisTree =
                  node _lhsIparentTree _localInfo [_declTree]
              _declTree =
                  node _thisTree _declInfo _declarationsIinfoTrees
              _lhsOinfoTree =
                  _thisTree
              _declarationsOparentTree =
                  _declTree
              __tup58 =
                  internalError "PartialSyntax.ag" "n/a" "toplevel Statement"
              (_collectTypeConstructors,_,_,_,_,_) =
                  __tup58
              (_,_collectValueConstructors,_,_,_,_) =
                  __tup58
              (_,_,_collectTypeSynonyms,_,_,_) =
                  __tup58
              (_,_,_,_collectConstructorEnv,_,_) =
                  __tup58
              (_,_,_,_,_derivedFunctions,_) =
                  __tup58
              (_,_,_,_,_,_operatorFixities) =
                  __tup58
              __tup59 =
                  changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup59
              (_,_unboundNames,_) =
                  __tup59
              (_,_,_scopeInfo) =
                  __tup59
              _lhsOunboundNames =
                  _unboundNames
              _lhsOcollectInstances =
                  _declarationsIcollectInstances
              _self =
                  Statement_Let _rangeIself _declarationsIself
              _lhsOself =
                  _self
              _lhsOdictionaryEnvironment =
                  _declarationsIdictionaryEnvironment
              _lhsOmatchIO =
                  _declarationsImatchIO
              _lhsOmonos =
                  _lhsImonos
              _lhsOnamesInScope =
                  _namesInScope
              _lhsOpatternMatchWarnings =
                  _declarationsIpatternMatchWarnings
              _lhsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _declarationsOallPatterns =
                  _lhsIallPatterns
              _declarationsOallTypeSchemes =
                  _allTypeSchemes
              _declarationsOavailablePredicates =
                  _lhsIavailablePredicates
              _declarationsObetaUnique =
                  _lhsIbetaUnique
              _declarationsOclassEnvironment =
                  _lhsIclassEnvironment
              _declarationsOcollectErrors =
                  _lhsIcollectErrors
              _declarationsOcollectWarnings =
                  _lhsIcollectWarnings
              _declarationsOcurrentChunk =
                  _lhsIcurrentChunk
              _declarationsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _declarationsOimportEnvironment =
                  _lhsIimportEnvironment
              _declarationsOinheritedBDG =
                  _inheritedBDG
              _declarationsOmatchIO =
                  _lhsImatchIO
              _declarationsOmonos =
                  _lhsImonos
              _declarationsOnamesInScope =
                  _namesInScope
              _declarationsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _declarationsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _declarationsOsubstitution =
                  _lhsIsubstitution
              _declarationsOtypeschemeMap =
                  _lhsItypeschemeMap
              _declarationsOuniqueChunk =
                  _lhsIuniqueChunk
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIbetaUnique,_declarationsIbindingGroups,_declarationsIcollectErrors,_declarationsIcollectInstances,_declarationsIcollectWarnings,_declarationsIdeclVarNames,_declarationsIdictionaryEnvironment,_declarationsIinfoTrees,_declarationsImatchIO,_declarationsIpatternMatchWarnings,_declarationsIrestrictedNames,_declarationsIself,_declarationsIsimplePatNames,_declarationsItypeSignatures,_declarationsIunboundNames,_declarationsIuniqueChunk) =
                  (declarations_ _declarationsOallPatterns _declarationsOallTypeSchemes _declarationsOavailablePredicates _declarationsObetaUnique _declarationsObindingGroups _declarationsOclassEnvironment _declarationsOcollectErrors _declarationsOcollectWarnings _declarationsOcurrentChunk _declarationsOdictionaryEnvironment _declarationsOimportEnvironment _declarationsOinheritedBDG _declarationsOmatchIO _declarationsOmonos _declarationsOnamesInScope _declarationsOorderedTypeSynonyms _declarationsOparentTree _declarationsOpatternMatchWarnings _declarationsOsubstitution _declarationsOtypeSignatures _declarationsOtypeschemeMap _declarationsOuniqueChunk )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOgeneratorBeta,_lhsOinfoTree,_lhsOmatchIO,_lhsOmonos,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
-- Statements --------------------------------------------------
-- cata
sem_Statements :: Statements  ->
                  T_Statements 
sem_Statements list  =
    (Prelude.foldr sem_Statements_Cons sem_Statements_Nil (Prelude.map sem_Statement list) )
-- semantic domain
type T_Statements  = ([((Expression, [String]), Core_TypingStrategy)]) ->
                     (M.Map NameWithRange TpScheme) ->
                     Assumptions ->
                     Predicates ->
                     Int ->
                     ClassEnvironment ->
                     TypeErrors ->
                     Warnings ->
                     ConstraintSet ->
                     Int ->
                     DictionaryEnvironment ->
                     (Maybe Tp) ->
                     ImportEnvironment ->
                     (IO ()) ->
                     Monos ->
                     Names ->
                     OrderedTypeSynonyms ->
                     InfoTree ->
                     ([Warning]) ->
                     FixpointSubstitution ->
                     (M.Map Int (Scheme Predicates)) ->
                     Names ->
                     Int ->
                     Int ->
                     ( Assumptions,Int,TypeErrors,([(Name, Instance)]),Warnings,ConstraintSet,DictionaryEnvironment,(Maybe Tp),InfoTrees,(IO ()),Names,([Warning]),Statements,Names,Int,Int)
sem_Statements_Cons :: T_Statement  ->
                       T_Statements  ->
                       T_Statements 
sem_Statements_Cons hd_ tl_  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIgeneratorBeta
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraints :: ConstraintSet
              _hdOassumptions :: Assumptions
              _hdOconstraints :: ConstraintSet
              _tlOassumptions :: Assumptions
              _tlOconstraints :: ConstraintSet
              _lhsOinfoTrees :: InfoTrees
              _lhsOunboundNames :: Names
              _tlOunboundNames :: Names
              _hdOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statements
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOgeneratorBeta :: (Maybe Tp)
              _lhsOmatchIO :: (IO ())
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _hdOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _hdOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _hdOavailablePredicates :: Predicates
              _hdObetaUnique :: Int
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectErrors :: TypeErrors
              _hdOcollectWarnings :: Warnings
              _hdOcurrentChunk :: Int
              _hdOdictionaryEnvironment :: DictionaryEnvironment
              _hdOgeneratorBeta :: (Maybe Tp)
              _hdOimportEnvironment :: ImportEnvironment
              _hdOmatchIO :: (IO ())
              _hdOmonos :: Monos
              _hdOnamesInScope :: Names
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOparentTree :: InfoTree
              _hdOpatternMatchWarnings :: ([Warning])
              _hdOsubstitution :: FixpointSubstitution
              _hdOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _hdOuniqueChunk :: Int
              _hdOuniqueSecondRound :: Int
              _tlOallPatterns :: ([((Expression, [String]), Core_TypingStrategy)])
              _tlOallTypeSchemes :: (M.Map NameWithRange TpScheme)
              _tlOavailablePredicates :: Predicates
              _tlObetaUnique :: Int
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectErrors :: TypeErrors
              _tlOcollectWarnings :: Warnings
              _tlOcurrentChunk :: Int
              _tlOdictionaryEnvironment :: DictionaryEnvironment
              _tlOgeneratorBeta :: (Maybe Tp)
              _tlOimportEnvironment :: ImportEnvironment
              _tlOmatchIO :: (IO ())
              _tlOmonos :: Monos
              _tlOnamesInScope :: Names
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOparentTree :: InfoTree
              _tlOpatternMatchWarnings :: ([Warning])
              _tlOsubstitution :: FixpointSubstitution
              _tlOtypeschemeMap :: (M.Map Int (Scheme Predicates))
              _tlOuniqueChunk :: Int
              _tlOuniqueSecondRound :: Int
              _hdIassumptions :: Assumptions
              _hdIbetaUnique :: Int
              _hdIcollectErrors :: TypeErrors
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectWarnings :: Warnings
              _hdIconstraints :: ConstraintSet
              _hdIdictionaryEnvironment :: DictionaryEnvironment
              _hdIgeneratorBeta :: (Maybe Tp)
              _hdIinfoTree :: InfoTree
              _hdImatchIO :: (IO ())
              _hdImonos :: Monos
              _hdInamesInScope :: Names
              _hdIpatternMatchWarnings :: ([Warning])
              _hdIself :: Statement
              _hdIunboundNames :: Names
              _hdIuniqueChunk :: Int
              _hdIuniqueSecondRound :: Int
              _tlIassumptions :: Assumptions
              _tlIbetaUnique :: Int
              _tlIcollectErrors :: TypeErrors
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectWarnings :: Warnings
              _tlIconstraints :: ConstraintSet
              _tlIdictionaryEnvironment :: DictionaryEnvironment
              _tlIgeneratorBeta :: (Maybe Tp)
              _tlIinfoTrees :: InfoTrees
              _tlImatchIO :: (IO ())
              _tlInamesInScope :: Names
              _tlIpatternMatchWarnings :: ([Warning])
              _tlIself :: Statements
              _tlIunboundNames :: Names
              _tlIuniqueChunk :: Int
              _tlIuniqueSecondRound :: Int
              _lhsOassumptions =
                  _hdIassumptions
              _lhsOconstraints =
                  _hdIconstraints
              _hdOassumptions =
                  _tlIassumptions
              _hdOconstraints =
                  _tlIconstraints
              _tlOassumptions =
                  _lhsIassumptions
              _tlOconstraints =
                  _lhsIconstraints
              _lhsOinfoTrees =
                  _hdIinfoTree : _tlIinfoTrees
              _lhsOunboundNames =
                  _hdIunboundNames
              _tlOunboundNames =
                  _lhsIunboundNames
              _hdOunboundNames =
                  _tlIunboundNames
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObetaUnique =
                  _tlIbetaUnique
              _lhsOcollectErrors =
                  _tlIcollectErrors
              _lhsOcollectWarnings =
                  _tlIcollectWarnings
              _lhsOdictionaryEnvironment =
                  _tlIdictionaryEnvironment
              _lhsOgeneratorBeta =
                  _tlIgeneratorBeta
              _lhsOmatchIO =
                  _tlImatchIO
              _lhsOnamesInScope =
                  _tlInamesInScope
              _lhsOpatternMatchWarnings =
                  _tlIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _tlIuniqueChunk
              _lhsOuniqueSecondRound =
                  _tlIuniqueSecondRound
              _hdOallPatterns =
                  _lhsIallPatterns
              _hdOallTypeSchemes =
                  _lhsIallTypeSchemes
              _hdOavailablePredicates =
                  _lhsIavailablePredicates
              _hdObetaUnique =
                  _lhsIbetaUnique
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectErrors =
                  _lhsIcollectErrors
              _hdOcollectWarnings =
                  _lhsIcollectWarnings
              _hdOcurrentChunk =
                  _lhsIcurrentChunk
              _hdOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _hdOgeneratorBeta =
                  _lhsIgeneratorBeta
              _hdOimportEnvironment =
                  _lhsIimportEnvironment
              _hdOmatchIO =
                  _lhsImatchIO
              _hdOmonos =
                  _lhsImonos
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOparentTree =
                  _lhsIparentTree
              _hdOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _hdOsubstitution =
                  _lhsIsubstitution
              _hdOtypeschemeMap =
                  _lhsItypeschemeMap
              _hdOuniqueChunk =
                  _lhsIuniqueChunk
              _hdOuniqueSecondRound =
                  _lhsIuniqueSecondRound
              _tlOallPatterns =
                  _lhsIallPatterns
              _tlOallTypeSchemes =
                  _lhsIallTypeSchemes
              _tlOavailablePredicates =
                  _lhsIavailablePredicates
              _tlObetaUnique =
                  _hdIbetaUnique
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectErrors =
                  _hdIcollectErrors
              _tlOcollectWarnings =
                  _hdIcollectWarnings
              _tlOcurrentChunk =
                  _lhsIcurrentChunk
              _tlOdictionaryEnvironment =
                  _hdIdictionaryEnvironment
              _tlOgeneratorBeta =
                  _hdIgeneratorBeta
              _tlOimportEnvironment =
                  _lhsIimportEnvironment
              _tlOmatchIO =
                  _hdImatchIO
              _tlOmonos =
                  _hdImonos
              _tlOnamesInScope =
                  _hdInamesInScope
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOparentTree =
                  _lhsIparentTree
              _tlOpatternMatchWarnings =
                  _hdIpatternMatchWarnings
              _tlOsubstitution =
                  _lhsIsubstitution
              _tlOtypeschemeMap =
                  _lhsItypeschemeMap
              _tlOuniqueChunk =
                  _hdIuniqueChunk
              _tlOuniqueSecondRound =
                  _hdIuniqueSecondRound
              ( _hdIassumptions,_hdIbetaUnique,_hdIcollectErrors,_hdIcollectInstances,_hdIcollectWarnings,_hdIconstraints,_hdIdictionaryEnvironment,_hdIgeneratorBeta,_hdIinfoTree,_hdImatchIO,_hdImonos,_hdInamesInScope,_hdIpatternMatchWarnings,_hdIself,_hdIunboundNames,_hdIuniqueChunk,_hdIuniqueSecondRound) =
                  (hd_ _hdOallPatterns _hdOallTypeSchemes _hdOassumptions _hdOavailablePredicates _hdObetaUnique _hdOclassEnvironment _hdOcollectErrors _hdOcollectWarnings _hdOconstraints _hdOcurrentChunk _hdOdictionaryEnvironment _hdOgeneratorBeta _hdOimportEnvironment _hdOmatchIO _hdOmonos _hdOnamesInScope _hdOorderedTypeSynonyms _hdOparentTree _hdOpatternMatchWarnings _hdOsubstitution _hdOtypeschemeMap _hdOunboundNames _hdOuniqueChunk _hdOuniqueSecondRound )
              ( _tlIassumptions,_tlIbetaUnique,_tlIcollectErrors,_tlIcollectInstances,_tlIcollectWarnings,_tlIconstraints,_tlIdictionaryEnvironment,_tlIgeneratorBeta,_tlIinfoTrees,_tlImatchIO,_tlInamesInScope,_tlIpatternMatchWarnings,_tlIself,_tlIunboundNames,_tlIuniqueChunk,_tlIuniqueSecondRound) =
                  (tl_ _tlOallPatterns _tlOallTypeSchemes _tlOassumptions _tlOavailablePredicates _tlObetaUnique _tlOclassEnvironment _tlOcollectErrors _tlOcollectWarnings _tlOconstraints _tlOcurrentChunk _tlOdictionaryEnvironment _tlOgeneratorBeta _tlOimportEnvironment _tlOmatchIO _tlOmonos _tlOnamesInScope _tlOorderedTypeSynonyms _tlOparentTree _tlOpatternMatchWarnings _tlOsubstitution _tlOtypeschemeMap _tlOunboundNames _tlOuniqueChunk _tlOuniqueSecondRound )
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOgeneratorBeta,_lhsOinfoTrees,_lhsOmatchIO,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
sem_Statements_Nil :: T_Statements 
sem_Statements_Nil  =
    (\ _lhsIallPatterns
       _lhsIallTypeSchemes
       _lhsIassumptions
       _lhsIavailablePredicates
       _lhsIbetaUnique
       _lhsIclassEnvironment
       _lhsIcollectErrors
       _lhsIcollectWarnings
       _lhsIconstraints
       _lhsIcurrentChunk
       _lhsIdictionaryEnvironment
       _lhsIgeneratorBeta
       _lhsIimportEnvironment
       _lhsImatchIO
       _lhsImonos
       _lhsInamesInScope
       _lhsIorderedTypeSynonyms
       _lhsIparentTree
       _lhsIpatternMatchWarnings
       _lhsIsubstitution
       _lhsItypeschemeMap
       _lhsIunboundNames
       _lhsIuniqueChunk
       _lhsIuniqueSecondRound ->
         (let _lhsOinfoTrees :: InfoTrees
              _lhsOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statements
              _lhsOassumptions :: Assumptions
              _lhsObetaUnique :: Int
              _lhsOcollectErrors :: TypeErrors
              _lhsOcollectWarnings :: Warnings
              _lhsOconstraints :: ConstraintSet
              _lhsOdictionaryEnvironment :: DictionaryEnvironment
              _lhsOgeneratorBeta :: (Maybe Tp)
              _lhsOmatchIO :: (IO ())
              _lhsOnamesInScope :: Names
              _lhsOpatternMatchWarnings :: ([Warning])
              _lhsOuniqueChunk :: Int
              _lhsOuniqueSecondRound :: Int
              _lhsOinfoTrees =
                  []
              _lhsOunboundNames =
                  _lhsIunboundNames
              _lhsOcollectInstances =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _lhsIassumptions
              _lhsObetaUnique =
                  _lhsIbetaUnique
              _lhsOcollectErrors =
                  _lhsIcollectErrors
              _lhsOcollectWarnings =
                  _lhsIcollectWarnings
              _lhsOconstraints =
                  _lhsIconstraints
              _lhsOdictionaryEnvironment =
                  _lhsIdictionaryEnvironment
              _lhsOgeneratorBeta =
                  _lhsIgeneratorBeta
              _lhsOmatchIO =
                  _lhsImatchIO
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOpatternMatchWarnings =
                  _lhsIpatternMatchWarnings
              _lhsOuniqueChunk =
                  _lhsIuniqueChunk
              _lhsOuniqueSecondRound =
                  _lhsIuniqueSecondRound
          in  ( _lhsOassumptions,_lhsObetaUnique,_lhsOcollectErrors,_lhsOcollectInstances,_lhsOcollectWarnings,_lhsOconstraints,_lhsOdictionaryEnvironment,_lhsOgeneratorBeta,_lhsOinfoTrees,_lhsOmatchIO,_lhsOnamesInScope,_lhsOpatternMatchWarnings,_lhsOself,_lhsOunboundNames,_lhsOuniqueChunk,_lhsOuniqueSecondRound)))
-- Strings -----------------------------------------------------
-- cata
sem_Strings :: Strings  ->
               T_Strings 
sem_Strings list  =
    (Prelude.foldr sem_Strings_Cons sem_Strings_Nil list )
-- semantic domain
type T_Strings  = ( Strings)
sem_Strings_Cons :: String ->
                    T_Strings  ->
                    T_Strings 
sem_Strings_Cons hd_ tl_  =
    (let _lhsOself :: Strings
         _tlIself :: Strings
         _self =
             (:) hd_ _tlIself
         _lhsOself =
             _self
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Strings_Nil :: T_Strings 
sem_Strings_Nil  =
    (let _lhsOself :: Strings
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Type --------------------------------------------------------
-- cata
sem_Type :: Type  ->
            T_Type 
sem_Type (Type_Application _range _prefix _function _arguments )  =
    (sem_Type_Application (sem_Range _range ) _prefix (sem_Type _function ) (sem_Types _arguments ) )
sem_Type (Type_Constructor _range _name )  =
    (sem_Type_Constructor (sem_Range _range ) (sem_Name _name ) )
sem_Type (Type_Exists _range _typevariables _type )  =
    (sem_Type_Exists (sem_Range _range ) (sem_Names _typevariables ) (sem_Type _type ) )
sem_Type (Type_Forall _range _typevariables _type )  =
    (sem_Type_Forall (sem_Range _range ) (sem_Names _typevariables ) (sem_Type _type ) )
sem_Type (Type_Parenthesized _range _type )  =
    (sem_Type_Parenthesized (sem_Range _range ) (sem_Type _type ) )
sem_Type (Type_Qualified _range _context _type )  =
    (sem_Type_Qualified (sem_Range _range ) (sem_ContextItems _context ) (sem_Type _type ) )
sem_Type (Type_Variable _range _name )  =
    (sem_Type_Variable (sem_Range _range ) (sem_Name _name ) )
-- semantic domain
type T_Type  = ( Type)
sem_Type_Application :: T_Range  ->
                        Bool ->
                        T_Type  ->
                        T_Types  ->
                        T_Type 
sem_Type_Application range_ prefix_ function_ arguments_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _functionIself :: Type
         _argumentsIself :: Types
         _self =
             Type_Application _rangeIself prefix_ _functionIself _argumentsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _functionIself) =
             (function_ )
         ( _argumentsIself) =
             (arguments_ )
     in  ( _lhsOself))
sem_Type_Constructor :: T_Range  ->
                        T_Name  ->
                        T_Type 
sem_Type_Constructor range_ name_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Type_Constructor _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
sem_Type_Exists :: T_Range  ->
                   T_Names  ->
                   T_Type  ->
                   T_Type 
sem_Type_Exists range_ typevariables_ type_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _typevariablesIself :: Names
         _typeIself :: Type
         _self =
             Type_Exists _rangeIself _typevariablesIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _typevariablesIself) =
             (typevariables_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
sem_Type_Forall :: T_Range  ->
                   T_Names  ->
                   T_Type  ->
                   T_Type 
sem_Type_Forall range_ typevariables_ type_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _typevariablesIself :: Names
         _typeIself :: Type
         _self =
             Type_Forall _rangeIself _typevariablesIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _typevariablesIself) =
             (typevariables_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
sem_Type_Parenthesized :: T_Range  ->
                          T_Type  ->
                          T_Type 
sem_Type_Parenthesized range_ type_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _typeIself :: Type
         _self =
             Type_Parenthesized _rangeIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
sem_Type_Qualified :: T_Range  ->
                      T_ContextItems  ->
                      T_Type  ->
                      T_Type 
sem_Type_Qualified range_ context_ type_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _contextIself :: ContextItems
         _typeIself :: Type
         _self =
             Type_Qualified _rangeIself _contextIself _typeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _contextIself) =
             (context_ )
         ( _typeIself) =
             (type_ )
     in  ( _lhsOself))
sem_Type_Variable :: T_Range  ->
                     T_Name  ->
                     T_Type 
sem_Type_Variable range_ name_  =
    (let _lhsOself :: Type
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Type_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             (range_ )
         ( _nameIself) =
             (name_ )
     in  ( _lhsOself))
-- Types -------------------------------------------------------
-- cata
sem_Types :: Types  ->
             T_Types 
sem_Types list  =
    (Prelude.foldr sem_Types_Cons sem_Types_Nil (Prelude.map sem_Type list) )
-- semantic domain
type T_Types  = ( Types)
sem_Types_Cons :: T_Type  ->
                  T_Types  ->
                  T_Types 
sem_Types_Cons hd_ tl_  =
    (let _lhsOself :: Types
         _hdIself :: Type
         _tlIself :: Types
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             (hd_ )
         ( _tlIself) =
             (tl_ )
     in  ( _lhsOself))
sem_Types_Nil :: T_Types 
sem_Types_Nil  =
    (let _lhsOself :: Types
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))