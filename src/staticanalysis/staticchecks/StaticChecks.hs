
-- UUAGC 0.9.5 (StaticChecks.ag)
module StaticChecks where

import Similarity ( similar )
import Args
import UHA_Syntax
import UHA_Utils
import UHA_Range
import Top.Types
import StaticErrors
import Warnings
import Messages
import List
import Utils ( internalError, minInt, maxInt )
import TypeConversion
import DerivingShow
import qualified Data.Map as M
import ImportEnvironment
import OperatorTable
import Char ( isUpper )

-- filter undefined errors that are caused by the removal of a duplicate definition
filterRemovedNames :: [(Name,Entity)] -> Error -> Bool
filterRemovedNames list err = 
   case err of  
      Undefined entity name _ _ -> (name,entity) `notElem` list
      _                         -> True
      
filterDerivedNames :: [Range] -> Error -> Bool
filterDerivedNames ranges err = 
   case err of
      Duplicated Definition names -> any (`notElem` ranges) (map getNameRange names) 
      _                           -> True


uniqueKeys :: Ord key => [(key,a)] -> ([(key,a)],[[key]])
uniqueKeys = let comp (x,_) (y,_) = compare x y
                 eq   (x,_) (y,_) = x == y
                 predicate xs = length xs == 1 
             in (\(xs, ys) -> (map head xs, map (map fst) ys)) 
              . partition predicate 
              . groupBy eq 
              . sortBy comp

                  
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


checkType :: M.Map Name Int -> Names -> Type -> [Error]
checkType typeConstructors namesInScope t =
    let (f, xs) = walkSpine t
        xsErrors = concatMap (checkType typeConstructors namesInScope) xs
    in
        xsErrors
        ++
        case f of
            Type_Constructor r c ->
                checkKind c typeConstructors (length xs) namesInScope
                ++ [ TupleTooBig r
                   | let nameAsString = show c
                   , isTupleConstructor nameAsString
                   , length nameAsString - 1 > 10
                   ]
            Type_Variable _ v ->
                if length xs /= 0 then
                    [ TypeVarApplication v ]
                else
                    []
            _ ->
                internalError "StaticAnalysis" "checkType" "unexpected type"

walkSpine :: Type -> (Type, [Type])
walkSpine t =
    case t of
        Type_Variable _ _ -> (t, [])
        Type_Constructor _ _ -> (t, [])
        Type_Application _ _ f xs ->
            let (t, ys) = walkSpine f
            in (t, ys ++ xs)
        Type_Parenthesized _ t -> walkSpine t
        Type_Qualified _ _ t -> walkSpine t
        _ -> internalError "StaticAnalysis" "walkSpine" "unexpected type"

checkKind :: Name -> M.Map Name Int -> Int -> Names -> [Error]
checkKind tycon@(Name_Special _ _ ('(':commas)) _ useArity _ = -- !!!Name
    if expected == useArity then
        []
    else
        [ ArityMismatch TypeConstructor tycon expected useArity]
    where
        expected =
            case length (takeWhile (== ',') commas) of
                 0 -> 0  -- ()
                 n -> n + 1 -- (,) (,,) ...

checkKind tycon typeConstructors useArity namesInScope =
    case M.lookup tycon typeConstructors of
        Nothing ->
            let hint = [ "Constructor "++show (show tycon)++" cannot be used in a type"
                       | tycon `elem` namesInScope
                       ]
            in [ Undefined TypeConstructor tycon (M.keys typeConstructors) hint ]
        Just defArity ->
            if useArity /= defArity then
                [ ArityMismatch TypeConstructor tycon defArity useArity ]
            else
                [ ]


findSimilarFunctionBindings :: [(Name, TpScheme)] -> [(Name,Name)] -> [Warning]
findSimilarFunctionBindings environment candidates = 
   let namesWithTypeDef = map fst environment
   in [ uncurry SimilarFunctionBindings pair
      | (n1,n2) <- candidates
      , let bool1 = n1 `elem` namesWithTypeDef
            bool2 = n2 `elem` namesWithTypeDef
            pair  = if bool1 then (n2,n1) else (n1,n2)
      , bool1 `xor` bool2
      ]

xor :: Bool -> Bool -> Bool
xor b1 b2 = not (b1 == b2)


simplifyContext :: OrderedTypeSynonyms -> Range -> [(Int, Name)] -> TpScheme -> Warnings
simplifyContext synonyms range intMap typescheme = 
   let predicates = qualifiers (unquantify typescheme)
       reduced    = f predicates []
          where f [] as = reverse as -- reverse to original order
                f (p:ps) as 
                   | entail synonyms standardClasses (ps++as) p = f ps as
                   | otherwise = f ps (p:as)
       sub = listToSubstitution [ (i, TCon (show n)) | (i, n) <- intMap ]
   in if length reduced == length predicates 
        then []
        else [ ReduceContext range (sub |-> predicates) (sub |-> reduced) ]


mode :: Ord a => [a] -> Maybe a -- Just ... IF any of the elements is more common
mode xs = 
    case filter ((== maxFreq) . snd) fs of
        [(x, _)] -> Just x
        _ -> Nothing        
  where
    maxFreq = maximum (map snd fs)
    fs = frequencies xs

frequencies :: Ord a => [a] -> [(a, Int)]
frequencies = map (\ys -> (head ys, length ys)) . group . sort


patternConstructorErrors :: Maybe TpScheme -> Name -> Names -> Int -> Bool -> Names -> [Error]
patternConstructorErrors maybetparity name env useArity lhsPattern namesTyconEnv =
    case maybetparity of
        Nothing ->
            [ undefinedConstructorInPat lhsPattern name env namesTyconEnv ]
        Just tpScheme ->
            let arity = arityOfTpScheme tpScheme
            in if arity /= useArity
               then [ ArityMismatch Constructor name arity useArity ]
               else []


simplePattern :: Pattern -> Bool
simplePattern pattern =
   case pattern of
      Pattern_Constructor _ name _ -> case show name of 
                                         x:_ -> isUpper x
                                         _   -> False
      _                            -> False


-- Type signature but no function definition
-- Duplicated type signatures
-- Overloaded type scheme for a restricted pattern
checkTypeSignatures :: Names -> Names -> [(Name,TpScheme)] -> Errors
checkTypeSignatures declVarNames restrictedNames xs = 
   let (unique, doubles) = uniqueAppearance (map fst xs)
   in [ Duplicated TypeSignature names 
      | names <- doubles 
      ] 
   ++ [ NoFunDef TypeSignature name declVarNames
      | name <- unique
      , name `notElem` declVarNames
      ]
   ++ [ OverloadedRestrPat name
      | (name, scheme) <- xs
      , name `elem` unique 
      , name `elem` restrictedNames     
      , isOverloaded scheme
      ] 


isSimplePattern :: Pattern -> Bool
isSimplePattern pattern =
   case pattern of
      Pattern_Variable _ _ -> True
      Pattern_Parenthesized  _ p -> isSimplePattern p
      _ -> False


checkExport entity name inScope =
    makeUndefined entity
        (if name `elem` inScope then
            []
         else
            [name]
        )
        (nubBy equalName inScope)

equalName x y =
    getNameName x == getNameName y        


topLevelScopeInfo :: ScopeInfo -> ScopeInfo
topLevelScopeInfo (xs, _, _) = (xs, [], [])

makeErrors :: [(ScopeInfo, Entity)] -> Errors
makeErrors xs = [ Duplicated entity ys | ((yss, _, _), entity) <- xs, ys <- yss ]

makeWarnings :: [(ScopeInfo, Entity)] -> Warnings
makeWarnings xs =  [ Unused entity name | ((_, names, _), entity) <- xs, name <- names ]
                ++ [ Shadow n2 n1 | ((_, _, pairs), _) <- xs, (n1, n2) <- pairs ]
-- Alternative -------------------------------------------------
-- cata
sem_Alternative :: Alternative ->
                   T_Alternative
sem_Alternative (Alternative_Alternative _range _pattern _righthandside )  =
    (sem_Alternative_Alternative (sem_Range _range ) (sem_Pattern _pattern ) (sem_RightHandSide _righthandside ) )
sem_Alternative (Alternative_Empty _range )  =
    (sem_Alternative_Empty (sem_Range _range ) )
-- semantic domain
type T_Alternative = Names ->
                     Names ->
                     ClassEnvironment ->
                     ([(ScopeInfo, Entity)]) ->
                     ([Error]) ->
                     ([Error]) ->
                     Names ->
                     ([Option]) ->
                     OrderedTypeSynonyms ->
                     (M.Map Name Int) ->
                     (M.Map Name TpScheme) ->
                     ([Warning]) ->
                     ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),Alternative,Names,([Warning]))
sem_Alternative_Alternative :: T_Range ->
                               T_Pattern ->
                               T_RightHandSide ->
                               T_Alternative
sem_Alternative_Alternative range_ pattern_ righthandside_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _patternOlhsPattern :: Bool
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Alternative
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _patternOallTypeConstructors :: Names
              _patternOallValueConstructors :: Names
              _patternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternOmiscerrors :: ([Error])
              _patternOnamesInScope :: Names
              _patternOtypeConstructors :: (M.Map Name Int)
              _patternOvalueConstructors :: (M.Map Name TpScheme)
              _patternOwarnings :: ([Warning])
              _righthandsideOallTypeConstructors :: Names
              _righthandsideOallValueConstructors :: Names
              _righthandsideOclassEnvironment :: ClassEnvironment
              _righthandsideOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _righthandsideOkindErrors :: ([Error])
              _righthandsideOmiscerrors :: ([Error])
              _righthandsideOnamesInScope :: Names
              _righthandsideOoptions :: ([Option])
              _righthandsideOorderedTypeSynonyms :: OrderedTypeSynonyms
              _righthandsideOtypeConstructors :: (M.Map Name Int)
              _righthandsideOvalueConstructors :: (M.Map Name TpScheme)
              _righthandsideOwarnings :: ([Warning])
              _rangeIself :: Range
              _patternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternImiscerrors :: ([Error])
              _patternIpatVarNames :: Names
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _patternIwarnings :: ([Warning])
              _righthandsideIcollectInstances :: ([(Name, Instance)])
              _righthandsideIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _righthandsideIkindErrors :: ([Error])
              _righthandsideImiscerrors :: ([Error])
              _righthandsideIself :: RightHandSide
              _righthandsideIunboundNames :: Names
              _righthandsideIwarnings :: ([Warning])
              __tup1 =
                  changeOfScope _patternIpatVarNames _righthandsideIunboundNames _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup1
              (_,_unboundNames,_) =
                  __tup1
              (_,_,_scopeInfo) =
                  __tup1
              _lhsOunboundNames =
                  _unboundNames
              _patternOlhsPattern =
                  False
              _lhsOcollectScopeInfos =
                  (_scopeInfo, Variable)   : _righthandsideIcollectScopeInfos
              _lhsOcollectInstances =
                  _righthandsideIcollectInstances
              _self =
                  Alternative_Alternative _rangeIself _patternIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _righthandsideIkindErrors
              _lhsOmiscerrors =
                  _righthandsideImiscerrors
              _lhsOwarnings =
                  _righthandsideIwarnings
              _patternOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternOallValueConstructors =
                  _lhsIallValueConstructors
              _patternOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternOmiscerrors =
                  _lhsImiscerrors
              _patternOnamesInScope =
                  _namesInScope
              _patternOtypeConstructors =
                  _lhsItypeConstructors
              _patternOvalueConstructors =
                  _lhsIvalueConstructors
              _patternOwarnings =
                  _lhsIwarnings
              _righthandsideOallTypeConstructors =
                  _lhsIallTypeConstructors
              _righthandsideOallValueConstructors =
                  _lhsIallValueConstructors
              _righthandsideOclassEnvironment =
                  _lhsIclassEnvironment
              _righthandsideOcollectScopeInfos =
                  _patternIcollectScopeInfos
              _righthandsideOkindErrors =
                  _lhsIkindErrors
              _righthandsideOmiscerrors =
                  _patternImiscerrors
              _righthandsideOnamesInScope =
                  _namesInScope
              _righthandsideOoptions =
                  _lhsIoptions
              _righthandsideOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _righthandsideOtypeConstructors =
                  _lhsItypeConstructors
              _righthandsideOvalueConstructors =
                  _lhsIvalueConstructors
              _righthandsideOwarnings =
                  _patternIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternIcollectScopeInfos,_patternImiscerrors,_patternIpatVarNames,_patternIself,_patternIunboundNames,_patternIwarnings) =
                  (pattern_ _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings )
              ( _righthandsideIcollectInstances,_righthandsideIcollectScopeInfos,_righthandsideIkindErrors,_righthandsideImiscerrors,_righthandsideIself,_righthandsideIunboundNames,_righthandsideIwarnings) =
                  (righthandside_ _righthandsideOallTypeConstructors _righthandsideOallValueConstructors _righthandsideOclassEnvironment _righthandsideOcollectScopeInfos _righthandsideOkindErrors _righthandsideOmiscerrors _righthandsideOnamesInScope _righthandsideOoptions _righthandsideOorderedTypeSynonyms _righthandsideOtypeConstructors _righthandsideOvalueConstructors _righthandsideOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Alternative_Empty :: T_Range ->
                         T_Alternative
sem_Alternative_Empty range_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Alternative
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _rangeIself :: Range
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Alternative_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- Alternatives ------------------------------------------------
-- cata
sem_Alternatives :: Alternatives ->
                    T_Alternatives
sem_Alternatives list  =
    (Prelude.foldr sem_Alternatives_Cons sem_Alternatives_Nil (Prelude.map sem_Alternative list) )
-- semantic domain
type T_Alternatives = Names ->
                      Names ->
                      ClassEnvironment ->
                      ([(ScopeInfo, Entity)]) ->
                      ([Error]) ->
                      ([Error]) ->
                      Names ->
                      ([Option]) ->
                      OrderedTypeSynonyms ->
                      (M.Map Name Int) ->
                      (M.Map Name TpScheme) ->
                      ([Warning]) ->
                      ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),Alternatives,Names,([Warning]))
sem_Alternatives_Cons :: T_Alternative ->
                         T_Alternatives ->
                         T_Alternatives
sem_Alternatives_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Alternatives
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOallValueConstructors :: Names
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOkindErrors :: ([Error])
              _hdOmiscerrors :: ([Error])
              _hdOnamesInScope :: Names
              _hdOoptions :: ([Option])
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOvalueConstructors :: (M.Map Name TpScheme)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOallValueConstructors :: Names
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlOkindErrors :: ([Error])
              _tlOmiscerrors :: ([Error])
              _tlOnamesInScope :: Names
              _tlOoptions :: ([Option])
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOvalueConstructors :: (M.Map Name TpScheme)
              _tlOwarnings :: ([Warning])
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdIkindErrors :: ([Error])
              _hdImiscerrors :: ([Error])
              _hdIself :: Alternative
              _hdIunboundNames :: Names
              _hdIwarnings :: ([Warning])
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlIkindErrors :: ([Error])
              _tlImiscerrors :: ([Error])
              _tlIself :: Alternatives
              _tlIunboundNames :: Names
              _tlIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _tlIcollectScopeInfos
              _lhsOkindErrors =
                  _tlIkindErrors
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOallValueConstructors =
                  _lhsIallValueConstructors
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _hdOkindErrors =
                  _lhsIkindErrors
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOoptions =
                  _lhsIoptions
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOvalueConstructors =
                  _lhsIvalueConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOallValueConstructors =
                  _lhsIallValueConstructors
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectScopeInfos =
                  _hdIcollectScopeInfos
              _tlOkindErrors =
                  _hdIkindErrors
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOoptions =
                  _lhsIoptions
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOvalueConstructors =
                  _lhsIvalueConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIcollectInstances,_hdIcollectScopeInfos,_hdIkindErrors,_hdImiscerrors,_hdIself,_hdIunboundNames,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings )
              ( _tlIcollectInstances,_tlIcollectScopeInfos,_tlIkindErrors,_tlImiscerrors,_tlIself,_tlIunboundNames,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Alternatives_Nil :: T_Alternatives
sem_Alternatives_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Alternatives
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- AnnotatedType -----------------------------------------------
-- cata
sem_AnnotatedType :: AnnotatedType ->
                     T_AnnotatedType
sem_AnnotatedType (AnnotatedType_AnnotatedType _range _strict _type )  =
    (sem_AnnotatedType_AnnotatedType (sem_Range _range ) _strict (sem_Type _type ) )
-- semantic domain
type T_AnnotatedType = Names ->
                       Names ->
                       ([Error]) ->
                       ([Error]) ->
                       Names ->
                       ([Option]) ->
                       (M.Map Name Int) ->
                       (M.Map Name TpScheme) ->
                       ([Warning]) ->
                       ( ([Error]),([Error]),AnnotatedType,Type,Names,Names,([Warning]))
sem_AnnotatedType_AnnotatedType :: T_Range ->
                                   Bool ->
                                   T_Type ->
                                   T_AnnotatedType
sem_AnnotatedType_AnnotatedType range_ strict_ type_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOtype :: Type
              _lhsOkindErrors :: ([Error])
              _lhsOtypevariables :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: AnnotatedType
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _typeOallTypeConstructors :: Names
              _typeOmiscerrors :: ([Error])
              _typeOoptions :: ([Option])
              _typeOtypeConstructors :: (M.Map Name Int)
              _typeOwarnings :: ([Warning])
              _rangeIself :: Range
              _typeIcontextRange :: Range
              _typeImiscerrors :: ([Error])
              _typeIself :: Type
              _typeItypevariables :: Names
              _typeIwarnings :: ([Warning])
              _lhsOtype =
                  _typeIself
              _lhsOkindErrors =
                  _newErrors ++ _lhsIkindErrors
              _newErrors =
                  checkType _lhsItypeConstructors (_lhsInamesInScope ++ _lhsIallValueConstructors) _typeIself
              _lhsOtypevariables =
                  _typeItypevariables
              _lhsOunboundNames =
                  []
              _self =
                  AnnotatedType_AnnotatedType _rangeIself strict_ _typeIself
              _lhsOself =
                  _self
              _lhsOmiscerrors =
                  _typeImiscerrors
              _lhsOwarnings =
                  _typeIwarnings
              _typeOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typeOmiscerrors =
                  _lhsImiscerrors
              _typeOoptions =
                  _lhsIoptions
              _typeOtypeConstructors =
                  _lhsItypeConstructors
              _typeOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _typeIcontextRange,_typeImiscerrors,_typeIself,_typeItypevariables,_typeIwarnings) =
                  (type_ _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings )
          in  ( _lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOtype,_lhsOtypevariables,_lhsOunboundNames,_lhsOwarnings)))
-- AnnotatedTypes ----------------------------------------------
-- cata
sem_AnnotatedTypes :: AnnotatedTypes ->
                      T_AnnotatedTypes
sem_AnnotatedTypes list  =
    (Prelude.foldr sem_AnnotatedTypes_Cons sem_AnnotatedTypes_Nil (Prelude.map sem_AnnotatedType list) )
-- semantic domain
type T_AnnotatedTypes = Names ->
                        Names ->
                        ([Error]) ->
                        ([Error]) ->
                        Names ->
                        ([Option]) ->
                        (M.Map Name Int) ->
                        (M.Map Name TpScheme) ->
                        ([Warning]) ->
                        ( ([Error]),([Error]),AnnotatedTypes,Types,Names,Names,([Warning]))
sem_AnnotatedTypes_Cons :: T_AnnotatedType ->
                           T_AnnotatedTypes ->
                           T_AnnotatedTypes
sem_AnnotatedTypes_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOtypes :: Types
              _lhsOtypevariables :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: AnnotatedTypes
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOallValueConstructors :: Names
              _hdOkindErrors :: ([Error])
              _hdOmiscerrors :: ([Error])
              _hdOnamesInScope :: Names
              _hdOoptions :: ([Option])
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOvalueConstructors :: (M.Map Name TpScheme)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOallValueConstructors :: Names
              _tlOkindErrors :: ([Error])
              _tlOmiscerrors :: ([Error])
              _tlOnamesInScope :: Names
              _tlOoptions :: ([Option])
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOvalueConstructors :: (M.Map Name TpScheme)
              _tlOwarnings :: ([Warning])
              _hdIkindErrors :: ([Error])
              _hdImiscerrors :: ([Error])
              _hdIself :: AnnotatedType
              _hdItype :: Type
              _hdItypevariables :: Names
              _hdIunboundNames :: Names
              _hdIwarnings :: ([Warning])
              _tlIkindErrors :: ([Error])
              _tlImiscerrors :: ([Error])
              _tlIself :: AnnotatedTypes
              _tlItypes :: Types
              _tlItypevariables :: Names
              _tlIunboundNames :: Names
              _tlIwarnings :: ([Warning])
              _lhsOtypes =
                  _hdItype : _tlItypes
              _lhsOtypevariables =
                  _hdItypevariables  ++  _tlItypevariables
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _tlIkindErrors
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOallValueConstructors =
                  _lhsIallValueConstructors
              _hdOkindErrors =
                  _lhsIkindErrors
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOoptions =
                  _lhsIoptions
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOvalueConstructors =
                  _lhsIvalueConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOallValueConstructors =
                  _lhsIallValueConstructors
              _tlOkindErrors =
                  _hdIkindErrors
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOoptions =
                  _lhsIoptions
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOvalueConstructors =
                  _lhsIvalueConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIkindErrors,_hdImiscerrors,_hdIself,_hdItype,_hdItypevariables,_hdIunboundNames,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOallValueConstructors _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings )
              ( _tlIkindErrors,_tlImiscerrors,_tlIself,_tlItypes,_tlItypevariables,_tlIunboundNames,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOallValueConstructors _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings )
          in  ( _lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOtypes,_lhsOtypevariables,_lhsOunboundNames,_lhsOwarnings)))
sem_AnnotatedTypes_Nil :: T_AnnotatedTypes
sem_AnnotatedTypes_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOtypes :: Types
              _lhsOtypevariables :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: AnnotatedTypes
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _lhsOtypes =
                  []
              _lhsOtypevariables =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOtypes,_lhsOtypevariables,_lhsOunboundNames,_lhsOwarnings)))
-- Body --------------------------------------------------------
-- cata
sem_Body :: Body ->
            T_Body
sem_Body (Body_Body _range _importdeclarations _declarations )  =
    (sem_Body_Body (sem_Range _range ) (sem_ImportDeclarations _importdeclarations ) (sem_Declarations _declarations ) )
-- semantic domain
type T_Body = Names ->
              Names ->
              ClassEnvironment ->
              ([(ScopeInfo, Entity)]) ->
              ([(Name,Int)]) ->
              ([(Name,(Int,Tps -> Tp))]) ->
              ([(Name,TpScheme)]) ->
              ([Error]) ->
              ([Error]) ->
              Names ->
              ([(Name,(Int,Assoc))]) ->
              ([Option]) ->
              OrderedTypeSynonyms ->
              (M.Map Name Int) ->
              (M.Map Name TpScheme) ->
              ([Warning]) ->
              ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([(Name,Int)]),([(Name,(Int,Tps -> Tp))]),([(Name,TpScheme)]),Names,Names,([Error]),([Error]),([(Name,(Int,Assoc))]),Body,([(Name,TpScheme)]),Names,([Warning]))
sem_Body_Body :: T_Range ->
                 T_ImportDeclarations ->
                 T_Declarations ->
                 T_Body
sem_Body_Body range_ importdeclarations_ declarations_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _declarationsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOwarnings :: ([Warning])
              _declarationsOpreviousWasAlsoFB :: (Maybe Name)
              _declarationsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOmiscerrors :: ([Error])
              _importdeclarationsOimportedModules :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Body
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOimportedModules :: Names
              _lhsOkindErrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _declarationsOallTypeConstructors :: Names
              _declarationsOallValueConstructors :: Names
              _declarationsOclassEnvironment :: ClassEnvironment
              _declarationsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _declarationsOcollectTypeConstructors :: ([(Name,Int)])
              _declarationsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _declarationsOcollectValueConstructors :: ([(Name,TpScheme)])
              _declarationsOkindErrors :: ([Error])
              _declarationsOmiscerrors :: ([Error])
              _declarationsOnamesInScope :: Names
              _declarationsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _declarationsOoptions :: ([Option])
              _declarationsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _declarationsOtypeConstructors :: (M.Map Name Int)
              _declarationsOvalueConstructors :: (M.Map Name TpScheme)
              _declarationsOwarnings :: ([Warning])
              _rangeIself :: Range
              _importdeclarationsIimportedModules :: Names
              _importdeclarationsIself :: ImportDeclarations
              _declarationsIcollectInstances :: ([(Name, Instance)])
              _declarationsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _declarationsIcollectTypeConstructors :: ([(Name,Int)])
              _declarationsIcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _declarationsIcollectValueConstructors :: ([(Name,TpScheme)])
              _declarationsIdeclVarNames :: Names
              _declarationsIkindErrors :: ([Error])
              _declarationsImiscerrors :: ([Error])
              _declarationsIoperatorFixities :: ([(Name,(Int,Assoc))])
              _declarationsIpreviousWasAlsoFB :: (Maybe Name)
              _declarationsIrestrictedNames :: Names
              _declarationsIself :: Declarations
              _declarationsIsuspiciousFBs :: ([(Name,Name)])
              _declarationsItypeSignatures :: ([(Name,TpScheme)])
              _declarationsIunboundNames :: Names
              _declarationsIwarnings :: ([Warning])
              _declarationsOtypeSignatures =
                  []
              _lhsOwarnings =
                  _declarationsIwarnings ++
                  _suspiciousErrors
              _declarationsOpreviousWasAlsoFB =
                  Nothing
              _declarationsOsuspiciousFBs =
                  []
              _suspiciousErrors =
                  findSimilarFunctionBindings _declarationsItypeSignatures _declarationsIsuspiciousFBs
              _lhsOmiscerrors =
                  _typeSignatureErrors ++ _declarationsImiscerrors
              _typeSignatureErrors =
                  checkTypeSignatures _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
              _importdeclarationsOimportedModules =
                  []
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
              _lhsOcollectScopeInfos =
                  _declarationsIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _declarationsIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _declarationsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _declarationsIcollectValueConstructors
              _lhsOimportedModules =
                  _importdeclarationsIimportedModules
              _lhsOkindErrors =
                  _declarationsIkindErrors
              _lhsOoperatorFixities =
                  _declarationsIoperatorFixities
              _lhsOtypeSignatures =
                  _declarationsItypeSignatures
              _declarationsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _declarationsOallValueConstructors =
                  _lhsIallValueConstructors
              _declarationsOclassEnvironment =
                  _lhsIclassEnvironment
              _declarationsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _declarationsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _declarationsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _declarationsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _declarationsOkindErrors =
                  _lhsIkindErrors
              _declarationsOmiscerrors =
                  _lhsImiscerrors
              _declarationsOnamesInScope =
                  _lhsInamesInScope
              _declarationsOoperatorFixities =
                  _lhsIoperatorFixities
              _declarationsOoptions =
                  _lhsIoptions
              _declarationsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _declarationsOtypeConstructors =
                  _lhsItypeConstructors
              _declarationsOvalueConstructors =
                  _lhsIvalueConstructors
              _declarationsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _importdeclarationsIimportedModules,_importdeclarationsIself) =
                  (importdeclarations_ _importdeclarationsOimportedModules )
              ( _declarationsIcollectInstances,_declarationsIcollectScopeInfos,_declarationsIcollectTypeConstructors,_declarationsIcollectTypeSynonyms,_declarationsIcollectValueConstructors,_declarationsIdeclVarNames,_declarationsIkindErrors,_declarationsImiscerrors,_declarationsIoperatorFixities,_declarationsIpreviousWasAlsoFB,_declarationsIrestrictedNames,_declarationsIself,_declarationsIsuspiciousFBs,_declarationsItypeSignatures,_declarationsIunboundNames,_declarationsIwarnings) =
                  (declarations_ _declarationsOallTypeConstructors _declarationsOallValueConstructors _declarationsOclassEnvironment _declarationsOcollectScopeInfos _declarationsOcollectTypeConstructors _declarationsOcollectTypeSynonyms _declarationsOcollectValueConstructors _declarationsOkindErrors _declarationsOmiscerrors _declarationsOnamesInScope _declarationsOoperatorFixities _declarationsOoptions _declarationsOorderedTypeSynonyms _declarationsOpreviousWasAlsoFB _declarationsOsuspiciousFBs _declarationsOtypeConstructors _declarationsOtypeSignatures _declarationsOvalueConstructors _declarationsOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOimportedModules,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOself,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
-- Constructor -------------------------------------------------
-- cata
sem_Constructor :: Constructor ->
                   T_Constructor
sem_Constructor (Constructor_Constructor _range _constructor _types )  =
    (sem_Constructor_Constructor (sem_Range _range ) (sem_Name _constructor ) (sem_AnnotatedTypes _types ) )
sem_Constructor (Constructor_Infix _range _leftType _constructorOperator _rightType )  =
    (sem_Constructor_Infix (sem_Range _range ) (sem_AnnotatedType _leftType ) (sem_Name _constructorOperator ) (sem_AnnotatedType _rightType ) )
sem_Constructor (Constructor_Record _range _constructor _fieldDeclarations )  =
    (sem_Constructor_Record (sem_Range _range ) (sem_Name _constructor ) (sem_FieldDeclarations _fieldDeclarations ) )
-- semantic domain
type T_Constructor = Names ->
                     Names ->
                     ([(Name,TpScheme)]) ->
                     ([Error]) ->
                     ([Error]) ->
                     Names ->
                     ([Option]) ->
                     SimpleType ->
                     (M.Map Name Int) ->
                     (M.Map Name TpScheme) ->
                     ([Warning]) ->
                     ( ([(Name,TpScheme)]),([Error]),([Error]),Tps,Constructor,Names,Names,([Warning]))
sem_Constructor_Constructor :: T_Range ->
                               T_Name ->
                               T_AnnotatedTypes ->
                               T_Constructor
sem_Constructor_Constructor range_ constructor_ types_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIsimpletype
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOparameterTypes :: Tps
              _lhsOtypevariables :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Constructor
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _typesOallTypeConstructors :: Names
              _typesOallValueConstructors :: Names
              _typesOkindErrors :: ([Error])
              _typesOmiscerrors :: ([Error])
              _typesOnamesInScope :: Names
              _typesOoptions :: ([Option])
              _typesOtypeConstructors :: (M.Map Name Int)
              _typesOvalueConstructors :: (M.Map Name TpScheme)
              _typesOwarnings :: ([Warning])
              _rangeIself :: Range
              _constructorIself :: Name
              _typesIkindErrors :: ([Error])
              _typesImiscerrors :: ([Error])
              _typesIself :: AnnotatedTypes
              _typesItypes :: Types
              _typesItypevariables :: Names
              _typesIunboundNames :: Names
              _typesIwarnings :: ([Warning])
              _lhsOcollectValueConstructors =
                  (_constructorIself, _typeScheme) : _lhsIcollectValueConstructors
              _lhsOparameterTypes =
                  _tps
              _typeScheme =
                  generalizeAll ([] .=>. foldr (.->.) _tp _tps)
              __tup2 =
                  convertFromSimpleTypeAndTypes _lhsIsimpletype _typesItypes
              (_tp,_) =
                  __tup2
              (_,_tps) =
                  __tup2
              _lhsOtypevariables =
                  _typesItypevariables
              _lhsOunboundNames =
                  _typesIunboundNames
              _self =
                  Constructor_Constructor _rangeIself _constructorIself _typesIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _typesIkindErrors
              _lhsOmiscerrors =
                  _typesImiscerrors
              _lhsOwarnings =
                  _typesIwarnings
              _typesOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typesOallValueConstructors =
                  _lhsIallValueConstructors
              _typesOkindErrors =
                  _lhsIkindErrors
              _typesOmiscerrors =
                  _lhsImiscerrors
              _typesOnamesInScope =
                  _lhsInamesInScope
              _typesOoptions =
                  _lhsIoptions
              _typesOtypeConstructors =
                  _lhsItypeConstructors
              _typesOvalueConstructors =
                  _lhsIvalueConstructors
              _typesOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _constructorIself) =
                  (constructor_ )
              ( _typesIkindErrors,_typesImiscerrors,_typesIself,_typesItypes,_typesItypevariables,_typesIunboundNames,_typesIwarnings) =
                  (types_ _typesOallTypeConstructors _typesOallValueConstructors _typesOkindErrors _typesOmiscerrors _typesOnamesInScope _typesOoptions _typesOtypeConstructors _typesOvalueConstructors _typesOwarnings )
          in  ( _lhsOcollectValueConstructors,_lhsOkindErrors,_lhsOmiscerrors,_lhsOparameterTypes,_lhsOself,_lhsOtypevariables,_lhsOunboundNames,_lhsOwarnings)))
sem_Constructor_Infix :: T_Range ->
                         T_AnnotatedType ->
                         T_Name ->
                         T_AnnotatedType ->
                         T_Constructor
sem_Constructor_Infix range_ leftType_ constructorOperator_ rightType_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIsimpletype
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOparameterTypes :: Tps
              _lhsOtypevariables :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Constructor
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _leftTypeOallTypeConstructors :: Names
              _leftTypeOallValueConstructors :: Names
              _leftTypeOkindErrors :: ([Error])
              _leftTypeOmiscerrors :: ([Error])
              _leftTypeOnamesInScope :: Names
              _leftTypeOoptions :: ([Option])
              _leftTypeOtypeConstructors :: (M.Map Name Int)
              _leftTypeOvalueConstructors :: (M.Map Name TpScheme)
              _leftTypeOwarnings :: ([Warning])
              _rightTypeOallTypeConstructors :: Names
              _rightTypeOallValueConstructors :: Names
              _rightTypeOkindErrors :: ([Error])
              _rightTypeOmiscerrors :: ([Error])
              _rightTypeOnamesInScope :: Names
              _rightTypeOoptions :: ([Option])
              _rightTypeOtypeConstructors :: (M.Map Name Int)
              _rightTypeOvalueConstructors :: (M.Map Name TpScheme)
              _rightTypeOwarnings :: ([Warning])
              _rangeIself :: Range
              _leftTypeIkindErrors :: ([Error])
              _leftTypeImiscerrors :: ([Error])
              _leftTypeIself :: AnnotatedType
              _leftTypeItype :: Type
              _leftTypeItypevariables :: Names
              _leftTypeIunboundNames :: Names
              _leftTypeIwarnings :: ([Warning])
              _constructorOperatorIself :: Name
              _rightTypeIkindErrors :: ([Error])
              _rightTypeImiscerrors :: ([Error])
              _rightTypeIself :: AnnotatedType
              _rightTypeItype :: Type
              _rightTypeItypevariables :: Names
              _rightTypeIunboundNames :: Names
              _rightTypeIwarnings :: ([Warning])
              _lhsOcollectValueConstructors =
                  (_constructorOperatorIself, _typeScheme) : _lhsIcollectValueConstructors
              _lhsOparameterTypes =
                  _tps
              _typeScheme =
                  generalizeAll ([] .=>. foldr (.->.) _tp _tps)
              __tup3 =
                  convertFromSimpleTypeAndTypes _lhsIsimpletype [_leftTypeItype,_rightTypeItype]
              (_tp,_) =
                  __tup3
              (_,_tps) =
                  __tup3
              _lhsOtypevariables =
                  _leftTypeItypevariables  ++  _rightTypeItypevariables
              _lhsOunboundNames =
                  _leftTypeIunboundNames ++ _rightTypeIunboundNames
              _self =
                  Constructor_Infix _rangeIself _leftTypeIself _constructorOperatorIself _rightTypeIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _rightTypeIkindErrors
              _lhsOmiscerrors =
                  _rightTypeImiscerrors
              _lhsOwarnings =
                  _rightTypeIwarnings
              _leftTypeOallTypeConstructors =
                  _lhsIallTypeConstructors
              _leftTypeOallValueConstructors =
                  _lhsIallValueConstructors
              _leftTypeOkindErrors =
                  _lhsIkindErrors
              _leftTypeOmiscerrors =
                  _lhsImiscerrors
              _leftTypeOnamesInScope =
                  _lhsInamesInScope
              _leftTypeOoptions =
                  _lhsIoptions
              _leftTypeOtypeConstructors =
                  _lhsItypeConstructors
              _leftTypeOvalueConstructors =
                  _lhsIvalueConstructors
              _leftTypeOwarnings =
                  _lhsIwarnings
              _rightTypeOallTypeConstructors =
                  _lhsIallTypeConstructors
              _rightTypeOallValueConstructors =
                  _lhsIallValueConstructors
              _rightTypeOkindErrors =
                  _leftTypeIkindErrors
              _rightTypeOmiscerrors =
                  _leftTypeImiscerrors
              _rightTypeOnamesInScope =
                  _lhsInamesInScope
              _rightTypeOoptions =
                  _lhsIoptions
              _rightTypeOtypeConstructors =
                  _lhsItypeConstructors
              _rightTypeOvalueConstructors =
                  _lhsIvalueConstructors
              _rightTypeOwarnings =
                  _leftTypeIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _leftTypeIkindErrors,_leftTypeImiscerrors,_leftTypeIself,_leftTypeItype,_leftTypeItypevariables,_leftTypeIunboundNames,_leftTypeIwarnings) =
                  (leftType_ _leftTypeOallTypeConstructors _leftTypeOallValueConstructors _leftTypeOkindErrors _leftTypeOmiscerrors _leftTypeOnamesInScope _leftTypeOoptions _leftTypeOtypeConstructors _leftTypeOvalueConstructors _leftTypeOwarnings )
              ( _constructorOperatorIself) =
                  (constructorOperator_ )
              ( _rightTypeIkindErrors,_rightTypeImiscerrors,_rightTypeIself,_rightTypeItype,_rightTypeItypevariables,_rightTypeIunboundNames,_rightTypeIwarnings) =
                  (rightType_ _rightTypeOallTypeConstructors _rightTypeOallValueConstructors _rightTypeOkindErrors _rightTypeOmiscerrors _rightTypeOnamesInScope _rightTypeOoptions _rightTypeOtypeConstructors _rightTypeOvalueConstructors _rightTypeOwarnings )
          in  ( _lhsOcollectValueConstructors,_lhsOkindErrors,_lhsOmiscerrors,_lhsOparameterTypes,_lhsOself,_lhsOtypevariables,_lhsOunboundNames,_lhsOwarnings)))
sem_Constructor_Record :: T_Range ->
                          T_Name ->
                          T_FieldDeclarations ->
                          T_Constructor
sem_Constructor_Record range_ constructor_ fieldDeclarations_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIsimpletype
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOparameterTypes :: Tps
              _lhsOtypevariables :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Constructor
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _fieldDeclarationsOmiscerrors :: ([Error])
              _fieldDeclarationsOnamesInScope :: Names
              _fieldDeclarationsOoptions :: ([Option])
              _rangeIself :: Range
              _constructorIself :: Name
              _fieldDeclarationsImiscerrors :: ([Error])
              _fieldDeclarationsIself :: FieldDeclarations
              _fieldDeclarationsIunboundNames :: Names
              _lhsOparameterTypes =
                  []
              _lhsOtypevariables =
                  []
              _lhsOunboundNames =
                  _fieldDeclarationsIunboundNames
              _self =
                  Constructor_Record _rangeIself _constructorIself _fieldDeclarationsIself
              _lhsOself =
                  _self
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _fieldDeclarationsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              _fieldDeclarationsOmiscerrors =
                  _lhsImiscerrors
              _fieldDeclarationsOnamesInScope =
                  _lhsInamesInScope
              _fieldDeclarationsOoptions =
                  _lhsIoptions
              ( _rangeIself) =
                  (range_ )
              ( _constructorIself) =
                  (constructor_ )
              ( _fieldDeclarationsImiscerrors,_fieldDeclarationsIself,_fieldDeclarationsIunboundNames) =
                  (fieldDeclarations_ _fieldDeclarationsOmiscerrors _fieldDeclarationsOnamesInScope _fieldDeclarationsOoptions )
          in  ( _lhsOcollectValueConstructors,_lhsOkindErrors,_lhsOmiscerrors,_lhsOparameterTypes,_lhsOself,_lhsOtypevariables,_lhsOunboundNames,_lhsOwarnings)))
-- Constructors ------------------------------------------------
-- cata
sem_Constructors :: Constructors ->
                    T_Constructors
sem_Constructors list  =
    (Prelude.foldr sem_Constructors_Cons sem_Constructors_Nil (Prelude.map sem_Constructor list) )
-- semantic domain
type T_Constructors = Names ->
                      Names ->
                      ([(Name,TpScheme)]) ->
                      ([Error]) ->
                      ([Error]) ->
                      Names ->
                      ([Option]) ->
                      SimpleType ->
                      (M.Map Name Int) ->
                      (M.Map Name TpScheme) ->
                      ([Warning]) ->
                      ( ([(Name,TpScheme)]),([Error]),([Error]),Tps,Constructors,Names,Names,([Warning]))
sem_Constructors_Cons :: T_Constructor ->
                         T_Constructors ->
                         T_Constructors
sem_Constructors_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIsimpletype
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOparameterTypes :: Tps
              _lhsOtypevariables :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Constructors
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOallValueConstructors :: Names
              _hdOcollectValueConstructors :: ([(Name,TpScheme)])
              _hdOkindErrors :: ([Error])
              _hdOmiscerrors :: ([Error])
              _hdOnamesInScope :: Names
              _hdOoptions :: ([Option])
              _hdOsimpletype :: SimpleType
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOvalueConstructors :: (M.Map Name TpScheme)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOallValueConstructors :: Names
              _tlOcollectValueConstructors :: ([(Name,TpScheme)])
              _tlOkindErrors :: ([Error])
              _tlOmiscerrors :: ([Error])
              _tlOnamesInScope :: Names
              _tlOoptions :: ([Option])
              _tlOsimpletype :: SimpleType
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOvalueConstructors :: (M.Map Name TpScheme)
              _tlOwarnings :: ([Warning])
              _hdIcollectValueConstructors :: ([(Name,TpScheme)])
              _hdIkindErrors :: ([Error])
              _hdImiscerrors :: ([Error])
              _hdIparameterTypes :: Tps
              _hdIself :: Constructor
              _hdItypevariables :: Names
              _hdIunboundNames :: Names
              _hdIwarnings :: ([Warning])
              _tlIcollectValueConstructors :: ([(Name,TpScheme)])
              _tlIkindErrors :: ([Error])
              _tlImiscerrors :: ([Error])
              _tlIparameterTypes :: Tps
              _tlIself :: Constructors
              _tlItypevariables :: Names
              _tlIunboundNames :: Names
              _tlIwarnings :: ([Warning])
              _lhsOparameterTypes =
                  _hdIparameterTypes  ++  _tlIparameterTypes
              _lhsOtypevariables =
                  _hdItypevariables  ++  _tlItypevariables
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcollectValueConstructors =
                  _tlIcollectValueConstructors
              _lhsOkindErrors =
                  _tlIkindErrors
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOallValueConstructors =
                  _lhsIallValueConstructors
              _hdOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _hdOkindErrors =
                  _lhsIkindErrors
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOoptions =
                  _lhsIoptions
              _hdOsimpletype =
                  _lhsIsimpletype
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOvalueConstructors =
                  _lhsIvalueConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOallValueConstructors =
                  _lhsIallValueConstructors
              _tlOcollectValueConstructors =
                  _hdIcollectValueConstructors
              _tlOkindErrors =
                  _hdIkindErrors
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOoptions =
                  _lhsIoptions
              _tlOsimpletype =
                  _lhsIsimpletype
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOvalueConstructors =
                  _lhsIvalueConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIcollectValueConstructors,_hdIkindErrors,_hdImiscerrors,_hdIparameterTypes,_hdIself,_hdItypevariables,_hdIunboundNames,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOallValueConstructors _hdOcollectValueConstructors _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOsimpletype _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings )
              ( _tlIcollectValueConstructors,_tlIkindErrors,_tlImiscerrors,_tlIparameterTypes,_tlIself,_tlItypevariables,_tlIunboundNames,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOallValueConstructors _tlOcollectValueConstructors _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOsimpletype _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings )
          in  ( _lhsOcollectValueConstructors,_lhsOkindErrors,_lhsOmiscerrors,_lhsOparameterTypes,_lhsOself,_lhsOtypevariables,_lhsOunboundNames,_lhsOwarnings)))
sem_Constructors_Nil :: T_Constructors
sem_Constructors_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIsimpletype
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOparameterTypes :: Tps
              _lhsOtypevariables :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Constructors
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _lhsOparameterTypes =
                  []
              _lhsOtypevariables =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOcollectValueConstructors,_lhsOkindErrors,_lhsOmiscerrors,_lhsOparameterTypes,_lhsOself,_lhsOtypevariables,_lhsOunboundNames,_lhsOwarnings)))
-- ContextItem -------------------------------------------------
-- cata
sem_ContextItem :: ContextItem ->
                   T_ContextItem
sem_ContextItem (ContextItem_ContextItem _range _name _types )  =
    (sem_ContextItem_ContextItem (sem_Range _range ) (sem_Name _name ) (sem_Types _types ) )
-- semantic domain
type T_ContextItem = Names ->
                     ([Error]) ->
                     ([Option]) ->
                     (M.Map Name Int) ->
                     ([Warning]) ->
                     ( ([Range]),([Name]),([Error]),ContextItem,([Warning]))
sem_ContextItem_ContextItem :: T_Range ->
                               T_Name ->
                               T_Types ->
                               T_ContextItem
sem_ContextItem_ContextItem range_ name_ types_  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOcontextRanges :: ([Range])
              _lhsOcontextVars :: ([Name])
              _lhsOmiscerrors :: ([Error])
              _lhsOself :: ContextItem
              _lhsOwarnings :: ([Warning])
              _typesOallTypeConstructors :: Names
              _typesOmiscerrors :: ([Error])
              _typesOoptions :: ([Option])
              _typesOtypeConstructors :: (M.Map Name Int)
              _typesOwarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _typesImiscerrors :: ([Error])
              _typesIself :: Types
              _typesItypevariables :: Names
              _typesIwarnings :: ([Warning])
              _lhsOcontextRanges =
                  [_rangeIself]
              _lhsOcontextVars =
                  _typesItypevariables
              _lhsOmiscerrors =
                  if elem (getNameName _nameIself) (M.keys standardClasses)
                     then _typesImiscerrors
                     else UnknownClass _nameIself : _typesImiscerrors
              _tyconEnv =
                  internalError "PartialSyntax.ag" "n/a" "ContextItem.ContextItem"
              _self =
                  ContextItem_ContextItem _rangeIself _nameIself _typesIself
              _lhsOself =
                  _self
              _lhsOwarnings =
                  _typesIwarnings
              _typesOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typesOmiscerrors =
                  _lhsImiscerrors
              _typesOoptions =
                  _lhsIoptions
              _typesOtypeConstructors =
                  _lhsItypeConstructors
              _typesOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _typesImiscerrors,_typesIself,_typesItypevariables,_typesIwarnings) =
                  (types_ _typesOallTypeConstructors _typesOmiscerrors _typesOoptions _typesOtypeConstructors _typesOwarnings )
          in  ( _lhsOcontextRanges,_lhsOcontextVars,_lhsOmiscerrors,_lhsOself,_lhsOwarnings)))
-- ContextItems ------------------------------------------------
-- cata
sem_ContextItems :: ContextItems ->
                    T_ContextItems
sem_ContextItems list  =
    (Prelude.foldr sem_ContextItems_Cons sem_ContextItems_Nil (Prelude.map sem_ContextItem list) )
-- semantic domain
type T_ContextItems = Names ->
                      ([Error]) ->
                      ([Option]) ->
                      (M.Map Name Int) ->
                      ([Warning]) ->
                      ( ([Range]),([Name]),([Error]),ContextItems,([Warning]))
sem_ContextItems_Cons :: T_ContextItem ->
                         T_ContextItems ->
                         T_ContextItems
sem_ContextItems_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOcontextRanges :: ([Range])
              _lhsOcontextVars :: ([Name])
              _lhsOself :: ContextItems
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOmiscerrors :: ([Error])
              _hdOoptions :: ([Option])
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOmiscerrors :: ([Error])
              _tlOoptions :: ([Option])
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOwarnings :: ([Warning])
              _hdIcontextRanges :: ([Range])
              _hdIcontextVars :: ([Name])
              _hdImiscerrors :: ([Error])
              _hdIself :: ContextItem
              _hdIwarnings :: ([Warning])
              _tlIcontextRanges :: ([Range])
              _tlIcontextVars :: ([Name])
              _tlImiscerrors :: ([Error])
              _tlIself :: ContextItems
              _tlIwarnings :: ([Warning])
              _lhsOcontextRanges =
                  _hdIcontextRanges ++ _tlIcontextRanges
              _lhsOcontextVars =
                  _hdIcontextVars  ++  _tlIcontextVars
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOoptions =
                  _lhsIoptions
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOoptions =
                  _lhsIoptions
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIcontextRanges,_hdIcontextVars,_hdImiscerrors,_hdIself,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOmiscerrors _hdOoptions _hdOtypeConstructors _hdOwarnings )
              ( _tlIcontextRanges,_tlIcontextVars,_tlImiscerrors,_tlIself,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOmiscerrors _tlOoptions _tlOtypeConstructors _tlOwarnings )
          in  ( _lhsOcontextRanges,_lhsOcontextVars,_lhsOmiscerrors,_lhsOself,_lhsOwarnings)))
sem_ContextItems_Nil :: T_ContextItems
sem_ContextItems_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOcontextRanges :: ([Range])
              _lhsOcontextVars :: ([Name])
              _lhsOself :: ContextItems
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _lhsOcontextRanges =
                  []
              _lhsOcontextVars =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOcontextRanges,_lhsOcontextVars,_lhsOmiscerrors,_lhsOself,_lhsOwarnings)))
-- Declaration -------------------------------------------------
-- cata
sem_Declaration :: Declaration ->
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
type T_Declaration = Names ->
                     Names ->
                     ClassEnvironment ->
                     ([(ScopeInfo, Entity)]) ->
                     ([(Name,Int)]) ->
                     ([(Name,(Int,Tps -> Tp))]) ->
                     ([(Name,TpScheme)]) ->
                     ([Error]) ->
                     ([Error]) ->
                     Names ->
                     ([(Name,(Int,Assoc))]) ->
                     ([Option]) ->
                     OrderedTypeSynonyms ->
                     (Maybe Name) ->
                     ([(Name,Name)]) ->
                     (M.Map Name Int) ->
                     ([(Name,TpScheme)]) ->
                     (M.Map Name TpScheme) ->
                     ([Warning]) ->
                     ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([(Name,Int)]),([(Name,(Int,Tps -> Tp))]),([(Name,TpScheme)]),Names,([Error]),([Error]),([(Name,(Int,Assoc))]),(Maybe Name),Names,Declaration,([(Name,Name)]),([(Name,TpScheme)]),Names,([Warning]))
sem_Declaration_Class :: T_Range ->
                         T_ContextItems ->
                         T_SimpleType ->
                         T_MaybeDeclarations ->
                         T_Declaration
sem_Declaration_Class range_ context_ simpletype_ where_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOwarnings :: ([Warning])
              _contextOallTypeConstructors :: Names
              _contextOmiscerrors :: ([Error])
              _contextOoptions :: ([Option])
              _contextOtypeConstructors :: (M.Map Name Int)
              _contextOwarnings :: ([Warning])
              _whereOallTypeConstructors :: Names
              _whereOallValueConstructors :: Names
              _whereOclassEnvironment :: ClassEnvironment
              _whereOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _whereOkindErrors :: ([Error])
              _whereOmiscerrors :: ([Error])
              _whereOnamesInScope :: Names
              _whereOoptions :: ([Option])
              _whereOorderedTypeSynonyms :: OrderedTypeSynonyms
              _whereOtypeConstructors :: (M.Map Name Int)
              _whereOunboundNames :: Names
              _whereOvalueConstructors :: (M.Map Name TpScheme)
              _whereOwarnings :: ([Warning])
              _rangeIself :: Range
              _contextIcontextRanges :: ([Range])
              _contextIcontextVars :: ([Name])
              _contextImiscerrors :: ([Error])
              _contextIself :: ContextItems
              _contextIwarnings :: ([Warning])
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _whereIcollectInstances :: ([(Name, Instance)])
              _whereIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _whereIkindErrors :: ([Error])
              _whereImiscerrors :: ([Error])
              _whereInamesInScope :: Names
              _whereIself :: MaybeDeclarations
              _whereIunboundNames :: Names
              _whereIwarnings :: ([Warning])
              _lhsOpreviousWasAlsoFB =
                  Nothing
              __tup4 =
                  internalError "PartialSyntax.ag" "n/a" "Declaration.Class"
              (_assumptions,_,_) =
                  __tup4
              (_,_constraints,_) =
                  __tup4
              (_,_,_unboundNames) =
                  __tup4
              _lhsOcollectInstances =
                  _whereIcollectInstances
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOunboundNames =
                  _unboundNames
              _self =
                  Declaration_Class _rangeIself _contextIself _simpletypeIself _whereIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _whereIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOkindErrors =
                  _whereIkindErrors
              _lhsOmiscerrors =
                  _whereImiscerrors
              _lhsOoperatorFixities =
                  _lhsIoperatorFixities
              _lhsOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOwarnings =
                  _whereIwarnings
              _contextOallTypeConstructors =
                  _lhsIallTypeConstructors
              _contextOmiscerrors =
                  _lhsImiscerrors
              _contextOoptions =
                  _lhsIoptions
              _contextOtypeConstructors =
                  _lhsItypeConstructors
              _contextOwarnings =
                  _lhsIwarnings
              _whereOallTypeConstructors =
                  _lhsIallTypeConstructors
              _whereOallValueConstructors =
                  _lhsIallValueConstructors
              _whereOclassEnvironment =
                  _lhsIclassEnvironment
              _whereOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _whereOkindErrors =
                  _lhsIkindErrors
              _whereOmiscerrors =
                  _contextImiscerrors
              _whereOnamesInScope =
                  _lhsInamesInScope
              _whereOoptions =
                  _lhsIoptions
              _whereOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _whereOtypeConstructors =
                  _lhsItypeConstructors
              _whereOunboundNames =
                  _unboundNames
              _whereOvalueConstructors =
                  _lhsIvalueConstructors
              _whereOwarnings =
                  _contextIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _contextIcontextRanges,_contextIcontextVars,_contextImiscerrors,_contextIself,_contextIwarnings) =
                  (context_ _contextOallTypeConstructors _contextOmiscerrors _contextOoptions _contextOtypeConstructors _contextOwarnings )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _whereIcollectInstances,_whereIcollectScopeInfos,_whereIkindErrors,_whereImiscerrors,_whereInamesInScope,_whereIself,_whereIunboundNames,_whereIwarnings) =
                  (where_ _whereOallTypeConstructors _whereOallValueConstructors _whereOclassEnvironment _whereOcollectScopeInfos _whereOkindErrors _whereOmiscerrors _whereOnamesInScope _whereOoptions _whereOorderedTypeSynonyms _whereOtypeConstructors _whereOunboundNames _whereOvalueConstructors _whereOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
sem_Declaration_Data :: T_Range ->
                        T_ContextItems ->
                        T_SimpleType ->
                        T_Constructors ->
                        T_Names ->
                        T_Declaration
sem_Declaration_Data range_ context_ simpletype_ constructors_ derivings_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _constructorsOsimpletype :: SimpleType
              _lhsOwarnings :: ([Warning])
              _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOmiscerrors :: ([Error])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _contextOallTypeConstructors :: Names
              _contextOmiscerrors :: ([Error])
              _contextOoptions :: ([Option])
              _contextOtypeConstructors :: (M.Map Name Int)
              _contextOwarnings :: ([Warning])
              _constructorsOallTypeConstructors :: Names
              _constructorsOallValueConstructors :: Names
              _constructorsOcollectValueConstructors :: ([(Name,TpScheme)])
              _constructorsOkindErrors :: ([Error])
              _constructorsOmiscerrors :: ([Error])
              _constructorsOnamesInScope :: Names
              _constructorsOoptions :: ([Option])
              _constructorsOtypeConstructors :: (M.Map Name Int)
              _constructorsOvalueConstructors :: (M.Map Name TpScheme)
              _constructorsOwarnings :: ([Warning])
              _rangeIself :: Range
              _contextIcontextRanges :: ([Range])
              _contextIcontextVars :: ([Name])
              _contextImiscerrors :: ([Error])
              _contextIself :: ContextItems
              _contextIwarnings :: ([Warning])
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _constructorsIcollectValueConstructors :: ([(Name,TpScheme)])
              _constructorsIkindErrors :: ([Error])
              _constructorsImiscerrors :: ([Error])
              _constructorsIparameterTypes :: Tps
              _constructorsIself :: Constructors
              _constructorsItypevariables :: Names
              _constructorsIunboundNames :: Names
              _constructorsIwarnings :: ([Warning])
              _derivingsIself :: Names
              _lhsOcollectTypeConstructors =
                  (_simpletypeIname,length _simpletypeItypevariables) : _lhsIcollectTypeConstructors
              _lhsOcollectInstances =
                  [ (cl, makeInstance (show cl) (length _simpletypeItypevariables) (show _simpletypeIname) )
                  | cl <- _derivingsIself
                  ]
              _constructorsOsimpletype =
                  _simpletypeIself
              _lhsOwarnings =
                  map (Unused TypeVariable) _unused ++ _lhsIwarnings
              _lhsOpreviousWasAlsoFB =
                  Nothing
              _lhsOmiscerrors =
                  concat [ makeDuplicated TypeVariable _doubles
                         , makeUndefined TypeVariable _undef _simpletypeItypevariables
                         , _lhsImiscerrors
                         , _unknCls
                         , if null _unknCls then _cantDer else []
                         ]
              _unused =
                  filter (`notElem` _constructorsItypevariables) _simpletypeItypevariables
              _doubles =
                  filter ((>1) . length) . group . sort $        _simpletypeItypevariables
              _undef =
                  filter (`notElem` _simpletypeItypevariables)   _constructorsItypevariables
              _unknCls =
                  [ if className `elem` [ "Num", "Enum", "Ord" ]
                     then NonDerivableClass c
                     else UnknownClass c
                  | c <- _derivingsIself, let className = show c
                  , className `notElem` ["Show", "Eq"]
                  ]
              _cantDer =
                  [ CannotDerive c [ tp | ReductionError (Predicate _ tp) <- errs ]
                  | c <- _derivingsIself
                  , let preds     = map (Predicate (show c)) _constructorsIparameterTypes
                        (_, errs) = contextReduction _lhsIorderedTypeSynonyms _lhsIclassEnvironment preds
                  , not (null errs)
                  ]
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOunboundNames =
                  _constructorsIunboundNames
              _self =
                  Declaration_Data _rangeIself _contextIself _simpletypeIself _constructorsIself _derivingsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _constructorsIcollectValueConstructors
              _lhsOkindErrors =
                  _constructorsIkindErrors
              _lhsOoperatorFixities =
                  _lhsIoperatorFixities
              _lhsOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _contextOallTypeConstructors =
                  _lhsIallTypeConstructors
              _contextOmiscerrors =
                  _lhsImiscerrors
              _contextOoptions =
                  _lhsIoptions
              _contextOtypeConstructors =
                  _lhsItypeConstructors
              _contextOwarnings =
                  _lhsIwarnings
              _constructorsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _constructorsOallValueConstructors =
                  _lhsIallValueConstructors
              _constructorsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _constructorsOkindErrors =
                  _lhsIkindErrors
              _constructorsOmiscerrors =
                  _contextImiscerrors
              _constructorsOnamesInScope =
                  _lhsInamesInScope
              _constructorsOoptions =
                  _lhsIoptions
              _constructorsOtypeConstructors =
                  _lhsItypeConstructors
              _constructorsOvalueConstructors =
                  _lhsIvalueConstructors
              _constructorsOwarnings =
                  _contextIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _contextIcontextRanges,_contextIcontextVars,_contextImiscerrors,_contextIself,_contextIwarnings) =
                  (context_ _contextOallTypeConstructors _contextOmiscerrors _contextOoptions _contextOtypeConstructors _contextOwarnings )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _constructorsIcollectValueConstructors,_constructorsIkindErrors,_constructorsImiscerrors,_constructorsIparameterTypes,_constructorsIself,_constructorsItypevariables,_constructorsIunboundNames,_constructorsIwarnings) =
                  (constructors_ _constructorsOallTypeConstructors _constructorsOallValueConstructors _constructorsOcollectValueConstructors _constructorsOkindErrors _constructorsOmiscerrors _constructorsOnamesInScope _constructorsOoptions _constructorsOsimpletype _constructorsOtypeConstructors _constructorsOvalueConstructors _constructorsOwarnings )
              ( _derivingsIself) =
                  (derivings_ )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
sem_Declaration_Default :: T_Range ->
                           T_Types ->
                           T_Declaration
sem_Declaration_Default range_ types_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOwarnings :: ([Warning])
              _typesOallTypeConstructors :: Names
              _typesOmiscerrors :: ([Error])
              _typesOoptions :: ([Option])
              _typesOtypeConstructors :: (M.Map Name Int)
              _typesOwarnings :: ([Warning])
              _rangeIself :: Range
              _typesImiscerrors :: ([Error])
              _typesIself :: Types
              _typesItypevariables :: Names
              _typesIwarnings :: ([Warning])
              _lhsOpreviousWasAlsoFB =
                  Nothing
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Declaration_Default _rangeIself _typesIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _typesImiscerrors
              _lhsOoperatorFixities =
                  _lhsIoperatorFixities
              _lhsOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOwarnings =
                  _typesIwarnings
              _typesOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typesOmiscerrors =
                  _lhsImiscerrors
              _typesOoptions =
                  _lhsIoptions
              _typesOtypeConstructors =
                  _lhsItypeConstructors
              _typesOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _typesImiscerrors,_typesIself,_typesItypevariables,_typesIwarnings) =
                  (types_ _typesOallTypeConstructors _typesOmiscerrors _typesOoptions _typesOtypeConstructors _typesOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
sem_Declaration_Empty :: T_Range ->
                         T_Declaration
sem_Declaration_Empty range_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOwarnings :: ([Warning])
              _rangeIself :: Range
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Declaration_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOoperatorFixities =
                  _lhsIoperatorFixities
              _lhsOpreviousWasAlsoFB =
                  _lhsIpreviousWasAlsoFB
              _lhsOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
sem_Declaration_Fixity :: T_Range ->
                          T_Fixity ->
                          T_MaybeInt ->
                          T_Names ->
                          T_Declaration
sem_Declaration_Fixity range_ fixity_ priority_ operators_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOwarnings :: ([Warning])
              _rangeIself :: Range
              _fixityIself :: Fixity
              _priorityIself :: MaybeInt
              _operatorsIself :: Names
              _lhsOoperatorFixities =
                  let associativity = case _fixityIself of
                                         Fixity_Infix _  -> AssocNone
                                         Fixity_Infixl _ -> AssocLeft
                                         Fixity_Infixr _ -> AssocRight
                      priority      = case _priorityIself of
                                         MaybeInt_Just i  -> i
                                         MaybeInt_Nothing -> 9
                  in [ (name, (priority, associativity)) | name <- _operatorsIself ] ++ _lhsIoperatorFixities
              _lhsOpreviousWasAlsoFB =
                  Nothing
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Declaration_Fixity _rangeIself _fixityIself _priorityIself _operatorsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _fixityIself) =
                  (fixity_ )
              ( _priorityIself) =
                  (priority_ )
              ( _operatorsIself) =
                  (operators_ )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
sem_Declaration_FunctionBindings :: T_Range ->
                                    T_FunctionBindings ->
                                    T_Declaration
sem_Declaration_FunctionBindings range_ bindings_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOdeclVarNames :: Names
              _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOmiscerrors :: ([Error])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOwarnings :: ([Warning])
              _bindingsOallTypeConstructors :: Names
              _bindingsOallValueConstructors :: Names
              _bindingsOclassEnvironment :: ClassEnvironment
              _bindingsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _bindingsOkindErrors :: ([Error])
              _bindingsOmiscerrors :: ([Error])
              _bindingsOnamesInScope :: Names
              _bindingsOoptions :: ([Option])
              _bindingsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _bindingsOtypeConstructors :: (M.Map Name Int)
              _bindingsOvalueConstructors :: (M.Map Name TpScheme)
              _bindingsOwarnings :: ([Warning])
              _rangeIself :: Range
              _bindingsIarities :: ( [Int] )
              _bindingsIcollectInstances :: ([(Name, Instance)])
              _bindingsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _bindingsIkindErrors :: ([Error])
              _bindingsImiscerrors :: ([Error])
              _bindingsIname :: Name
              _bindingsIself :: FunctionBindings
              _bindingsIunboundNames :: Names
              _bindingsIwarnings :: ([Warning])
              _lhsOdeclVarNames =
                  [_bindingsIname]
              _lhsOpreviousWasAlsoFB =
                  Just _bindingsIname
              _lhsOsuspiciousFBs =
                  case _lhsIpreviousWasAlsoFB of
                     Just name | show name `similar` show _bindingsIname
                        -> (name,_bindingsIname) : _lhsIsuspiciousFBs
                     _  -> _lhsIsuspiciousFBs
              _lhsOmiscerrors =
                  _arityErrors ++ _bindingsImiscerrors
              _arityErrors =
                  if all (== head _bindingsIarities) _bindingsIarities
                    then []
                    else [ DefArityMismatch _bindingsIname (mode _bindingsIarities) _rangeIself ]
              _lhsOcollectInstances =
                  _bindingsIcollectInstances
              _lhsOrestrictedNames =
                  []
              _lhsOunboundNames =
                  _bindingsIunboundNames
              _self =
                  Declaration_FunctionBindings _rangeIself _bindingsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _bindingsIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOkindErrors =
                  _bindingsIkindErrors
              _lhsOoperatorFixities =
                  _lhsIoperatorFixities
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOwarnings =
                  _bindingsIwarnings
              _bindingsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _bindingsOallValueConstructors =
                  _lhsIallValueConstructors
              _bindingsOclassEnvironment =
                  _lhsIclassEnvironment
              _bindingsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _bindingsOkindErrors =
                  _lhsIkindErrors
              _bindingsOmiscerrors =
                  _lhsImiscerrors
              _bindingsOnamesInScope =
                  _lhsInamesInScope
              _bindingsOoptions =
                  _lhsIoptions
              _bindingsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _bindingsOtypeConstructors =
                  _lhsItypeConstructors
              _bindingsOvalueConstructors =
                  _lhsIvalueConstructors
              _bindingsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _bindingsIarities,_bindingsIcollectInstances,_bindingsIcollectScopeInfos,_bindingsIkindErrors,_bindingsImiscerrors,_bindingsIname,_bindingsIself,_bindingsIunboundNames,_bindingsIwarnings) =
                  (bindings_ _bindingsOallTypeConstructors _bindingsOallValueConstructors _bindingsOclassEnvironment _bindingsOcollectScopeInfos _bindingsOkindErrors _bindingsOmiscerrors _bindingsOnamesInScope _bindingsOoptions _bindingsOorderedTypeSynonyms _bindingsOtypeConstructors _bindingsOvalueConstructors _bindingsOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
sem_Declaration_Instance :: T_Range ->
                            T_ContextItems ->
                            T_Name ->
                            T_Types ->
                            T_MaybeDeclarations ->
                            T_Declaration
sem_Declaration_Instance range_ context_ name_ types_ where_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOwarnings :: ([Warning])
              _contextOallTypeConstructors :: Names
              _contextOmiscerrors :: ([Error])
              _contextOoptions :: ([Option])
              _contextOtypeConstructors :: (M.Map Name Int)
              _contextOwarnings :: ([Warning])
              _typesOallTypeConstructors :: Names
              _typesOmiscerrors :: ([Error])
              _typesOoptions :: ([Option])
              _typesOtypeConstructors :: (M.Map Name Int)
              _typesOwarnings :: ([Warning])
              _whereOallTypeConstructors :: Names
              _whereOallValueConstructors :: Names
              _whereOclassEnvironment :: ClassEnvironment
              _whereOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _whereOkindErrors :: ([Error])
              _whereOmiscerrors :: ([Error])
              _whereOnamesInScope :: Names
              _whereOoptions :: ([Option])
              _whereOorderedTypeSynonyms :: OrderedTypeSynonyms
              _whereOtypeConstructors :: (M.Map Name Int)
              _whereOunboundNames :: Names
              _whereOvalueConstructors :: (M.Map Name TpScheme)
              _whereOwarnings :: ([Warning])
              _rangeIself :: Range
              _contextIcontextRanges :: ([Range])
              _contextIcontextVars :: ([Name])
              _contextImiscerrors :: ([Error])
              _contextIself :: ContextItems
              _contextIwarnings :: ([Warning])
              _nameIself :: Name
              _typesImiscerrors :: ([Error])
              _typesIself :: Types
              _typesItypevariables :: Names
              _typesIwarnings :: ([Warning])
              _whereIcollectInstances :: ([(Name, Instance)])
              _whereIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _whereIkindErrors :: ([Error])
              _whereImiscerrors :: ([Error])
              _whereInamesInScope :: Names
              _whereIself :: MaybeDeclarations
              _whereIunboundNames :: Names
              _whereIwarnings :: ([Warning])
              _lhsOpreviousWasAlsoFB =
                  Nothing
              __tup5 =
                  internalError "PartialSyntax.ag" "n/a" "Declaration.Instance"
              (_assumptions,_,_) =
                  __tup5
              (_,_constraints,_) =
                  __tup5
              (_,_,_unboundNames) =
                  __tup5
              _lhsOcollectInstances =
                  _whereIcollectInstances
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOunboundNames =
                  _unboundNames
              _self =
                  Declaration_Instance _rangeIself _contextIself _nameIself _typesIself _whereIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _whereIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOkindErrors =
                  _whereIkindErrors
              _lhsOmiscerrors =
                  _whereImiscerrors
              _lhsOoperatorFixities =
                  _lhsIoperatorFixities
              _lhsOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOwarnings =
                  _whereIwarnings
              _contextOallTypeConstructors =
                  _lhsIallTypeConstructors
              _contextOmiscerrors =
                  _lhsImiscerrors
              _contextOoptions =
                  _lhsIoptions
              _contextOtypeConstructors =
                  _lhsItypeConstructors
              _contextOwarnings =
                  _lhsIwarnings
              _typesOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typesOmiscerrors =
                  _contextImiscerrors
              _typesOoptions =
                  _lhsIoptions
              _typesOtypeConstructors =
                  _lhsItypeConstructors
              _typesOwarnings =
                  _contextIwarnings
              _whereOallTypeConstructors =
                  _lhsIallTypeConstructors
              _whereOallValueConstructors =
                  _lhsIallValueConstructors
              _whereOclassEnvironment =
                  _lhsIclassEnvironment
              _whereOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _whereOkindErrors =
                  _lhsIkindErrors
              _whereOmiscerrors =
                  _typesImiscerrors
              _whereOnamesInScope =
                  _lhsInamesInScope
              _whereOoptions =
                  _lhsIoptions
              _whereOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _whereOtypeConstructors =
                  _lhsItypeConstructors
              _whereOunboundNames =
                  _unboundNames
              _whereOvalueConstructors =
                  _lhsIvalueConstructors
              _whereOwarnings =
                  _typesIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _contextIcontextRanges,_contextIcontextVars,_contextImiscerrors,_contextIself,_contextIwarnings) =
                  (context_ _contextOallTypeConstructors _contextOmiscerrors _contextOoptions _contextOtypeConstructors _contextOwarnings )
              ( _nameIself) =
                  (name_ )
              ( _typesImiscerrors,_typesIself,_typesItypevariables,_typesIwarnings) =
                  (types_ _typesOallTypeConstructors _typesOmiscerrors _typesOoptions _typesOtypeConstructors _typesOwarnings )
              ( _whereIcollectInstances,_whereIcollectScopeInfos,_whereIkindErrors,_whereImiscerrors,_whereInamesInScope,_whereIself,_whereIunboundNames,_whereIwarnings) =
                  (where_ _whereOallTypeConstructors _whereOallValueConstructors _whereOclassEnvironment _whereOcollectScopeInfos _whereOkindErrors _whereOmiscerrors _whereOnamesInScope _whereOoptions _whereOorderedTypeSynonyms _whereOtypeConstructors _whereOunboundNames _whereOvalueConstructors _whereOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
sem_Declaration_Newtype :: T_Range ->
                           T_ContextItems ->
                           T_SimpleType ->
                           T_Constructor ->
                           T_Names ->
                           T_Declaration
sem_Declaration_Newtype range_ context_ simpletype_ constructor_ derivings_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _constructorOsimpletype :: SimpleType
              _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOwarnings :: ([Warning])
              _contextOallTypeConstructors :: Names
              _contextOmiscerrors :: ([Error])
              _contextOoptions :: ([Option])
              _contextOtypeConstructors :: (M.Map Name Int)
              _contextOwarnings :: ([Warning])
              _constructorOallTypeConstructors :: Names
              _constructorOallValueConstructors :: Names
              _constructorOcollectValueConstructors :: ([(Name,TpScheme)])
              _constructorOkindErrors :: ([Error])
              _constructorOmiscerrors :: ([Error])
              _constructorOnamesInScope :: Names
              _constructorOoptions :: ([Option])
              _constructorOtypeConstructors :: (M.Map Name Int)
              _constructorOvalueConstructors :: (M.Map Name TpScheme)
              _constructorOwarnings :: ([Warning])
              _rangeIself :: Range
              _contextIcontextRanges :: ([Range])
              _contextIcontextVars :: ([Name])
              _contextImiscerrors :: ([Error])
              _contextIself :: ContextItems
              _contextIwarnings :: ([Warning])
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _constructorIcollectValueConstructors :: ([(Name,TpScheme)])
              _constructorIkindErrors :: ([Error])
              _constructorImiscerrors :: ([Error])
              _constructorIparameterTypes :: Tps
              _constructorIself :: Constructor
              _constructorItypevariables :: Names
              _constructorIunboundNames :: Names
              _constructorIwarnings :: ([Warning])
              _derivingsIself :: Names
              _constructorOsimpletype =
                  _simpletypeIself
              _lhsOpreviousWasAlsoFB =
                  Nothing
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOunboundNames =
                  _constructorIunboundNames
              _self =
                  Declaration_Newtype _rangeIself _contextIself _simpletypeIself _constructorIself _derivingsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _constructorIcollectValueConstructors
              _lhsOkindErrors =
                  _constructorIkindErrors
              _lhsOmiscerrors =
                  _constructorImiscerrors
              _lhsOoperatorFixities =
                  _lhsIoperatorFixities
              _lhsOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOwarnings =
                  _constructorIwarnings
              _contextOallTypeConstructors =
                  _lhsIallTypeConstructors
              _contextOmiscerrors =
                  _lhsImiscerrors
              _contextOoptions =
                  _lhsIoptions
              _contextOtypeConstructors =
                  _lhsItypeConstructors
              _contextOwarnings =
                  _lhsIwarnings
              _constructorOallTypeConstructors =
                  _lhsIallTypeConstructors
              _constructorOallValueConstructors =
                  _lhsIallValueConstructors
              _constructorOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _constructorOkindErrors =
                  _lhsIkindErrors
              _constructorOmiscerrors =
                  _contextImiscerrors
              _constructorOnamesInScope =
                  _lhsInamesInScope
              _constructorOoptions =
                  _lhsIoptions
              _constructorOtypeConstructors =
                  _lhsItypeConstructors
              _constructorOvalueConstructors =
                  _lhsIvalueConstructors
              _constructorOwarnings =
                  _contextIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _contextIcontextRanges,_contextIcontextVars,_contextImiscerrors,_contextIself,_contextIwarnings) =
                  (context_ _contextOallTypeConstructors _contextOmiscerrors _contextOoptions _contextOtypeConstructors _contextOwarnings )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _constructorIcollectValueConstructors,_constructorIkindErrors,_constructorImiscerrors,_constructorIparameterTypes,_constructorIself,_constructorItypevariables,_constructorIunboundNames,_constructorIwarnings) =
                  (constructor_ _constructorOallTypeConstructors _constructorOallValueConstructors _constructorOcollectValueConstructors _constructorOkindErrors _constructorOmiscerrors _constructorOnamesInScope _constructorOoptions _constructorOsimpletype _constructorOtypeConstructors _constructorOvalueConstructors _constructorOwarnings )
              ( _derivingsIself) =
                  (derivings_ )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
sem_Declaration_PatternBinding :: T_Range ->
                                  T_Pattern ->
                                  T_RightHandSide ->
                                  T_Declaration
sem_Declaration_PatternBinding range_ pattern_ righthandside_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOdeclVarNames :: Names
              _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOmiscerrors :: ([Error])
              _patternOlhsPattern :: Bool
              _lhsOrestrictedNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOwarnings :: ([Warning])
              _patternOallTypeConstructors :: Names
              _patternOallValueConstructors :: Names
              _patternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternOmiscerrors :: ([Error])
              _patternOnamesInScope :: Names
              _patternOtypeConstructors :: (M.Map Name Int)
              _patternOvalueConstructors :: (M.Map Name TpScheme)
              _patternOwarnings :: ([Warning])
              _righthandsideOallTypeConstructors :: Names
              _righthandsideOallValueConstructors :: Names
              _righthandsideOclassEnvironment :: ClassEnvironment
              _righthandsideOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _righthandsideOkindErrors :: ([Error])
              _righthandsideOmiscerrors :: ([Error])
              _righthandsideOnamesInScope :: Names
              _righthandsideOoptions :: ([Option])
              _righthandsideOorderedTypeSynonyms :: OrderedTypeSynonyms
              _righthandsideOtypeConstructors :: (M.Map Name Int)
              _righthandsideOvalueConstructors :: (M.Map Name TpScheme)
              _righthandsideOwarnings :: ([Warning])
              _rangeIself :: Range
              _patternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternImiscerrors :: ([Error])
              _patternIpatVarNames :: Names
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _patternIwarnings :: ([Warning])
              _righthandsideIcollectInstances :: ([(Name, Instance)])
              _righthandsideIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _righthandsideIkindErrors :: ([Error])
              _righthandsideImiscerrors :: ([Error])
              _righthandsideIself :: RightHandSide
              _righthandsideIunboundNames :: Names
              _righthandsideIwarnings :: ([Warning])
              _lhsOdeclVarNames =
                  _patternIpatVarNames
              _lhsOpreviousWasAlsoFB =
                  Nothing
              _lhsOmiscerrors =
                  _patternDefinesNoVarsErrors ++ _righthandsideImiscerrors
              _patternDefinesNoVarsErrors =
                  if null _patternIpatVarNames
                    then [ PatternDefinesNoVars (getPatRange _patternIself) ]
                    else []
              _patternOlhsPattern =
                  simplePattern _patternIself
              _lhsOrestrictedNames =
                  if isSimplePattern _patternIself
                    then []
                    else _patternIpatVarNames
              _lhsOcollectInstances =
                  _righthandsideIcollectInstances
              _lhsOunboundNames =
                  _patternIunboundNames ++ _righthandsideIunboundNames
              _self =
                  Declaration_PatternBinding _rangeIself _patternIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _righthandsideIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOkindErrors =
                  _righthandsideIkindErrors
              _lhsOoperatorFixities =
                  _lhsIoperatorFixities
              _lhsOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOwarnings =
                  _righthandsideIwarnings
              _patternOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternOallValueConstructors =
                  _lhsIallValueConstructors
              _patternOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternOmiscerrors =
                  _lhsImiscerrors
              _patternOnamesInScope =
                  _lhsInamesInScope
              _patternOtypeConstructors =
                  _lhsItypeConstructors
              _patternOvalueConstructors =
                  _lhsIvalueConstructors
              _patternOwarnings =
                  _lhsIwarnings
              _righthandsideOallTypeConstructors =
                  _lhsIallTypeConstructors
              _righthandsideOallValueConstructors =
                  _lhsIallValueConstructors
              _righthandsideOclassEnvironment =
                  _lhsIclassEnvironment
              _righthandsideOcollectScopeInfos =
                  _patternIcollectScopeInfos
              _righthandsideOkindErrors =
                  _lhsIkindErrors
              _righthandsideOmiscerrors =
                  _patternImiscerrors
              _righthandsideOnamesInScope =
                  _lhsInamesInScope
              _righthandsideOoptions =
                  _lhsIoptions
              _righthandsideOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _righthandsideOtypeConstructors =
                  _lhsItypeConstructors
              _righthandsideOvalueConstructors =
                  _lhsIvalueConstructors
              _righthandsideOwarnings =
                  _patternIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternIcollectScopeInfos,_patternImiscerrors,_patternIpatVarNames,_patternIself,_patternIunboundNames,_patternIwarnings) =
                  (pattern_ _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings )
              ( _righthandsideIcollectInstances,_righthandsideIcollectScopeInfos,_righthandsideIkindErrors,_righthandsideImiscerrors,_righthandsideIself,_righthandsideIunboundNames,_righthandsideIwarnings) =
                  (righthandside_ _righthandsideOallTypeConstructors _righthandsideOallValueConstructors _righthandsideOclassEnvironment _righthandsideOcollectScopeInfos _righthandsideOkindErrors _righthandsideOmiscerrors _righthandsideOnamesInScope _righthandsideOoptions _righthandsideOorderedTypeSynonyms _righthandsideOtypeConstructors _righthandsideOvalueConstructors _righthandsideOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
sem_Declaration_Type :: T_Range ->
                        T_SimpleType ->
                        T_Type ->
                        T_Declaration
sem_Declaration_Type range_ simpletype_ type_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOkindErrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOmiscerrors :: ([Error])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _typeOallTypeConstructors :: Names
              _typeOmiscerrors :: ([Error])
              _typeOoptions :: ([Option])
              _typeOtypeConstructors :: (M.Map Name Int)
              _typeOwarnings :: ([Warning])
              _rangeIself :: Range
              _simpletypeIname :: Name
              _simpletypeIself :: SimpleType
              _simpletypeItypevariables :: Names
              _typeIcontextRange :: Range
              _typeImiscerrors :: ([Error])
              _typeIself :: Type
              _typeItypevariables :: Names
              _typeIwarnings :: ([Warning])
              _lhsOcollectTypeSynonyms =
                  (_simpletypeIname, _typeSynonymInfo) : _lhsIcollectTypeSynonyms
              _typeSynonymInfo =
                  (length _simpletypeItypevariables,\tps -> makeTpFromType (zip _simpletypeItypevariables tps) _typeIself)
              _lhsOkindErrors =
                  _newErrors ++ _lhsIkindErrors
              _newErrors =
                  checkType _lhsItypeConstructors (_lhsInamesInScope ++ _lhsIallValueConstructors) _typeIself
              _lhsOwarnings =
                  map (Unused TypeVariable) _unused ++ _lhsIwarnings
              _lhsOpreviousWasAlsoFB =
                  Nothing
              _lhsOmiscerrors =
                  concat [ makeDuplicated TypeVariable _doubles
                         , makeUndefined TypeVariable _undef _simpletypeItypevariables
                         , _lhsImiscerrors
                         ]
              _unused =
                  filter (`notElem` _typeItypevariables)       _simpletypeItypevariables
              _doubles =
                  filter ((>1) . length) . group . sort $      _simpletypeItypevariables
              _undef =
                  filter (`notElem` _simpletypeItypevariables) _typeItypevariables
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Declaration_Type _rangeIself _simpletypeIself _typeIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOoperatorFixities =
                  _lhsIoperatorFixities
              _lhsOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _typeOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typeOmiscerrors =
                  _lhsImiscerrors
              _typeOoptions =
                  _lhsIoptions
              _typeOtypeConstructors =
                  _lhsItypeConstructors
              _typeOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _simpletypeIname,_simpletypeIself,_simpletypeItypevariables) =
                  (simpletype_ )
              ( _typeIcontextRange,_typeImiscerrors,_typeIself,_typeItypevariables,_typeIwarnings) =
                  (type_ _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
sem_Declaration_TypeSignature :: T_Range ->
                                 T_Names ->
                                 T_Type ->
                                 T_Declaration
sem_Declaration_TypeSignature range_ names_ type_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOwarnings :: ([Warning])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declaration
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOmiscerrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _typeOallTypeConstructors :: Names
              _typeOmiscerrors :: ([Error])
              _typeOoptions :: ([Option])
              _typeOtypeConstructors :: (M.Map Name Int)
              _typeOwarnings :: ([Warning])
              _rangeIself :: Range
              _namesIself :: Names
              _typeIcontextRange :: Range
              _typeImiscerrors :: ([Error])
              _typeIself :: Type
              _typeItypevariables :: Names
              _typeIwarnings :: ([Warning])
              _lhsOtypeSignatures =
                  [ (name, _typeScheme) | name <- _namesIself ] ++ _lhsItypeSignatures
              __tup6 =
                  makeTpSchemeFromType' _typeIself
              (_typeScheme,_) =
                  __tup6
              (_,_intMap) =
                  __tup6
              _lhsOkindErrors =
                  _newErrors ++ _lhsIkindErrors
              _newErrors =
                  checkType _lhsItypeConstructors (_lhsInamesInScope ++ _lhsIallValueConstructors) _typeIself
              _lhsOpreviousWasAlsoFB =
                  Nothing
              _lhsOwarnings =
                  simplifyContext _lhsIorderedTypeSynonyms _typeIcontextRange _intMap _typeScheme ++ _typeIwarnings
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Declaration_TypeSignature _rangeIself _namesIself _typeIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOmiscerrors =
                  _typeImiscerrors
              _lhsOoperatorFixities =
                  _lhsIoperatorFixities
              _lhsOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _typeOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typeOmiscerrors =
                  _lhsImiscerrors
              _typeOoptions =
                  _lhsIoptions
              _typeOtypeConstructors =
                  _lhsItypeConstructors
              _typeOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _namesIself) =
                  (names_ )
              ( _typeIcontextRange,_typeImiscerrors,_typeIself,_typeItypevariables,_typeIwarnings) =
                  (type_ _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
-- Declarations ------------------------------------------------
-- cata
sem_Declarations :: Declarations ->
                    T_Declarations
sem_Declarations list  =
    (Prelude.foldr sem_Declarations_Cons sem_Declarations_Nil (Prelude.map sem_Declaration list) )
-- semantic domain
type T_Declarations = Names ->
                      Names ->
                      ClassEnvironment ->
                      ([(ScopeInfo, Entity)]) ->
                      ([(Name,Int)]) ->
                      ([(Name,(Int,Tps -> Tp))]) ->
                      ([(Name,TpScheme)]) ->
                      ([Error]) ->
                      ([Error]) ->
                      Names ->
                      ([(Name,(Int,Assoc))]) ->
                      ([Option]) ->
                      OrderedTypeSynonyms ->
                      (Maybe Name) ->
                      ([(Name,Name)]) ->
                      (M.Map Name Int) ->
                      ([(Name,TpScheme)]) ->
                      (M.Map Name TpScheme) ->
                      ([Warning]) ->
                      ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([(Name,Int)]),([(Name,(Int,Tps -> Tp))]),([(Name,TpScheme)]),Names,([Error]),([Error]),([(Name,(Int,Assoc))]),(Maybe Name),Names,Declarations,([(Name,Name)]),([(Name,TpScheme)]),Names,([Warning]))
sem_Declarations_Cons :: T_Declaration ->
                         T_Declarations ->
                         T_Declarations
sem_Declarations_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declarations
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOallValueConstructors :: Names
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOcollectTypeConstructors :: ([(Name,Int)])
              _hdOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _hdOcollectValueConstructors :: ([(Name,TpScheme)])
              _hdOkindErrors :: ([Error])
              _hdOmiscerrors :: ([Error])
              _hdOnamesInScope :: Names
              _hdOoperatorFixities :: ([(Name,(Int,Assoc))])
              _hdOoptions :: ([Option])
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOpreviousWasAlsoFB :: (Maybe Name)
              _hdOsuspiciousFBs :: ([(Name,Name)])
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOtypeSignatures :: ([(Name,TpScheme)])
              _hdOvalueConstructors :: (M.Map Name TpScheme)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOallValueConstructors :: Names
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlOcollectTypeConstructors :: ([(Name,Int)])
              _tlOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _tlOcollectValueConstructors :: ([(Name,TpScheme)])
              _tlOkindErrors :: ([Error])
              _tlOmiscerrors :: ([Error])
              _tlOnamesInScope :: Names
              _tlOoperatorFixities :: ([(Name,(Int,Assoc))])
              _tlOoptions :: ([Option])
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOpreviousWasAlsoFB :: (Maybe Name)
              _tlOsuspiciousFBs :: ([(Name,Name)])
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOtypeSignatures :: ([(Name,TpScheme)])
              _tlOvalueConstructors :: (M.Map Name TpScheme)
              _tlOwarnings :: ([Warning])
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdIcollectTypeConstructors :: ([(Name,Int)])
              _hdIcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _hdIcollectValueConstructors :: ([(Name,TpScheme)])
              _hdIdeclVarNames :: Names
              _hdIkindErrors :: ([Error])
              _hdImiscerrors :: ([Error])
              _hdIoperatorFixities :: ([(Name,(Int,Assoc))])
              _hdIpreviousWasAlsoFB :: (Maybe Name)
              _hdIrestrictedNames :: Names
              _hdIself :: Declaration
              _hdIsuspiciousFBs :: ([(Name,Name)])
              _hdItypeSignatures :: ([(Name,TpScheme)])
              _hdIunboundNames :: Names
              _hdIwarnings :: ([Warning])
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlIcollectTypeConstructors :: ([(Name,Int)])
              _tlIcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _tlIcollectValueConstructors :: ([(Name,TpScheme)])
              _tlIdeclVarNames :: Names
              _tlIkindErrors :: ([Error])
              _tlImiscerrors :: ([Error])
              _tlIoperatorFixities :: ([(Name,(Int,Assoc))])
              _tlIpreviousWasAlsoFB :: (Maybe Name)
              _tlIrestrictedNames :: Names
              _tlIself :: Declarations
              _tlIsuspiciousFBs :: ([(Name,Name)])
              _tlItypeSignatures :: ([(Name,TpScheme)])
              _tlIunboundNames :: Names
              _tlIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOdeclVarNames =
                  _hdIdeclVarNames ++ _tlIdeclVarNames
              _lhsOrestrictedNames =
                  _hdIrestrictedNames  ++  _tlIrestrictedNames
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _tlIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _tlIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _tlIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _tlIcollectValueConstructors
              _lhsOkindErrors =
                  _tlIkindErrors
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOoperatorFixities =
                  _tlIoperatorFixities
              _lhsOpreviousWasAlsoFB =
                  _tlIpreviousWasAlsoFB
              _lhsOsuspiciousFBs =
                  _tlIsuspiciousFBs
              _lhsOtypeSignatures =
                  _tlItypeSignatures
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOallValueConstructors =
                  _lhsIallValueConstructors
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _hdOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _hdOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _hdOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _hdOkindErrors =
                  _lhsIkindErrors
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOoperatorFixities =
                  _lhsIoperatorFixities
              _hdOoptions =
                  _lhsIoptions
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOpreviousWasAlsoFB =
                  _lhsIpreviousWasAlsoFB
              _hdOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOtypeSignatures =
                  _lhsItypeSignatures
              _hdOvalueConstructors =
                  _lhsIvalueConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOallValueConstructors =
                  _lhsIallValueConstructors
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectScopeInfos =
                  _hdIcollectScopeInfos
              _tlOcollectTypeConstructors =
                  _hdIcollectTypeConstructors
              _tlOcollectTypeSynonyms =
                  _hdIcollectTypeSynonyms
              _tlOcollectValueConstructors =
                  _hdIcollectValueConstructors
              _tlOkindErrors =
                  _hdIkindErrors
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOoperatorFixities =
                  _hdIoperatorFixities
              _tlOoptions =
                  _lhsIoptions
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOpreviousWasAlsoFB =
                  _hdIpreviousWasAlsoFB
              _tlOsuspiciousFBs =
                  _hdIsuspiciousFBs
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOtypeSignatures =
                  _hdItypeSignatures
              _tlOvalueConstructors =
                  _lhsIvalueConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIcollectInstances,_hdIcollectScopeInfos,_hdIcollectTypeConstructors,_hdIcollectTypeSynonyms,_hdIcollectValueConstructors,_hdIdeclVarNames,_hdIkindErrors,_hdImiscerrors,_hdIoperatorFixities,_hdIpreviousWasAlsoFB,_hdIrestrictedNames,_hdIself,_hdIsuspiciousFBs,_hdItypeSignatures,_hdIunboundNames,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOcollectTypeConstructors _hdOcollectTypeSynonyms _hdOcollectValueConstructors _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoperatorFixities _hdOoptions _hdOorderedTypeSynonyms _hdOpreviousWasAlsoFB _hdOsuspiciousFBs _hdOtypeConstructors _hdOtypeSignatures _hdOvalueConstructors _hdOwarnings )
              ( _tlIcollectInstances,_tlIcollectScopeInfos,_tlIcollectTypeConstructors,_tlIcollectTypeSynonyms,_tlIcollectValueConstructors,_tlIdeclVarNames,_tlIkindErrors,_tlImiscerrors,_tlIoperatorFixities,_tlIpreviousWasAlsoFB,_tlIrestrictedNames,_tlIself,_tlIsuspiciousFBs,_tlItypeSignatures,_tlIunboundNames,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOcollectTypeConstructors _tlOcollectTypeSynonyms _tlOcollectValueConstructors _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoperatorFixities _tlOoptions _tlOorderedTypeSynonyms _tlOpreviousWasAlsoFB _tlOsuspiciousFBs _tlOtypeConstructors _tlOtypeSignatures _tlOvalueConstructors _tlOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
sem_Declarations_Nil :: T_Declarations
sem_Declarations_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIcollectTypeConstructors
       _lhsIcollectTypeSynonyms
       _lhsIcollectValueConstructors
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoperatorFixities
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsIpreviousWasAlsoFB
       _lhsIsuspiciousFBs
       _lhsItypeConstructors
       _lhsItypeSignatures
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOdeclVarNames :: Names
              _lhsOrestrictedNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Declarations
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectTypeConstructors :: ([(Name,Int)])
              _lhsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _lhsOcollectValueConstructors :: ([(Name,TpScheme)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _lhsOpreviousWasAlsoFB :: (Maybe Name)
              _lhsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOwarnings :: ([Warning])
              _lhsOcollectInstances =
                  []
              _lhsOdeclVarNames =
                  []
              _lhsOrestrictedNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOcollectTypeConstructors =
                  _lhsIcollectTypeConstructors
              _lhsOcollectTypeSynonyms =
                  _lhsIcollectTypeSynonyms
              _lhsOcollectValueConstructors =
                  _lhsIcollectValueConstructors
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOoperatorFixities =
                  _lhsIoperatorFixities
              _lhsOpreviousWasAlsoFB =
                  _lhsIpreviousWasAlsoFB
              _lhsOsuspiciousFBs =
                  _lhsIsuspiciousFBs
              _lhsOtypeSignatures =
                  _lhsItypeSignatures
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOcollectTypeConstructors,_lhsOcollectTypeSynonyms,_lhsOcollectValueConstructors,_lhsOdeclVarNames,_lhsOkindErrors,_lhsOmiscerrors,_lhsOoperatorFixities,_lhsOpreviousWasAlsoFB,_lhsOrestrictedNames,_lhsOself,_lhsOsuspiciousFBs,_lhsOtypeSignatures,_lhsOunboundNames,_lhsOwarnings)))
-- Export ------------------------------------------------------
-- cata
sem_Export :: Export ->
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
type T_Export = Names ->
                Names ->
                Names ->
                Names ->
                ( ([Error]),Export)
sem_Export_Module :: T_Range ->
                     T_Name ->
                     T_Export
sem_Export_Module range_ name_  =
    (\ _lhsIconsInScope
       _lhsImodulesInScope
       _lhsInamesInScop
       _lhsItyconsInScope ->
         (let _lhsOexportErrors :: ([Error])
              _lhsOself :: Export
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOexportErrors =
                  checkExport ExportModule _nameIself
                     _lhsImodulesInScope
              _self =
                  Export_Module _rangeIself _nameIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOexportErrors,_lhsOself)))
sem_Export_TypeOrClass :: T_Range ->
                          T_Name ->
                          T_MaybeNames ->
                          T_Export
sem_Export_TypeOrClass range_ name_ names_  =
    (\ _lhsIconsInScope
       _lhsImodulesInScope
       _lhsInamesInScop
       _lhsItyconsInScope ->
         (let _lhsOexportErrors :: ([Error])
              _lhsOself :: Export
              _rangeIself :: Range
              _nameIself :: Name
              _namesIself :: MaybeNames
              _lhsOexportErrors =
                  []
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
          in  ( _lhsOexportErrors,_lhsOself)))
sem_Export_TypeOrClassComplete :: T_Range ->
                                  T_Name ->
                                  T_Export
sem_Export_TypeOrClassComplete range_ name_  =
    (\ _lhsIconsInScope
       _lhsImodulesInScope
       _lhsInamesInScop
       _lhsItyconsInScope ->
         (let _lhsOexportErrors :: ([Error])
              _lhsOself :: Export
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOexportErrors =
                  []
              _self =
                  Export_TypeOrClassComplete _rangeIself _nameIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOexportErrors,_lhsOself)))
sem_Export_Variable :: T_Range ->
                       T_Name ->
                       T_Export
sem_Export_Variable range_ name_  =
    (\ _lhsIconsInScope
       _lhsImodulesInScope
       _lhsInamesInScop
       _lhsItyconsInScope ->
         (let _lhsOexportErrors :: ([Error])
              _lhsOself :: Export
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOexportErrors =
                  checkExport ExportVariable _nameIself
                     _lhsInamesInScop
              _self =
                  Export_Variable _rangeIself _nameIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOexportErrors,_lhsOself)))
-- Exports -----------------------------------------------------
-- cata
sem_Exports :: Exports ->
               T_Exports
sem_Exports list  =
    (Prelude.foldr sem_Exports_Cons sem_Exports_Nil (Prelude.map sem_Export list) )
-- semantic domain
type T_Exports = Names ->
                 Names ->
                 Names ->
                 Names ->
                 ( ([Error]),Exports)
sem_Exports_Cons :: T_Export ->
                    T_Exports ->
                    T_Exports
sem_Exports_Cons hd_ tl_  =
    (\ _lhsIconsInScope
       _lhsImodulesInScope
       _lhsInamesInScop
       _lhsItyconsInScope ->
         (let _lhsOexportErrors :: ([Error])
              _lhsOself :: Exports
              _hdOconsInScope :: Names
              _hdOmodulesInScope :: Names
              _hdOnamesInScop :: Names
              _hdOtyconsInScope :: Names
              _tlOconsInScope :: Names
              _tlOmodulesInScope :: Names
              _tlOnamesInScop :: Names
              _tlOtyconsInScope :: Names
              _hdIexportErrors :: ([Error])
              _hdIself :: Export
              _tlIexportErrors :: ([Error])
              _tlIself :: Exports
              _lhsOexportErrors =
                  _hdIexportErrors  ++  _tlIexportErrors
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _hdOconsInScope =
                  _lhsIconsInScope
              _hdOmodulesInScope =
                  _lhsImodulesInScope
              _hdOnamesInScop =
                  _lhsInamesInScop
              _hdOtyconsInScope =
                  _lhsItyconsInScope
              _tlOconsInScope =
                  _lhsIconsInScope
              _tlOmodulesInScope =
                  _lhsImodulesInScope
              _tlOnamesInScop =
                  _lhsInamesInScop
              _tlOtyconsInScope =
                  _lhsItyconsInScope
              ( _hdIexportErrors,_hdIself) =
                  (hd_ _hdOconsInScope _hdOmodulesInScope _hdOnamesInScop _hdOtyconsInScope )
              ( _tlIexportErrors,_tlIself) =
                  (tl_ _tlOconsInScope _tlOmodulesInScope _tlOnamesInScop _tlOtyconsInScope )
          in  ( _lhsOexportErrors,_lhsOself)))
sem_Exports_Nil :: T_Exports
sem_Exports_Nil  =
    (\ _lhsIconsInScope
       _lhsImodulesInScope
       _lhsInamesInScop
       _lhsItyconsInScope ->
         (let _lhsOexportErrors :: ([Error])
              _lhsOself :: Exports
              _lhsOexportErrors =
                  []
              _self =
                  []
              _lhsOself =
                  _self
          in  ( _lhsOexportErrors,_lhsOself)))
-- Expression --------------------------------------------------
-- cata
sem_Expression :: Expression ->
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
type T_Expression = Names ->
                    Names ->
                    ClassEnvironment ->
                    ([(ScopeInfo, Entity)]) ->
                    ([Error]) ->
                    ([Error]) ->
                    Names ->
                    ([Option]) ->
                    OrderedTypeSynonyms ->
                    (M.Map Name Int) ->
                    (M.Map Name TpScheme) ->
                    ([Warning]) ->
                    ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),Expression,Names,([Warning]))
sem_Expression_Case :: T_Range ->
                       T_Expression ->
                       T_Alternatives ->
                       T_Expression
sem_Expression_Case range_ expression_ alternatives_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _alternativesOallTypeConstructors :: Names
              _alternativesOallValueConstructors :: Names
              _alternativesOclassEnvironment :: ClassEnvironment
              _alternativesOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _alternativesOkindErrors :: ([Error])
              _alternativesOmiscerrors :: ([Error])
              _alternativesOnamesInScope :: Names
              _alternativesOoptions :: ([Option])
              _alternativesOorderedTypeSynonyms :: OrderedTypeSynonyms
              _alternativesOtypeConstructors :: (M.Map Name Int)
              _alternativesOvalueConstructors :: (M.Map Name TpScheme)
              _alternativesOwarnings :: ([Warning])
              _rangeIself :: Range
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _alternativesIcollectInstances :: ([(Name, Instance)])
              _alternativesIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _alternativesIkindErrors :: ([Error])
              _alternativesImiscerrors :: ([Error])
              _alternativesIself :: Alternatives
              _alternativesIunboundNames :: Names
              _alternativesIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _expressionIcollectInstances  ++  _alternativesIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames ++ _alternativesIunboundNames
              _self =
                  Expression_Case _rangeIself _expressionIself _alternativesIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _alternativesIcollectScopeInfos
              _lhsOkindErrors =
                  _alternativesIkindErrors
              _lhsOmiscerrors =
                  _alternativesImiscerrors
              _lhsOwarnings =
                  _alternativesIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _lhsImiscerrors
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _lhsIwarnings
              _alternativesOallTypeConstructors =
                  _lhsIallTypeConstructors
              _alternativesOallValueConstructors =
                  _lhsIallValueConstructors
              _alternativesOclassEnvironment =
                  _lhsIclassEnvironment
              _alternativesOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _alternativesOkindErrors =
                  _expressionIkindErrors
              _alternativesOmiscerrors =
                  _expressionImiscerrors
              _alternativesOnamesInScope =
                  _lhsInamesInScope
              _alternativesOoptions =
                  _lhsIoptions
              _alternativesOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _alternativesOtypeConstructors =
                  _lhsItypeConstructors
              _alternativesOvalueConstructors =
                  _lhsIvalueConstructors
              _alternativesOwarnings =
                  _expressionIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
              ( _alternativesIcollectInstances,_alternativesIcollectScopeInfos,_alternativesIkindErrors,_alternativesImiscerrors,_alternativesIself,_alternativesIunboundNames,_alternativesIwarnings) =
                  (alternatives_ _alternativesOallTypeConstructors _alternativesOallValueConstructors _alternativesOclassEnvironment _alternativesOcollectScopeInfos _alternativesOkindErrors _alternativesOmiscerrors _alternativesOnamesInScope _alternativesOoptions _alternativesOorderedTypeSynonyms _alternativesOtypeConstructors _alternativesOvalueConstructors _alternativesOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Comprehension :: T_Range ->
                                T_Expression ->
                                T_Qualifiers ->
                                T_Expression
sem_Expression_Comprehension range_ expression_ qualifiers_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _expressionOnamesInScope :: Names
              _qualifiersOnamesInScope :: Names
              _qualifiersOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _qualifiersOallTypeConstructors :: Names
              _qualifiersOallValueConstructors :: Names
              _qualifiersOclassEnvironment :: ClassEnvironment
              _qualifiersOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _qualifiersOkindErrors :: ([Error])
              _qualifiersOmiscerrors :: ([Error])
              _qualifiersOoptions :: ([Option])
              _qualifiersOorderedTypeSynonyms :: OrderedTypeSynonyms
              _qualifiersOtypeConstructors :: (M.Map Name Int)
              _qualifiersOvalueConstructors :: (M.Map Name TpScheme)
              _qualifiersOwarnings :: ([Warning])
              _rangeIself :: Range
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _qualifiersIcollectInstances :: ([(Name, Instance)])
              _qualifiersIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _qualifiersIkindErrors :: ([Error])
              _qualifiersImiscerrors :: ([Error])
              _qualifiersInamesInScope :: Names
              _qualifiersIself :: Qualifiers
              _qualifiersIunboundNames :: Names
              _qualifiersIwarnings :: ([Warning])
              _lhsOunboundNames =
                  _qualifiersIunboundNames
              _expressionOnamesInScope =
                  _qualifiersInamesInScope
              _qualifiersOnamesInScope =
                  _lhsInamesInScope
              _qualifiersOunboundNames =
                  _expressionIunboundNames
              _lhsOcollectInstances =
                  _expressionIcollectInstances  ++  _qualifiersIcollectInstances
              _self =
                  Expression_Comprehension _rangeIself _expressionIself _qualifiersIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _qualifiersIcollectScopeInfos
              _lhsOkindErrors =
                  _qualifiersIkindErrors
              _lhsOmiscerrors =
                  _qualifiersImiscerrors
              _lhsOwarnings =
                  _qualifiersIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _lhsImiscerrors
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _lhsIwarnings
              _qualifiersOallTypeConstructors =
                  _lhsIallTypeConstructors
              _qualifiersOallValueConstructors =
                  _lhsIallValueConstructors
              _qualifiersOclassEnvironment =
                  _lhsIclassEnvironment
              _qualifiersOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _qualifiersOkindErrors =
                  _expressionIkindErrors
              _qualifiersOmiscerrors =
                  _expressionImiscerrors
              _qualifiersOoptions =
                  _lhsIoptions
              _qualifiersOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _qualifiersOtypeConstructors =
                  _lhsItypeConstructors
              _qualifiersOvalueConstructors =
                  _lhsIvalueConstructors
              _qualifiersOwarnings =
                  _expressionIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
              ( _qualifiersIcollectInstances,_qualifiersIcollectScopeInfos,_qualifiersIkindErrors,_qualifiersImiscerrors,_qualifiersInamesInScope,_qualifiersIself,_qualifiersIunboundNames,_qualifiersIwarnings) =
                  (qualifiers_ _qualifiersOallTypeConstructors _qualifiersOallValueConstructors _qualifiersOclassEnvironment _qualifiersOcollectScopeInfos _qualifiersOkindErrors _qualifiersOmiscerrors _qualifiersOnamesInScope _qualifiersOoptions _qualifiersOorderedTypeSynonyms _qualifiersOtypeConstructors _qualifiersOunboundNames _qualifiersOvalueConstructors _qualifiersOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Constructor :: T_Range ->
                              T_Name ->
                              T_Expression
sem_Expression_Constructor range_ name_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOmiscerrors :: ([Error])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOmiscerrors =
                  _undefinedConstructorErrors ++ _lhsImiscerrors
              _undefinedConstructorErrors =
                  case M.lookup _nameIself _lhsIvalueConstructors of
                     Nothing -> [ undefinedConstructorInExpr _nameIself (_lhsInamesInScope ++ _lhsIallValueConstructors) _lhsIallTypeConstructors ]
                     Just _  -> []
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Expression_Constructor _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Do :: T_Range ->
                     T_Statements ->
                     T_Expression
sem_Expression_Do range_ statements_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _statementsOunboundNames :: Names
              _statementsOlastStatementIsExpr :: Bool
              _lhsOmiscerrors :: ([Error])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _statementsOallTypeConstructors :: Names
              _statementsOallValueConstructors :: Names
              _statementsOclassEnvironment :: ClassEnvironment
              _statementsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _statementsOkindErrors :: ([Error])
              _statementsOmiscerrors :: ([Error])
              _statementsOnamesInScope :: Names
              _statementsOoptions :: ([Option])
              _statementsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _statementsOtypeConstructors :: (M.Map Name Int)
              _statementsOvalueConstructors :: (M.Map Name TpScheme)
              _statementsOwarnings :: ([Warning])
              _rangeIself :: Range
              _statementsIcollectInstances :: ([(Name, Instance)])
              _statementsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _statementsIkindErrors :: ([Error])
              _statementsIlastStatementIsExpr :: Bool
              _statementsImiscerrors :: ([Error])
              _statementsInamesInScope :: Names
              _statementsIself :: Statements
              _statementsIunboundNames :: Names
              _statementsIwarnings :: ([Warning])
              _statementsOunboundNames =
                  []
              _statementsOlastStatementIsExpr =
                  False
              _lhsOmiscerrors =
                  _lastStatementErrors ++ _statementsImiscerrors
              _lastStatementErrors =
                  if _statementsIlastStatementIsExpr
                    then []
                    else let range = getStatementRange (last _statementsIself)
                         in [ LastStatementNotExpr range ]
              _lhsOcollectInstances =
                  _statementsIcollectInstances
              _lhsOunboundNames =
                  _statementsIunboundNames
              _self =
                  Expression_Do _rangeIself _statementsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _statementsIcollectScopeInfos
              _lhsOkindErrors =
                  _statementsIkindErrors
              _lhsOwarnings =
                  _statementsIwarnings
              _statementsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _statementsOallValueConstructors =
                  _lhsIallValueConstructors
              _statementsOclassEnvironment =
                  _lhsIclassEnvironment
              _statementsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _statementsOkindErrors =
                  _lhsIkindErrors
              _statementsOmiscerrors =
                  _lhsImiscerrors
              _statementsOnamesInScope =
                  _lhsInamesInScope
              _statementsOoptions =
                  _lhsIoptions
              _statementsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _statementsOtypeConstructors =
                  _lhsItypeConstructors
              _statementsOvalueConstructors =
                  _lhsIvalueConstructors
              _statementsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _statementsIcollectInstances,_statementsIcollectScopeInfos,_statementsIkindErrors,_statementsIlastStatementIsExpr,_statementsImiscerrors,_statementsInamesInScope,_statementsIself,_statementsIunboundNames,_statementsIwarnings) =
                  (statements_ _statementsOallTypeConstructors _statementsOallValueConstructors _statementsOclassEnvironment _statementsOcollectScopeInfos _statementsOkindErrors _statementsOlastStatementIsExpr _statementsOmiscerrors _statementsOnamesInScope _statementsOoptions _statementsOorderedTypeSynonyms _statementsOtypeConstructors _statementsOunboundNames _statementsOvalueConstructors _statementsOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Enum :: T_Range ->
                       T_Expression ->
                       T_MaybeExpression ->
                       T_MaybeExpression ->
                       T_Expression
sem_Expression_Enum range_ from_ then_ to_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _fromOallTypeConstructors :: Names
              _fromOallValueConstructors :: Names
              _fromOclassEnvironment :: ClassEnvironment
              _fromOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _fromOkindErrors :: ([Error])
              _fromOmiscerrors :: ([Error])
              _fromOnamesInScope :: Names
              _fromOoptions :: ([Option])
              _fromOorderedTypeSynonyms :: OrderedTypeSynonyms
              _fromOtypeConstructors :: (M.Map Name Int)
              _fromOvalueConstructors :: (M.Map Name TpScheme)
              _fromOwarnings :: ([Warning])
              _thenOallTypeConstructors :: Names
              _thenOallValueConstructors :: Names
              _thenOclassEnvironment :: ClassEnvironment
              _thenOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _thenOkindErrors :: ([Error])
              _thenOmiscerrors :: ([Error])
              _thenOnamesInScope :: Names
              _thenOoptions :: ([Option])
              _thenOorderedTypeSynonyms :: OrderedTypeSynonyms
              _thenOtypeConstructors :: (M.Map Name Int)
              _thenOvalueConstructors :: (M.Map Name TpScheme)
              _thenOwarnings :: ([Warning])
              _toOallTypeConstructors :: Names
              _toOallValueConstructors :: Names
              _toOclassEnvironment :: ClassEnvironment
              _toOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _toOkindErrors :: ([Error])
              _toOmiscerrors :: ([Error])
              _toOnamesInScope :: Names
              _toOoptions :: ([Option])
              _toOorderedTypeSynonyms :: OrderedTypeSynonyms
              _toOtypeConstructors :: (M.Map Name Int)
              _toOvalueConstructors :: (M.Map Name TpScheme)
              _toOwarnings :: ([Warning])
              _rangeIself :: Range
              _fromIcollectInstances :: ([(Name, Instance)])
              _fromIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _fromIkindErrors :: ([Error])
              _fromImiscerrors :: ([Error])
              _fromIself :: Expression
              _fromIunboundNames :: Names
              _fromIwarnings :: ([Warning])
              _thenIcollectInstances :: ([(Name, Instance)])
              _thenIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _thenIkindErrors :: ([Error])
              _thenImiscerrors :: ([Error])
              _thenIself :: MaybeExpression
              _thenIunboundNames :: Names
              _thenIwarnings :: ([Warning])
              _toIcollectInstances :: ([(Name, Instance)])
              _toIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _toIkindErrors :: ([Error])
              _toImiscerrors :: ([Error])
              _toIself :: MaybeExpression
              _toIunboundNames :: Names
              _toIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _fromIcollectInstances  ++  _thenIcollectInstances  ++  _toIcollectInstances
              _lhsOunboundNames =
                  _fromIunboundNames ++ _thenIunboundNames ++ _toIunboundNames
              _self =
                  Expression_Enum _rangeIself _fromIself _thenIself _toIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _toIcollectScopeInfos
              _lhsOkindErrors =
                  _toIkindErrors
              _lhsOmiscerrors =
                  _toImiscerrors
              _lhsOwarnings =
                  _toIwarnings
              _fromOallTypeConstructors =
                  _lhsIallTypeConstructors
              _fromOallValueConstructors =
                  _lhsIallValueConstructors
              _fromOclassEnvironment =
                  _lhsIclassEnvironment
              _fromOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _fromOkindErrors =
                  _lhsIkindErrors
              _fromOmiscerrors =
                  _lhsImiscerrors
              _fromOnamesInScope =
                  _lhsInamesInScope
              _fromOoptions =
                  _lhsIoptions
              _fromOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _fromOtypeConstructors =
                  _lhsItypeConstructors
              _fromOvalueConstructors =
                  _lhsIvalueConstructors
              _fromOwarnings =
                  _lhsIwarnings
              _thenOallTypeConstructors =
                  _lhsIallTypeConstructors
              _thenOallValueConstructors =
                  _lhsIallValueConstructors
              _thenOclassEnvironment =
                  _lhsIclassEnvironment
              _thenOcollectScopeInfos =
                  _fromIcollectScopeInfos
              _thenOkindErrors =
                  _fromIkindErrors
              _thenOmiscerrors =
                  _fromImiscerrors
              _thenOnamesInScope =
                  _lhsInamesInScope
              _thenOoptions =
                  _lhsIoptions
              _thenOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _thenOtypeConstructors =
                  _lhsItypeConstructors
              _thenOvalueConstructors =
                  _lhsIvalueConstructors
              _thenOwarnings =
                  _fromIwarnings
              _toOallTypeConstructors =
                  _lhsIallTypeConstructors
              _toOallValueConstructors =
                  _lhsIallValueConstructors
              _toOclassEnvironment =
                  _lhsIclassEnvironment
              _toOcollectScopeInfos =
                  _thenIcollectScopeInfos
              _toOkindErrors =
                  _thenIkindErrors
              _toOmiscerrors =
                  _thenImiscerrors
              _toOnamesInScope =
                  _lhsInamesInScope
              _toOoptions =
                  _lhsIoptions
              _toOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _toOtypeConstructors =
                  _lhsItypeConstructors
              _toOvalueConstructors =
                  _lhsIvalueConstructors
              _toOwarnings =
                  _thenIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _fromIcollectInstances,_fromIcollectScopeInfos,_fromIkindErrors,_fromImiscerrors,_fromIself,_fromIunboundNames,_fromIwarnings) =
                  (from_ _fromOallTypeConstructors _fromOallValueConstructors _fromOclassEnvironment _fromOcollectScopeInfos _fromOkindErrors _fromOmiscerrors _fromOnamesInScope _fromOoptions _fromOorderedTypeSynonyms _fromOtypeConstructors _fromOvalueConstructors _fromOwarnings )
              ( _thenIcollectInstances,_thenIcollectScopeInfos,_thenIkindErrors,_thenImiscerrors,_thenIself,_thenIunboundNames,_thenIwarnings) =
                  (then_ _thenOallTypeConstructors _thenOallValueConstructors _thenOclassEnvironment _thenOcollectScopeInfos _thenOkindErrors _thenOmiscerrors _thenOnamesInScope _thenOoptions _thenOorderedTypeSynonyms _thenOtypeConstructors _thenOvalueConstructors _thenOwarnings )
              ( _toIcollectInstances,_toIcollectScopeInfos,_toIkindErrors,_toImiscerrors,_toIself,_toIunboundNames,_toIwarnings) =
                  (to_ _toOallTypeConstructors _toOallValueConstructors _toOclassEnvironment _toOcollectScopeInfos _toOkindErrors _toOmiscerrors _toOnamesInScope _toOoptions _toOorderedTypeSynonyms _toOtypeConstructors _toOvalueConstructors _toOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_If :: T_Range ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression
sem_Expression_If range_ guardExpression_ thenExpression_ elseExpression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _guardExpressionOallTypeConstructors :: Names
              _guardExpressionOallValueConstructors :: Names
              _guardExpressionOclassEnvironment :: ClassEnvironment
              _guardExpressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _guardExpressionOkindErrors :: ([Error])
              _guardExpressionOmiscerrors :: ([Error])
              _guardExpressionOnamesInScope :: Names
              _guardExpressionOoptions :: ([Option])
              _guardExpressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _guardExpressionOtypeConstructors :: (M.Map Name Int)
              _guardExpressionOvalueConstructors :: (M.Map Name TpScheme)
              _guardExpressionOwarnings :: ([Warning])
              _thenExpressionOallTypeConstructors :: Names
              _thenExpressionOallValueConstructors :: Names
              _thenExpressionOclassEnvironment :: ClassEnvironment
              _thenExpressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _thenExpressionOkindErrors :: ([Error])
              _thenExpressionOmiscerrors :: ([Error])
              _thenExpressionOnamesInScope :: Names
              _thenExpressionOoptions :: ([Option])
              _thenExpressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _thenExpressionOtypeConstructors :: (M.Map Name Int)
              _thenExpressionOvalueConstructors :: (M.Map Name TpScheme)
              _thenExpressionOwarnings :: ([Warning])
              _elseExpressionOallTypeConstructors :: Names
              _elseExpressionOallValueConstructors :: Names
              _elseExpressionOclassEnvironment :: ClassEnvironment
              _elseExpressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _elseExpressionOkindErrors :: ([Error])
              _elseExpressionOmiscerrors :: ([Error])
              _elseExpressionOnamesInScope :: Names
              _elseExpressionOoptions :: ([Option])
              _elseExpressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _elseExpressionOtypeConstructors :: (M.Map Name Int)
              _elseExpressionOvalueConstructors :: (M.Map Name TpScheme)
              _elseExpressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _guardExpressionIcollectInstances :: ([(Name, Instance)])
              _guardExpressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _guardExpressionIkindErrors :: ([Error])
              _guardExpressionImiscerrors :: ([Error])
              _guardExpressionIself :: Expression
              _guardExpressionIunboundNames :: Names
              _guardExpressionIwarnings :: ([Warning])
              _thenExpressionIcollectInstances :: ([(Name, Instance)])
              _thenExpressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _thenExpressionIkindErrors :: ([Error])
              _thenExpressionImiscerrors :: ([Error])
              _thenExpressionIself :: Expression
              _thenExpressionIunboundNames :: Names
              _thenExpressionIwarnings :: ([Warning])
              _elseExpressionIcollectInstances :: ([(Name, Instance)])
              _elseExpressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _elseExpressionIkindErrors :: ([Error])
              _elseExpressionImiscerrors :: ([Error])
              _elseExpressionIself :: Expression
              _elseExpressionIunboundNames :: Names
              _elseExpressionIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _guardExpressionIcollectInstances  ++  _thenExpressionIcollectInstances  ++  _elseExpressionIcollectInstances
              _lhsOunboundNames =
                  _guardExpressionIunboundNames ++ _thenExpressionIunboundNames ++ _elseExpressionIunboundNames
              _self =
                  Expression_If _rangeIself _guardExpressionIself _thenExpressionIself _elseExpressionIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _elseExpressionIcollectScopeInfos
              _lhsOkindErrors =
                  _elseExpressionIkindErrors
              _lhsOmiscerrors =
                  _elseExpressionImiscerrors
              _lhsOwarnings =
                  _elseExpressionIwarnings
              _guardExpressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _guardExpressionOallValueConstructors =
                  _lhsIallValueConstructors
              _guardExpressionOclassEnvironment =
                  _lhsIclassEnvironment
              _guardExpressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _guardExpressionOkindErrors =
                  _lhsIkindErrors
              _guardExpressionOmiscerrors =
                  _lhsImiscerrors
              _guardExpressionOnamesInScope =
                  _lhsInamesInScope
              _guardExpressionOoptions =
                  _lhsIoptions
              _guardExpressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _guardExpressionOtypeConstructors =
                  _lhsItypeConstructors
              _guardExpressionOvalueConstructors =
                  _lhsIvalueConstructors
              _guardExpressionOwarnings =
                  _lhsIwarnings
              _thenExpressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _thenExpressionOallValueConstructors =
                  _lhsIallValueConstructors
              _thenExpressionOclassEnvironment =
                  _lhsIclassEnvironment
              _thenExpressionOcollectScopeInfos =
                  _guardExpressionIcollectScopeInfos
              _thenExpressionOkindErrors =
                  _guardExpressionIkindErrors
              _thenExpressionOmiscerrors =
                  _guardExpressionImiscerrors
              _thenExpressionOnamesInScope =
                  _lhsInamesInScope
              _thenExpressionOoptions =
                  _lhsIoptions
              _thenExpressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _thenExpressionOtypeConstructors =
                  _lhsItypeConstructors
              _thenExpressionOvalueConstructors =
                  _lhsIvalueConstructors
              _thenExpressionOwarnings =
                  _guardExpressionIwarnings
              _elseExpressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _elseExpressionOallValueConstructors =
                  _lhsIallValueConstructors
              _elseExpressionOclassEnvironment =
                  _lhsIclassEnvironment
              _elseExpressionOcollectScopeInfos =
                  _thenExpressionIcollectScopeInfos
              _elseExpressionOkindErrors =
                  _thenExpressionIkindErrors
              _elseExpressionOmiscerrors =
                  _thenExpressionImiscerrors
              _elseExpressionOnamesInScope =
                  _lhsInamesInScope
              _elseExpressionOoptions =
                  _lhsIoptions
              _elseExpressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _elseExpressionOtypeConstructors =
                  _lhsItypeConstructors
              _elseExpressionOvalueConstructors =
                  _lhsIvalueConstructors
              _elseExpressionOwarnings =
                  _thenExpressionIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _guardExpressionIcollectInstances,_guardExpressionIcollectScopeInfos,_guardExpressionIkindErrors,_guardExpressionImiscerrors,_guardExpressionIself,_guardExpressionIunboundNames,_guardExpressionIwarnings) =
                  (guardExpression_ _guardExpressionOallTypeConstructors _guardExpressionOallValueConstructors _guardExpressionOclassEnvironment _guardExpressionOcollectScopeInfos _guardExpressionOkindErrors _guardExpressionOmiscerrors _guardExpressionOnamesInScope _guardExpressionOoptions _guardExpressionOorderedTypeSynonyms _guardExpressionOtypeConstructors _guardExpressionOvalueConstructors _guardExpressionOwarnings )
              ( _thenExpressionIcollectInstances,_thenExpressionIcollectScopeInfos,_thenExpressionIkindErrors,_thenExpressionImiscerrors,_thenExpressionIself,_thenExpressionIunboundNames,_thenExpressionIwarnings) =
                  (thenExpression_ _thenExpressionOallTypeConstructors _thenExpressionOallValueConstructors _thenExpressionOclassEnvironment _thenExpressionOcollectScopeInfos _thenExpressionOkindErrors _thenExpressionOmiscerrors _thenExpressionOnamesInScope _thenExpressionOoptions _thenExpressionOorderedTypeSynonyms _thenExpressionOtypeConstructors _thenExpressionOvalueConstructors _thenExpressionOwarnings )
              ( _elseExpressionIcollectInstances,_elseExpressionIcollectScopeInfos,_elseExpressionIkindErrors,_elseExpressionImiscerrors,_elseExpressionIself,_elseExpressionIunboundNames,_elseExpressionIwarnings) =
                  (elseExpression_ _elseExpressionOallTypeConstructors _elseExpressionOallValueConstructors _elseExpressionOclassEnvironment _elseExpressionOcollectScopeInfos _elseExpressionOkindErrors _elseExpressionOmiscerrors _elseExpressionOnamesInScope _elseExpressionOoptions _elseExpressionOorderedTypeSynonyms _elseExpressionOtypeConstructors _elseExpressionOvalueConstructors _elseExpressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_InfixApplication :: T_Range ->
                                   T_MaybeExpression ->
                                   T_Expression ->
                                   T_MaybeExpression ->
                                   T_Expression
sem_Expression_InfixApplication range_ leftExpression_ operator_ rightExpression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _leftExpressionOallTypeConstructors :: Names
              _leftExpressionOallValueConstructors :: Names
              _leftExpressionOclassEnvironment :: ClassEnvironment
              _leftExpressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _leftExpressionOkindErrors :: ([Error])
              _leftExpressionOmiscerrors :: ([Error])
              _leftExpressionOnamesInScope :: Names
              _leftExpressionOoptions :: ([Option])
              _leftExpressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _leftExpressionOtypeConstructors :: (M.Map Name Int)
              _leftExpressionOvalueConstructors :: (M.Map Name TpScheme)
              _leftExpressionOwarnings :: ([Warning])
              _operatorOallTypeConstructors :: Names
              _operatorOallValueConstructors :: Names
              _operatorOclassEnvironment :: ClassEnvironment
              _operatorOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _operatorOkindErrors :: ([Error])
              _operatorOmiscerrors :: ([Error])
              _operatorOnamesInScope :: Names
              _operatorOoptions :: ([Option])
              _operatorOorderedTypeSynonyms :: OrderedTypeSynonyms
              _operatorOtypeConstructors :: (M.Map Name Int)
              _operatorOvalueConstructors :: (M.Map Name TpScheme)
              _operatorOwarnings :: ([Warning])
              _rightExpressionOallTypeConstructors :: Names
              _rightExpressionOallValueConstructors :: Names
              _rightExpressionOclassEnvironment :: ClassEnvironment
              _rightExpressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _rightExpressionOkindErrors :: ([Error])
              _rightExpressionOmiscerrors :: ([Error])
              _rightExpressionOnamesInScope :: Names
              _rightExpressionOoptions :: ([Option])
              _rightExpressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _rightExpressionOtypeConstructors :: (M.Map Name Int)
              _rightExpressionOvalueConstructors :: (M.Map Name TpScheme)
              _rightExpressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _leftExpressionIcollectInstances :: ([(Name, Instance)])
              _leftExpressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _leftExpressionIkindErrors :: ([Error])
              _leftExpressionImiscerrors :: ([Error])
              _leftExpressionIself :: MaybeExpression
              _leftExpressionIunboundNames :: Names
              _leftExpressionIwarnings :: ([Warning])
              _operatorIcollectInstances :: ([(Name, Instance)])
              _operatorIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _operatorIkindErrors :: ([Error])
              _operatorImiscerrors :: ([Error])
              _operatorIself :: Expression
              _operatorIunboundNames :: Names
              _operatorIwarnings :: ([Warning])
              _rightExpressionIcollectInstances :: ([(Name, Instance)])
              _rightExpressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _rightExpressionIkindErrors :: ([Error])
              _rightExpressionImiscerrors :: ([Error])
              _rightExpressionIself :: MaybeExpression
              _rightExpressionIunboundNames :: Names
              _rightExpressionIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _leftExpressionIcollectInstances  ++  _operatorIcollectInstances  ++  _rightExpressionIcollectInstances
              _lhsOunboundNames =
                  _leftExpressionIunboundNames ++ _operatorIunboundNames ++ _rightExpressionIunboundNames
              _self =
                  Expression_InfixApplication _rangeIself _leftExpressionIself _operatorIself _rightExpressionIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _rightExpressionIcollectScopeInfos
              _lhsOkindErrors =
                  _rightExpressionIkindErrors
              _lhsOmiscerrors =
                  _rightExpressionImiscerrors
              _lhsOwarnings =
                  _rightExpressionIwarnings
              _leftExpressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _leftExpressionOallValueConstructors =
                  _lhsIallValueConstructors
              _leftExpressionOclassEnvironment =
                  _lhsIclassEnvironment
              _leftExpressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _leftExpressionOkindErrors =
                  _lhsIkindErrors
              _leftExpressionOmiscerrors =
                  _lhsImiscerrors
              _leftExpressionOnamesInScope =
                  _lhsInamesInScope
              _leftExpressionOoptions =
                  _lhsIoptions
              _leftExpressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _leftExpressionOtypeConstructors =
                  _lhsItypeConstructors
              _leftExpressionOvalueConstructors =
                  _lhsIvalueConstructors
              _leftExpressionOwarnings =
                  _lhsIwarnings
              _operatorOallTypeConstructors =
                  _lhsIallTypeConstructors
              _operatorOallValueConstructors =
                  _lhsIallValueConstructors
              _operatorOclassEnvironment =
                  _lhsIclassEnvironment
              _operatorOcollectScopeInfos =
                  _leftExpressionIcollectScopeInfos
              _operatorOkindErrors =
                  _leftExpressionIkindErrors
              _operatorOmiscerrors =
                  _leftExpressionImiscerrors
              _operatorOnamesInScope =
                  _lhsInamesInScope
              _operatorOoptions =
                  _lhsIoptions
              _operatorOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _operatorOtypeConstructors =
                  _lhsItypeConstructors
              _operatorOvalueConstructors =
                  _lhsIvalueConstructors
              _operatorOwarnings =
                  _leftExpressionIwarnings
              _rightExpressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _rightExpressionOallValueConstructors =
                  _lhsIallValueConstructors
              _rightExpressionOclassEnvironment =
                  _lhsIclassEnvironment
              _rightExpressionOcollectScopeInfos =
                  _operatorIcollectScopeInfos
              _rightExpressionOkindErrors =
                  _operatorIkindErrors
              _rightExpressionOmiscerrors =
                  _operatorImiscerrors
              _rightExpressionOnamesInScope =
                  _lhsInamesInScope
              _rightExpressionOoptions =
                  _lhsIoptions
              _rightExpressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _rightExpressionOtypeConstructors =
                  _lhsItypeConstructors
              _rightExpressionOvalueConstructors =
                  _lhsIvalueConstructors
              _rightExpressionOwarnings =
                  _operatorIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _leftExpressionIcollectInstances,_leftExpressionIcollectScopeInfos,_leftExpressionIkindErrors,_leftExpressionImiscerrors,_leftExpressionIself,_leftExpressionIunboundNames,_leftExpressionIwarnings) =
                  (leftExpression_ _leftExpressionOallTypeConstructors _leftExpressionOallValueConstructors _leftExpressionOclassEnvironment _leftExpressionOcollectScopeInfos _leftExpressionOkindErrors _leftExpressionOmiscerrors _leftExpressionOnamesInScope _leftExpressionOoptions _leftExpressionOorderedTypeSynonyms _leftExpressionOtypeConstructors _leftExpressionOvalueConstructors _leftExpressionOwarnings )
              ( _operatorIcollectInstances,_operatorIcollectScopeInfos,_operatorIkindErrors,_operatorImiscerrors,_operatorIself,_operatorIunboundNames,_operatorIwarnings) =
                  (operator_ _operatorOallTypeConstructors _operatorOallValueConstructors _operatorOclassEnvironment _operatorOcollectScopeInfos _operatorOkindErrors _operatorOmiscerrors _operatorOnamesInScope _operatorOoptions _operatorOorderedTypeSynonyms _operatorOtypeConstructors _operatorOvalueConstructors _operatorOwarnings )
              ( _rightExpressionIcollectInstances,_rightExpressionIcollectScopeInfos,_rightExpressionIkindErrors,_rightExpressionImiscerrors,_rightExpressionIself,_rightExpressionIunboundNames,_rightExpressionIwarnings) =
                  (rightExpression_ _rightExpressionOallTypeConstructors _rightExpressionOallValueConstructors _rightExpressionOclassEnvironment _rightExpressionOcollectScopeInfos _rightExpressionOkindErrors _rightExpressionOmiscerrors _rightExpressionOnamesInScope _rightExpressionOoptions _rightExpressionOorderedTypeSynonyms _rightExpressionOtypeConstructors _rightExpressionOvalueConstructors _rightExpressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Lambda :: T_Range ->
                         T_Patterns ->
                         T_Expression ->
                         T_Expression
sem_Expression_Lambda range_ patterns_ expression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _patternsOlhsPattern :: Bool
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Expression
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _patternsOallTypeConstructors :: Names
              _patternsOallValueConstructors :: Names
              _patternsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsOmiscerrors :: ([Error])
              _patternsOnamesInScope :: Names
              _patternsOtypeConstructors :: (M.Map Name Int)
              _patternsOvalueConstructors :: (M.Map Name TpScheme)
              _patternsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _patternsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsImiscerrors :: ([Error])
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _patternsIwarnings :: ([Warning])
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              __tup7 =
                  changeOfScope _patternsIpatVarNames _expressionIunboundNames _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup7
              (_,_unboundNames,_) =
                  __tup7
              (_,_,_scopeInfo) =
                  __tup7
              _lhsOunboundNames =
                  _unboundNames
              _patternsOlhsPattern =
                  False
              _lhsOcollectScopeInfos =
                  (_scopeInfo, Variable)   : _expressionIcollectScopeInfos
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _self =
                  Expression_Lambda _rangeIself _patternsIself _expressionIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _expressionIkindErrors
              _lhsOmiscerrors =
                  _expressionImiscerrors
              _lhsOwarnings =
                  _expressionIwarnings
              _patternsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternsOallValueConstructors =
                  _lhsIallValueConstructors
              _patternsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternsOmiscerrors =
                  _lhsImiscerrors
              _patternsOnamesInScope =
                  _namesInScope
              _patternsOtypeConstructors =
                  _lhsItypeConstructors
              _patternsOvalueConstructors =
                  _lhsIvalueConstructors
              _patternsOwarnings =
                  _lhsIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _patternsIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _patternsImiscerrors
              _expressionOnamesInScope =
                  _namesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _patternsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternsIcollectScopeInfos,_patternsImiscerrors,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIself,_patternsIunboundNames,_patternsIwarnings) =
                  (patterns_ _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Let :: T_Range ->
                      T_Declarations ->
                      T_Expression ->
                      T_Expression
sem_Expression_Let range_ declarations_ expression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _declarationsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOunboundNames :: Names
              _lhsOwarnings :: ([Warning])
              _declarationsOpreviousWasAlsoFB :: (Maybe Name)
              _declarationsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOmiscerrors :: ([Error])
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Expression
              _lhsOkindErrors :: ([Error])
              _declarationsOallTypeConstructors :: Names
              _declarationsOallValueConstructors :: Names
              _declarationsOclassEnvironment :: ClassEnvironment
              _declarationsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _declarationsOcollectTypeConstructors :: ([(Name,Int)])
              _declarationsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _declarationsOcollectValueConstructors :: ([(Name,TpScheme)])
              _declarationsOkindErrors :: ([Error])
              _declarationsOmiscerrors :: ([Error])
              _declarationsOnamesInScope :: Names
              _declarationsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _declarationsOoptions :: ([Option])
              _declarationsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _declarationsOtypeConstructors :: (M.Map Name Int)
              _declarationsOvalueConstructors :: (M.Map Name TpScheme)
              _declarationsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _declarationsIcollectInstances :: ([(Name, Instance)])
              _declarationsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _declarationsIcollectTypeConstructors :: ([(Name,Int)])
              _declarationsIcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _declarationsIcollectValueConstructors :: ([(Name,TpScheme)])
              _declarationsIdeclVarNames :: Names
              _declarationsIkindErrors :: ([Error])
              _declarationsImiscerrors :: ([Error])
              _declarationsIoperatorFixities :: ([(Name,(Int,Assoc))])
              _declarationsIpreviousWasAlsoFB :: (Maybe Name)
              _declarationsIrestrictedNames :: Names
              _declarationsIself :: Declarations
              _declarationsIsuspiciousFBs :: ([(Name,Name)])
              _declarationsItypeSignatures :: ([(Name,TpScheme)])
              _declarationsIunboundNames :: Names
              _declarationsIwarnings :: ([Warning])
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _declarationsOtypeSignatures =
                  []
              __tup8 =
                  changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _expressionIunboundNames) _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup8
              (_,_unboundNames,_) =
                  __tup8
              (_,_,_scopeInfo) =
                  __tup8
              _lhsOunboundNames =
                  _unboundNames
              _lhsOwarnings =
                  _expressionIwarnings ++
                  _suspiciousErrors
              _declarationsOpreviousWasAlsoFB =
                  Nothing
              _declarationsOsuspiciousFBs =
                  []
              _suspiciousErrors =
                  findSimilarFunctionBindings _declarationsItypeSignatures _declarationsIsuspiciousFBs
              _lhsOmiscerrors =
                  _typeSignatureErrors ++ _expressionImiscerrors
              __tup9 =
                  uniqueAppearance (map fst _declarationsItypeSignatures)
              (_,_doubles) =
                  __tup9
              _typeSignatureErrors =
                  checkTypeSignatures _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
              __tup10 =
                  internalError "PartialSyntax.ag" "n/a" "toplevel Expression"
              (_collectTypeConstructors,_,_,_,_,_) =
                  __tup10
              (_,_collectValueConstructors,_,_,_,_) =
                  __tup10
              (_,_,_collectTypeSynonyms,_,_,_) =
                  __tup10
              (_,_,_,_collectConstructorEnv,_,_) =
                  __tup10
              (_,_,_,_,_derivedFunctions,_) =
                  __tup10
              (_,_,_,_,_,_operatorFixities) =
                  __tup10
              _lhsOcollectScopeInfos =
                  (_scopeInfo, Definition) : _expressionIcollectScopeInfos
              _lhsOcollectInstances =
                  _declarationsIcollectInstances  ++  _expressionIcollectInstances
              _self =
                  Expression_Let _rangeIself _declarationsIself _expressionIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _expressionIkindErrors
              _declarationsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _declarationsOallValueConstructors =
                  _lhsIallValueConstructors
              _declarationsOclassEnvironment =
                  _lhsIclassEnvironment
              _declarationsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _declarationsOcollectTypeConstructors =
                  _collectTypeConstructors
              _declarationsOcollectTypeSynonyms =
                  _collectTypeSynonyms
              _declarationsOcollectValueConstructors =
                  _collectValueConstructors
              _declarationsOkindErrors =
                  _lhsIkindErrors
              _declarationsOmiscerrors =
                  _lhsImiscerrors
              _declarationsOnamesInScope =
                  _namesInScope
              _declarationsOoperatorFixities =
                  _operatorFixities
              _declarationsOoptions =
                  _lhsIoptions
              _declarationsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _declarationsOtypeConstructors =
                  _lhsItypeConstructors
              _declarationsOvalueConstructors =
                  _lhsIvalueConstructors
              _declarationsOwarnings =
                  _lhsIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _declarationsIcollectScopeInfos
              _expressionOkindErrors =
                  _declarationsIkindErrors
              _expressionOmiscerrors =
                  _declarationsImiscerrors
              _expressionOnamesInScope =
                  _namesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _declarationsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIcollectInstances,_declarationsIcollectScopeInfos,_declarationsIcollectTypeConstructors,_declarationsIcollectTypeSynonyms,_declarationsIcollectValueConstructors,_declarationsIdeclVarNames,_declarationsIkindErrors,_declarationsImiscerrors,_declarationsIoperatorFixities,_declarationsIpreviousWasAlsoFB,_declarationsIrestrictedNames,_declarationsIself,_declarationsIsuspiciousFBs,_declarationsItypeSignatures,_declarationsIunboundNames,_declarationsIwarnings) =
                  (declarations_ _declarationsOallTypeConstructors _declarationsOallValueConstructors _declarationsOclassEnvironment _declarationsOcollectScopeInfos _declarationsOcollectTypeConstructors _declarationsOcollectTypeSynonyms _declarationsOcollectValueConstructors _declarationsOkindErrors _declarationsOmiscerrors _declarationsOnamesInScope _declarationsOoperatorFixities _declarationsOoptions _declarationsOorderedTypeSynonyms _declarationsOpreviousWasAlsoFB _declarationsOsuspiciousFBs _declarationsOtypeConstructors _declarationsOtypeSignatures _declarationsOvalueConstructors _declarationsOwarnings )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_List :: T_Range ->
                       T_Expressions ->
                       T_Expression
sem_Expression_List range_ expressions_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _expressionsOallTypeConstructors :: Names
              _expressionsOallValueConstructors :: Names
              _expressionsOclassEnvironment :: ClassEnvironment
              _expressionsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionsOkindErrors :: ([Error])
              _expressionsOmiscerrors :: ([Error])
              _expressionsOnamesInScope :: Names
              _expressionsOoptions :: ([Option])
              _expressionsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionsOtypeConstructors :: (M.Map Name Int)
              _expressionsOvalueConstructors :: (M.Map Name TpScheme)
              _expressionsOwarnings :: ([Warning])
              _rangeIself :: Range
              _expressionsIcollectInstances :: ([(Name, Instance)])
              _expressionsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionsIkindErrors :: ([Error])
              _expressionsImiscerrors :: ([Error])
              _expressionsIself :: Expressions
              _expressionsIunboundNames :: Names
              _expressionsIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _expressionsIcollectInstances
              _lhsOunboundNames =
                  _expressionsIunboundNames
              _self =
                  Expression_List _rangeIself _expressionsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _expressionsIcollectScopeInfos
              _lhsOkindErrors =
                  _expressionsIkindErrors
              _lhsOmiscerrors =
                  _expressionsImiscerrors
              _lhsOwarnings =
                  _expressionsIwarnings
              _expressionsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionsOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionsOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionsOkindErrors =
                  _lhsIkindErrors
              _expressionsOmiscerrors =
                  _lhsImiscerrors
              _expressionsOnamesInScope =
                  _lhsInamesInScope
              _expressionsOoptions =
                  _lhsIoptions
              _expressionsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionsOtypeConstructors =
                  _lhsItypeConstructors
              _expressionsOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _expressionsIcollectInstances,_expressionsIcollectScopeInfos,_expressionsIkindErrors,_expressionsImiscerrors,_expressionsIself,_expressionsIunboundNames,_expressionsIwarnings) =
                  (expressions_ _expressionsOallTypeConstructors _expressionsOallValueConstructors _expressionsOclassEnvironment _expressionsOcollectScopeInfos _expressionsOkindErrors _expressionsOmiscerrors _expressionsOnamesInScope _expressionsOoptions _expressionsOorderedTypeSynonyms _expressionsOtypeConstructors _expressionsOvalueConstructors _expressionsOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Literal :: T_Range ->
                          T_Literal ->
                          T_Expression
sem_Expression_Literal range_ literal_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _literalOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _literalOmiscerrors :: ([Error])
              _rangeIself :: Range
              _literalIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _literalImiscerrors :: ([Error])
              _literalIself :: Literal
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Expression_Literal _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _literalIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _literalImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              _literalOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _literalOmiscerrors =
                  _lhsImiscerrors
              ( _rangeIself) =
                  (range_ )
              ( _literalIcollectScopeInfos,_literalImiscerrors,_literalIself) =
                  (literal_ _literalOcollectScopeInfos _literalOmiscerrors )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Negate :: T_Range ->
                         T_Expression ->
                         T_Expression
sem_Expression_Negate range_ expression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  Expression_Negate _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _lhsOkindErrors =
                  _expressionIkindErrors
              _lhsOmiscerrors =
                  _expressionImiscerrors
              _lhsOwarnings =
                  _expressionIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _lhsImiscerrors
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_NegateFloat :: T_Range ->
                              T_Expression ->
                              T_Expression
sem_Expression_NegateFloat range_ expression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  Expression_NegateFloat _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _lhsOkindErrors =
                  _expressionIkindErrors
              _lhsOmiscerrors =
                  _expressionImiscerrors
              _lhsOwarnings =
                  _expressionIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _lhsImiscerrors
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_NormalApplication :: T_Range ->
                                    T_Expression ->
                                    T_Expressions ->
                                    T_Expression
sem_Expression_NormalApplication range_ function_ arguments_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _functionOallTypeConstructors :: Names
              _functionOallValueConstructors :: Names
              _functionOclassEnvironment :: ClassEnvironment
              _functionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _functionOkindErrors :: ([Error])
              _functionOmiscerrors :: ([Error])
              _functionOnamesInScope :: Names
              _functionOoptions :: ([Option])
              _functionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _functionOtypeConstructors :: (M.Map Name Int)
              _functionOvalueConstructors :: (M.Map Name TpScheme)
              _functionOwarnings :: ([Warning])
              _argumentsOallTypeConstructors :: Names
              _argumentsOallValueConstructors :: Names
              _argumentsOclassEnvironment :: ClassEnvironment
              _argumentsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _argumentsOkindErrors :: ([Error])
              _argumentsOmiscerrors :: ([Error])
              _argumentsOnamesInScope :: Names
              _argumentsOoptions :: ([Option])
              _argumentsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _argumentsOtypeConstructors :: (M.Map Name Int)
              _argumentsOvalueConstructors :: (M.Map Name TpScheme)
              _argumentsOwarnings :: ([Warning])
              _rangeIself :: Range
              _functionIcollectInstances :: ([(Name, Instance)])
              _functionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _functionIkindErrors :: ([Error])
              _functionImiscerrors :: ([Error])
              _functionIself :: Expression
              _functionIunboundNames :: Names
              _functionIwarnings :: ([Warning])
              _argumentsIcollectInstances :: ([(Name, Instance)])
              _argumentsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _argumentsIkindErrors :: ([Error])
              _argumentsImiscerrors :: ([Error])
              _argumentsIself :: Expressions
              _argumentsIunboundNames :: Names
              _argumentsIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _functionIcollectInstances  ++  _argumentsIcollectInstances
              _lhsOunboundNames =
                  _functionIunboundNames ++ _argumentsIunboundNames
              _self =
                  Expression_NormalApplication _rangeIself _functionIself _argumentsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _argumentsIcollectScopeInfos
              _lhsOkindErrors =
                  _argumentsIkindErrors
              _lhsOmiscerrors =
                  _argumentsImiscerrors
              _lhsOwarnings =
                  _argumentsIwarnings
              _functionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _functionOallValueConstructors =
                  _lhsIallValueConstructors
              _functionOclassEnvironment =
                  _lhsIclassEnvironment
              _functionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _functionOkindErrors =
                  _lhsIkindErrors
              _functionOmiscerrors =
                  _lhsImiscerrors
              _functionOnamesInScope =
                  _lhsInamesInScope
              _functionOoptions =
                  _lhsIoptions
              _functionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _functionOtypeConstructors =
                  _lhsItypeConstructors
              _functionOvalueConstructors =
                  _lhsIvalueConstructors
              _functionOwarnings =
                  _lhsIwarnings
              _argumentsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _argumentsOallValueConstructors =
                  _lhsIallValueConstructors
              _argumentsOclassEnvironment =
                  _lhsIclassEnvironment
              _argumentsOcollectScopeInfos =
                  _functionIcollectScopeInfos
              _argumentsOkindErrors =
                  _functionIkindErrors
              _argumentsOmiscerrors =
                  _functionImiscerrors
              _argumentsOnamesInScope =
                  _lhsInamesInScope
              _argumentsOoptions =
                  _lhsIoptions
              _argumentsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _argumentsOtypeConstructors =
                  _lhsItypeConstructors
              _argumentsOvalueConstructors =
                  _lhsIvalueConstructors
              _argumentsOwarnings =
                  _functionIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _functionIcollectInstances,_functionIcollectScopeInfos,_functionIkindErrors,_functionImiscerrors,_functionIself,_functionIunboundNames,_functionIwarnings) =
                  (function_ _functionOallTypeConstructors _functionOallValueConstructors _functionOclassEnvironment _functionOcollectScopeInfos _functionOkindErrors _functionOmiscerrors _functionOnamesInScope _functionOoptions _functionOorderedTypeSynonyms _functionOtypeConstructors _functionOvalueConstructors _functionOwarnings )
              ( _argumentsIcollectInstances,_argumentsIcollectScopeInfos,_argumentsIkindErrors,_argumentsImiscerrors,_argumentsIself,_argumentsIunboundNames,_argumentsIwarnings) =
                  (arguments_ _argumentsOallTypeConstructors _argumentsOallValueConstructors _argumentsOclassEnvironment _argumentsOcollectScopeInfos _argumentsOkindErrors _argumentsOmiscerrors _argumentsOnamesInScope _argumentsOoptions _argumentsOorderedTypeSynonyms _argumentsOtypeConstructors _argumentsOvalueConstructors _argumentsOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Parenthesized :: T_Range ->
                                T_Expression ->
                                T_Expression
sem_Expression_Parenthesized range_ expression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  Expression_Parenthesized _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _lhsOkindErrors =
                  _expressionIkindErrors
              _lhsOmiscerrors =
                  _expressionImiscerrors
              _lhsOwarnings =
                  _expressionIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _lhsImiscerrors
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_RecordConstruction :: T_Range ->
                                     T_Name ->
                                     T_RecordExpressionBindings ->
                                     T_Expression
sem_Expression_RecordConstruction range_ name_ recordExpressionBindings_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _recordExpressionBindingsOclassEnvironment :: ClassEnvironment
              _recordExpressionBindingsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _recordExpressionBindingsOnamesInScope :: Names
              _recordExpressionBindingsOoptions :: ([Option])
              _recordExpressionBindingsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _rangeIself :: Range
              _nameIself :: Name
              _recordExpressionBindingsIcollectInstances :: ([(Name, Instance)])
              _recordExpressionBindingsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _recordExpressionBindingsIself :: RecordExpressionBindings
              _recordExpressionBindingsIunboundNames :: Names
              __tup11 =
                  internalError "PartialSyntax.ag" "n/a" "Expression.RecordConstruction"
              (_assumptions,_,_) =
                  __tup11
              (_,_constraints,_) =
                  __tup11
              (_,_,_beta) =
                  __tup11
              _lhsOcollectInstances =
                  _recordExpressionBindingsIcollectInstances
              _lhsOunboundNames =
                  _recordExpressionBindingsIunboundNames
              _self =
                  Expression_RecordConstruction _rangeIself _nameIself _recordExpressionBindingsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _recordExpressionBindingsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              _recordExpressionBindingsOclassEnvironment =
                  _lhsIclassEnvironment
              _recordExpressionBindingsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _recordExpressionBindingsOnamesInScope =
                  _lhsInamesInScope
              _recordExpressionBindingsOoptions =
                  _lhsIoptions
              _recordExpressionBindingsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _recordExpressionBindingsIcollectInstances,_recordExpressionBindingsIcollectScopeInfos,_recordExpressionBindingsIself,_recordExpressionBindingsIunboundNames) =
                  (recordExpressionBindings_ _recordExpressionBindingsOclassEnvironment _recordExpressionBindingsOcollectScopeInfos _recordExpressionBindingsOnamesInScope _recordExpressionBindingsOoptions _recordExpressionBindingsOorderedTypeSynonyms )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_RecordUpdate :: T_Range ->
                               T_Expression ->
                               T_RecordExpressionBindings ->
                               T_Expression
sem_Expression_RecordUpdate range_ expression_ recordExpressionBindings_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _recordExpressionBindingsOclassEnvironment :: ClassEnvironment
              _recordExpressionBindingsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _recordExpressionBindingsOnamesInScope :: Names
              _recordExpressionBindingsOoptions :: ([Option])
              _recordExpressionBindingsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _rangeIself :: Range
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _recordExpressionBindingsIcollectInstances :: ([(Name, Instance)])
              _recordExpressionBindingsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _recordExpressionBindingsIself :: RecordExpressionBindings
              _recordExpressionBindingsIunboundNames :: Names
              _lhsOcollectInstances =
                  _expressionIcollectInstances  ++  _recordExpressionBindingsIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames ++ _recordExpressionBindingsIunboundNames
              _self =
                  Expression_RecordUpdate _rangeIself _expressionIself _recordExpressionBindingsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _recordExpressionBindingsIcollectScopeInfos
              _lhsOkindErrors =
                  _expressionIkindErrors
              _lhsOmiscerrors =
                  _expressionImiscerrors
              _lhsOwarnings =
                  _expressionIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _lhsImiscerrors
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _lhsIwarnings
              _recordExpressionBindingsOclassEnvironment =
                  _lhsIclassEnvironment
              _recordExpressionBindingsOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _recordExpressionBindingsOnamesInScope =
                  _lhsInamesInScope
              _recordExpressionBindingsOoptions =
                  _lhsIoptions
              _recordExpressionBindingsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
              ( _recordExpressionBindingsIcollectInstances,_recordExpressionBindingsIcollectScopeInfos,_recordExpressionBindingsIself,_recordExpressionBindingsIunboundNames) =
                  (recordExpressionBindings_ _recordExpressionBindingsOclassEnvironment _recordExpressionBindingsOcollectScopeInfos _recordExpressionBindingsOnamesInScope _recordExpressionBindingsOoptions _recordExpressionBindingsOorderedTypeSynonyms )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Tuple :: T_Range ->
                        T_Expressions ->
                        T_Expression
sem_Expression_Tuple range_ expressions_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOmiscerrors :: ([Error])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _expressionsOallTypeConstructors :: Names
              _expressionsOallValueConstructors :: Names
              _expressionsOclassEnvironment :: ClassEnvironment
              _expressionsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionsOkindErrors :: ([Error])
              _expressionsOmiscerrors :: ([Error])
              _expressionsOnamesInScope :: Names
              _expressionsOoptions :: ([Option])
              _expressionsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionsOtypeConstructors :: (M.Map Name Int)
              _expressionsOvalueConstructors :: (M.Map Name TpScheme)
              _expressionsOwarnings :: ([Warning])
              _rangeIself :: Range
              _expressionsIcollectInstances :: ([(Name, Instance)])
              _expressionsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionsIkindErrors :: ([Error])
              _expressionsImiscerrors :: ([Error])
              _expressionsIself :: Expressions
              _expressionsIunboundNames :: Names
              _expressionsIwarnings :: ([Warning])
              _lhsOmiscerrors =
                  _tupleTooBigErrors ++ _expressionsImiscerrors
              _tupleTooBigErrors =
                  [ TupleTooBig _rangeIself
                  | length _expressionsIself > 10
                  ]
              _lhsOcollectInstances =
                  _expressionsIcollectInstances
              _lhsOunboundNames =
                  _expressionsIunboundNames
              _self =
                  Expression_Tuple _rangeIself _expressionsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _expressionsIcollectScopeInfos
              _lhsOkindErrors =
                  _expressionsIkindErrors
              _lhsOwarnings =
                  _expressionsIwarnings
              _expressionsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionsOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionsOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionsOkindErrors =
                  _lhsIkindErrors
              _expressionsOmiscerrors =
                  _lhsImiscerrors
              _expressionsOnamesInScope =
                  _lhsInamesInScope
              _expressionsOoptions =
                  _lhsIoptions
              _expressionsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionsOtypeConstructors =
                  _lhsItypeConstructors
              _expressionsOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _expressionsIcollectInstances,_expressionsIcollectScopeInfos,_expressionsIkindErrors,_expressionsImiscerrors,_expressionsIself,_expressionsIunboundNames,_expressionsIwarnings) =
                  (expressions_ _expressionsOallTypeConstructors _expressionsOallValueConstructors _expressionsOclassEnvironment _expressionsOcollectScopeInfos _expressionsOkindErrors _expressionsOmiscerrors _expressionsOnamesInScope _expressionsOoptions _expressionsOorderedTypeSynonyms _expressionsOtypeConstructors _expressionsOvalueConstructors _expressionsOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Typed :: T_Range ->
                        T_Expression ->
                        T_Type ->
                        T_Expression
sem_Expression_Typed range_ expression_ type_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOkindErrors :: ([Error])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _typeOallTypeConstructors :: Names
              _typeOmiscerrors :: ([Error])
              _typeOoptions :: ([Option])
              _typeOtypeConstructors :: (M.Map Name Int)
              _typeOwarnings :: ([Warning])
              _rangeIself :: Range
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _typeIcontextRange :: Range
              _typeImiscerrors :: ([Error])
              _typeIself :: Type
              _typeItypevariables :: Names
              _typeIwarnings :: ([Warning])
              _lhsOkindErrors =
                  _newErrors ++ _expressionIkindErrors
              _newErrors =
                  checkType _lhsItypeConstructors (_lhsInamesInScope ++ _lhsIallValueConstructors) _typeIself
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  Expression_Typed _rangeIself _expressionIself _typeIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _lhsOmiscerrors =
                  _typeImiscerrors
              _lhsOwarnings =
                  _typeIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _lhsImiscerrors
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _lhsIwarnings
              _typeOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typeOmiscerrors =
                  _expressionImiscerrors
              _typeOoptions =
                  _lhsIoptions
              _typeOtypeConstructors =
                  _lhsItypeConstructors
              _typeOwarnings =
                  _expressionIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
              ( _typeIcontextRange,_typeImiscerrors,_typeIself,_typeItypevariables,_typeIwarnings) =
                  (type_ _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expression_Variable :: T_Range ->
                           T_Name ->
                           T_Expression
sem_Expression_Variable range_ name_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _lhsOmiscerrors :: ([Error])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Expression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOunboundNames =
                  [ _nameIself ]
              _lhsOmiscerrors =
                  _undefinedErrors ++ _lhsImiscerrors
              _undefinedErrors =
                  if _nameIself `elem` _lhsInamesInScope
                    then []
                    else [ Undefined Variable _nameIself _lhsInamesInScope [] ]
              _lhsOcollectInstances =
                  []
              _self =
                  Expression_Variable _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- Expressions -------------------------------------------------
-- cata
sem_Expressions :: Expressions ->
                   T_Expressions
sem_Expressions list  =
    (Prelude.foldr sem_Expressions_Cons sem_Expressions_Nil (Prelude.map sem_Expression list) )
-- semantic domain
type T_Expressions = Names ->
                     Names ->
                     ClassEnvironment ->
                     ([(ScopeInfo, Entity)]) ->
                     ([Error]) ->
                     ([Error]) ->
                     Names ->
                     ([Option]) ->
                     OrderedTypeSynonyms ->
                     (M.Map Name Int) ->
                     (M.Map Name TpScheme) ->
                     ([Warning]) ->
                     ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),Expressions,Names,([Warning]))
sem_Expressions_Cons :: T_Expression ->
                        T_Expressions ->
                        T_Expressions
sem_Expressions_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expressions
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOallValueConstructors :: Names
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOkindErrors :: ([Error])
              _hdOmiscerrors :: ([Error])
              _hdOnamesInScope :: Names
              _hdOoptions :: ([Option])
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOvalueConstructors :: (M.Map Name TpScheme)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOallValueConstructors :: Names
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlOkindErrors :: ([Error])
              _tlOmiscerrors :: ([Error])
              _tlOnamesInScope :: Names
              _tlOoptions :: ([Option])
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOvalueConstructors :: (M.Map Name TpScheme)
              _tlOwarnings :: ([Warning])
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdIkindErrors :: ([Error])
              _hdImiscerrors :: ([Error])
              _hdIself :: Expression
              _hdIunboundNames :: Names
              _hdIwarnings :: ([Warning])
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlIkindErrors :: ([Error])
              _tlImiscerrors :: ([Error])
              _tlIself :: Expressions
              _tlIunboundNames :: Names
              _tlIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _tlIcollectScopeInfos
              _lhsOkindErrors =
                  _tlIkindErrors
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOallValueConstructors =
                  _lhsIallValueConstructors
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _hdOkindErrors =
                  _lhsIkindErrors
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOoptions =
                  _lhsIoptions
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOvalueConstructors =
                  _lhsIvalueConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOallValueConstructors =
                  _lhsIallValueConstructors
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectScopeInfos =
                  _hdIcollectScopeInfos
              _tlOkindErrors =
                  _hdIkindErrors
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOoptions =
                  _lhsIoptions
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOvalueConstructors =
                  _lhsIvalueConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIcollectInstances,_hdIcollectScopeInfos,_hdIkindErrors,_hdImiscerrors,_hdIself,_hdIunboundNames,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings )
              ( _tlIcollectInstances,_tlIcollectScopeInfos,_tlIkindErrors,_tlImiscerrors,_tlIself,_tlIunboundNames,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Expressions_Nil :: T_Expressions
sem_Expressions_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: Expressions
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- FieldDeclaration --------------------------------------------
-- cata
sem_FieldDeclaration :: FieldDeclaration ->
                        T_FieldDeclaration
sem_FieldDeclaration (FieldDeclaration_FieldDeclaration _range _names _type )  =
    (sem_FieldDeclaration_FieldDeclaration (sem_Range _range ) (sem_Names _names ) (sem_AnnotatedType _type ) )
-- semantic domain
type T_FieldDeclaration = ([Error]) ->
                          Names ->
                          ([Option]) ->
                          ( ([Error]),FieldDeclaration,Names)
sem_FieldDeclaration_FieldDeclaration :: T_Range ->
                                         T_Names ->
                                         T_AnnotatedType ->
                                         T_FieldDeclaration
sem_FieldDeclaration_FieldDeclaration range_ names_ type_  =
    (\ _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: FieldDeclaration
              _lhsOmiscerrors :: ([Error])
              _typeOallTypeConstructors :: Names
              _typeOallValueConstructors :: Names
              _typeOkindErrors :: ([Error])
              _typeOmiscerrors :: ([Error])
              _typeOnamesInScope :: Names
              _typeOoptions :: ([Option])
              _typeOtypeConstructors :: (M.Map Name Int)
              _typeOvalueConstructors :: (M.Map Name TpScheme)
              _typeOwarnings :: ([Warning])
              _rangeIself :: Range
              _namesIself :: Names
              _typeIkindErrors :: ([Error])
              _typeImiscerrors :: ([Error])
              _typeIself :: AnnotatedType
              _typeItype :: Type
              _typeItypevariables :: Names
              _typeIunboundNames :: Names
              _typeIwarnings :: ([Warning])
              __tup12 =
                  internalError "PartialSyntax.ag" "n/a" "FieldDeclaration.FieldDeclaration"
              (_kindErrors,_,_,_,_,_,_,_,_) =
                  __tup12
              (_,_tyconEnv,_,_,_,_,_,_,_) =
                  __tup12
              (_,_,_constructorenv,_,_,_,_,_,_) =
                  __tup12
              (_,_,_,_importEnvironment,_,_,_,_,_) =
                  __tup12
              (_,_,_,_,_valueConstructors,_,_,_,_) =
                  __tup12
              (_,_,_,_,_,_allValueConstructors,_,_,_) =
                  __tup12
              (_,_,_,_,_,_,_typeConstructors,_,_) =
                  __tup12
              (_,_,_,_,_,_,_,_allTypeConstructors,_) =
                  __tup12
              (_,_,_,_,_,_,_,_,_warnings) =
                  __tup12
              _lhsOunboundNames =
                  _typeIunboundNames
              _self =
                  FieldDeclaration_FieldDeclaration _rangeIself _namesIself _typeIself
              _lhsOself =
                  _self
              _lhsOmiscerrors =
                  _typeImiscerrors
              _typeOallTypeConstructors =
                  _allTypeConstructors
              _typeOallValueConstructors =
                  _allValueConstructors
              _typeOkindErrors =
                  _kindErrors
              _typeOmiscerrors =
                  _lhsImiscerrors
              _typeOnamesInScope =
                  _lhsInamesInScope
              _typeOoptions =
                  _lhsIoptions
              _typeOtypeConstructors =
                  _typeConstructors
              _typeOvalueConstructors =
                  _valueConstructors
              _typeOwarnings =
                  _warnings
              ( _rangeIself) =
                  (range_ )
              ( _namesIself) =
                  (names_ )
              ( _typeIkindErrors,_typeImiscerrors,_typeIself,_typeItype,_typeItypevariables,_typeIunboundNames,_typeIwarnings) =
                  (type_ _typeOallTypeConstructors _typeOallValueConstructors _typeOkindErrors _typeOmiscerrors _typeOnamesInScope _typeOoptions _typeOtypeConstructors _typeOvalueConstructors _typeOwarnings )
          in  ( _lhsOmiscerrors,_lhsOself,_lhsOunboundNames)))
-- FieldDeclarations -------------------------------------------
-- cata
sem_FieldDeclarations :: FieldDeclarations ->
                         T_FieldDeclarations
sem_FieldDeclarations list  =
    (Prelude.foldr sem_FieldDeclarations_Cons sem_FieldDeclarations_Nil (Prelude.map sem_FieldDeclaration list) )
-- semantic domain
type T_FieldDeclarations = ([Error]) ->
                           Names ->
                           ([Option]) ->
                           ( ([Error]),FieldDeclarations,Names)
sem_FieldDeclarations_Cons :: T_FieldDeclaration ->
                              T_FieldDeclarations ->
                              T_FieldDeclarations
sem_FieldDeclarations_Cons hd_ tl_  =
    (\ _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: FieldDeclarations
              _lhsOmiscerrors :: ([Error])
              _hdOmiscerrors :: ([Error])
              _hdOnamesInScope :: Names
              _hdOoptions :: ([Option])
              _tlOmiscerrors :: ([Error])
              _tlOnamesInScope :: Names
              _tlOoptions :: ([Option])
              _hdImiscerrors :: ([Error])
              _hdIself :: FieldDeclaration
              _hdIunboundNames :: Names
              _tlImiscerrors :: ([Error])
              _tlIself :: FieldDeclarations
              _tlIunboundNames :: Names
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOmiscerrors =
                  _tlImiscerrors
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOoptions =
                  _lhsIoptions
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOoptions =
                  _lhsIoptions
              ( _hdImiscerrors,_hdIself,_hdIunboundNames) =
                  (hd_ _hdOmiscerrors _hdOnamesInScope _hdOoptions )
              ( _tlImiscerrors,_tlIself,_tlIunboundNames) =
                  (tl_ _tlOmiscerrors _tlOnamesInScope _tlOoptions )
          in  ( _lhsOmiscerrors,_lhsOself,_lhsOunboundNames)))
sem_FieldDeclarations_Nil :: T_FieldDeclarations
sem_FieldDeclarations_Nil  =
    (\ _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: FieldDeclarations
              _lhsOmiscerrors :: ([Error])
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOmiscerrors =
                  _lhsImiscerrors
          in  ( _lhsOmiscerrors,_lhsOself,_lhsOunboundNames)))
-- Fixity ------------------------------------------------------
-- cata
sem_Fixity :: Fixity ->
              T_Fixity
sem_Fixity (Fixity_Infix _range )  =
    (sem_Fixity_Infix (sem_Range _range ) )
sem_Fixity (Fixity_Infixl _range )  =
    (sem_Fixity_Infixl (sem_Range _range ) )
sem_Fixity (Fixity_Infixr _range )  =
    (sem_Fixity_Infixr (sem_Range _range ) )
-- semantic domain
type T_Fixity = ( Fixity)
sem_Fixity_Infix :: T_Range ->
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
sem_Fixity_Infixl :: T_Range ->
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
sem_Fixity_Infixr :: T_Range ->
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
sem_FunctionBinding :: FunctionBinding ->
                       T_FunctionBinding
sem_FunctionBinding (FunctionBinding_FunctionBinding _range _lefthandside _righthandside )  =
    (sem_FunctionBinding_FunctionBinding (sem_Range _range ) (sem_LeftHandSide _lefthandside ) (sem_RightHandSide _righthandside ) )
-- semantic domain
type T_FunctionBinding = Names ->
                         Names ->
                         ClassEnvironment ->
                         ([(ScopeInfo, Entity)]) ->
                         ([Error]) ->
                         ([Error]) ->
                         Names ->
                         ([Option]) ->
                         OrderedTypeSynonyms ->
                         (M.Map Name Int) ->
                         (M.Map Name TpScheme) ->
                         ([Warning]) ->
                         ( Int,([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),Name,FunctionBinding,Names,([Warning]))
sem_FunctionBinding_FunctionBinding :: T_Range ->
                                       T_LeftHandSide ->
                                       T_RightHandSide ->
                                       T_FunctionBinding
sem_FunctionBinding_FunctionBinding range_ lefthandside_ righthandside_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _lhsOarity :: Int
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: FunctionBinding
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOname :: Name
              _lhsOwarnings :: ([Warning])
              _lefthandsideOallTypeConstructors :: Names
              _lefthandsideOallValueConstructors :: Names
              _lefthandsideOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lefthandsideOmiscerrors :: ([Error])
              _lefthandsideOnamesInScope :: Names
              _lefthandsideOtypeConstructors :: (M.Map Name Int)
              _lefthandsideOvalueConstructors :: (M.Map Name TpScheme)
              _lefthandsideOwarnings :: ([Warning])
              _righthandsideOallTypeConstructors :: Names
              _righthandsideOallValueConstructors :: Names
              _righthandsideOclassEnvironment :: ClassEnvironment
              _righthandsideOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _righthandsideOkindErrors :: ([Error])
              _righthandsideOmiscerrors :: ([Error])
              _righthandsideOnamesInScope :: Names
              _righthandsideOoptions :: ([Option])
              _righthandsideOorderedTypeSynonyms :: OrderedTypeSynonyms
              _righthandsideOtypeConstructors :: (M.Map Name Int)
              _righthandsideOvalueConstructors :: (M.Map Name TpScheme)
              _righthandsideOwarnings :: ([Warning])
              _rangeIself :: Range
              _lefthandsideIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lefthandsideImiscerrors :: ([Error])
              _lefthandsideIname :: Name
              _lefthandsideInumberOfPatterns :: Int
              _lefthandsideIpatVarNames :: Names
              _lefthandsideIself :: LeftHandSide
              _lefthandsideIunboundNames :: Names
              _lefthandsideIwarnings :: ([Warning])
              _righthandsideIcollectInstances :: ([(Name, Instance)])
              _righthandsideIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _righthandsideIkindErrors :: ([Error])
              _righthandsideImiscerrors :: ([Error])
              _righthandsideIself :: RightHandSide
              _righthandsideIunboundNames :: Names
              _righthandsideIwarnings :: ([Warning])
              __tup13 =
                  changeOfScope _lefthandsideIpatVarNames _righthandsideIunboundNames _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup13
              (_,_unboundNames,_) =
                  __tup13
              (_,_,_scopeInfo) =
                  __tup13
              _lhsOunboundNames =
                  _unboundNames
              _lhsOarity =
                  _lefthandsideInumberOfPatterns
              _lhsOcollectScopeInfos =
                  (_scopeInfo, Variable)   : _righthandsideIcollectScopeInfos
              _lhsOcollectInstances =
                  _righthandsideIcollectInstances
              _self =
                  FunctionBinding_FunctionBinding _rangeIself _lefthandsideIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _righthandsideIkindErrors
              _lhsOmiscerrors =
                  _righthandsideImiscerrors
              _lhsOname =
                  _lefthandsideIname
              _lhsOwarnings =
                  _righthandsideIwarnings
              _lefthandsideOallTypeConstructors =
                  _lhsIallTypeConstructors
              _lefthandsideOallValueConstructors =
                  _lhsIallValueConstructors
              _lefthandsideOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lefthandsideOmiscerrors =
                  _lhsImiscerrors
              _lefthandsideOnamesInScope =
                  _namesInScope
              _lefthandsideOtypeConstructors =
                  _lhsItypeConstructors
              _lefthandsideOvalueConstructors =
                  _lhsIvalueConstructors
              _lefthandsideOwarnings =
                  _lhsIwarnings
              _righthandsideOallTypeConstructors =
                  _lhsIallTypeConstructors
              _righthandsideOallValueConstructors =
                  _lhsIallValueConstructors
              _righthandsideOclassEnvironment =
                  _lhsIclassEnvironment
              _righthandsideOcollectScopeInfos =
                  _lefthandsideIcollectScopeInfos
              _righthandsideOkindErrors =
                  _lhsIkindErrors
              _righthandsideOmiscerrors =
                  _lefthandsideImiscerrors
              _righthandsideOnamesInScope =
                  _namesInScope
              _righthandsideOoptions =
                  _lhsIoptions
              _righthandsideOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _righthandsideOtypeConstructors =
                  _lhsItypeConstructors
              _righthandsideOvalueConstructors =
                  _lhsIvalueConstructors
              _righthandsideOwarnings =
                  _lefthandsideIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _lefthandsideIcollectScopeInfos,_lefthandsideImiscerrors,_lefthandsideIname,_lefthandsideInumberOfPatterns,_lefthandsideIpatVarNames,_lefthandsideIself,_lefthandsideIunboundNames,_lefthandsideIwarnings) =
                  (lefthandside_ _lefthandsideOallTypeConstructors _lefthandsideOallValueConstructors _lefthandsideOcollectScopeInfos _lefthandsideOmiscerrors _lefthandsideOnamesInScope _lefthandsideOtypeConstructors _lefthandsideOvalueConstructors _lefthandsideOwarnings )
              ( _righthandsideIcollectInstances,_righthandsideIcollectScopeInfos,_righthandsideIkindErrors,_righthandsideImiscerrors,_righthandsideIself,_righthandsideIunboundNames,_righthandsideIwarnings) =
                  (righthandside_ _righthandsideOallTypeConstructors _righthandsideOallValueConstructors _righthandsideOclassEnvironment _righthandsideOcollectScopeInfos _righthandsideOkindErrors _righthandsideOmiscerrors _righthandsideOnamesInScope _righthandsideOoptions _righthandsideOorderedTypeSynonyms _righthandsideOtypeConstructors _righthandsideOvalueConstructors _righthandsideOwarnings )
          in  ( _lhsOarity,_lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOname,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- FunctionBindings --------------------------------------------
-- cata
sem_FunctionBindings :: FunctionBindings ->
                        T_FunctionBindings
sem_FunctionBindings list  =
    (Prelude.foldr sem_FunctionBindings_Cons sem_FunctionBindings_Nil (Prelude.map sem_FunctionBinding list) )
-- semantic domain
type T_FunctionBindings = Names ->
                          Names ->
                          ClassEnvironment ->
                          ([(ScopeInfo, Entity)]) ->
                          ([Error]) ->
                          ([Error]) ->
                          Names ->
                          ([Option]) ->
                          OrderedTypeSynonyms ->
                          (M.Map Name Int) ->
                          (M.Map Name TpScheme) ->
                          ([Warning]) ->
                          ( ( [Int] ),([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),Name,FunctionBindings,Names,([Warning]))
sem_FunctionBindings_Cons :: T_FunctionBinding ->
                             T_FunctionBindings ->
                             T_FunctionBindings
sem_FunctionBindings_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOname :: Name
              _lhsOarities :: ( [Int] )
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: FunctionBindings
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOallValueConstructors :: Names
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOkindErrors :: ([Error])
              _hdOmiscerrors :: ([Error])
              _hdOnamesInScope :: Names
              _hdOoptions :: ([Option])
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOvalueConstructors :: (M.Map Name TpScheme)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOallValueConstructors :: Names
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlOkindErrors :: ([Error])
              _tlOmiscerrors :: ([Error])
              _tlOnamesInScope :: Names
              _tlOoptions :: ([Option])
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOvalueConstructors :: (M.Map Name TpScheme)
              _tlOwarnings :: ([Warning])
              _hdIarity :: Int
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdIkindErrors :: ([Error])
              _hdImiscerrors :: ([Error])
              _hdIname :: Name
              _hdIself :: FunctionBinding
              _hdIunboundNames :: Names
              _hdIwarnings :: ([Warning])
              _tlIarities :: ( [Int] )
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlIkindErrors :: ([Error])
              _tlImiscerrors :: ([Error])
              _tlIname :: Name
              _tlIself :: FunctionBindings
              _tlIunboundNames :: Names
              _tlIwarnings :: ([Warning])
              _lhsOname =
                  _hdIname
              _lhsOarities =
                  _hdIarity : _tlIarities
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _tlIcollectScopeInfos
              _lhsOkindErrors =
                  _tlIkindErrors
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOallValueConstructors =
                  _lhsIallValueConstructors
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _hdOkindErrors =
                  _lhsIkindErrors
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOoptions =
                  _lhsIoptions
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOvalueConstructors =
                  _lhsIvalueConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOallValueConstructors =
                  _lhsIallValueConstructors
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectScopeInfos =
                  _hdIcollectScopeInfos
              _tlOkindErrors =
                  _hdIkindErrors
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOoptions =
                  _lhsIoptions
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOvalueConstructors =
                  _lhsIvalueConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIarity,_hdIcollectInstances,_hdIcollectScopeInfos,_hdIkindErrors,_hdImiscerrors,_hdIname,_hdIself,_hdIunboundNames,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings )
              ( _tlIarities,_tlIcollectInstances,_tlIcollectScopeInfos,_tlIkindErrors,_tlImiscerrors,_tlIname,_tlIself,_tlIunboundNames,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings )
          in  ( _lhsOarities,_lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOname,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_FunctionBindings_Nil :: T_FunctionBindings
sem_FunctionBindings_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOname :: Name
              _lhsOarities :: ( [Int] )
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: FunctionBindings
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _lhsOname =
                  internalError "StaticChecks.ag" "n/a" "empty FunctionBindings"
              _lhsOarities =
                  []
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOarities,_lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOname,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- GuardedExpression -------------------------------------------
-- cata
sem_GuardedExpression :: GuardedExpression ->
                         T_GuardedExpression
sem_GuardedExpression (GuardedExpression_GuardedExpression _range _guard _expression )  =
    (sem_GuardedExpression_GuardedExpression (sem_Range _range ) (sem_Expression _guard ) (sem_Expression _expression ) )
-- semantic domain
type T_GuardedExpression = Names ->
                           Names ->
                           ClassEnvironment ->
                           ([(ScopeInfo, Entity)]) ->
                           ([Error]) ->
                           ([Error]) ->
                           Names ->
                           ([Option]) ->
                           OrderedTypeSynonyms ->
                           (M.Map Name Int) ->
                           (M.Map Name TpScheme) ->
                           ([Warning]) ->
                           ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),GuardedExpression,Names,([Warning]))
sem_GuardedExpression_GuardedExpression :: T_Range ->
                                           T_Expression ->
                                           T_Expression ->
                                           T_GuardedExpression
sem_GuardedExpression_GuardedExpression range_ guard_ expression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: GuardedExpression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _guardOallTypeConstructors :: Names
              _guardOallValueConstructors :: Names
              _guardOclassEnvironment :: ClassEnvironment
              _guardOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _guardOkindErrors :: ([Error])
              _guardOmiscerrors :: ([Error])
              _guardOnamesInScope :: Names
              _guardOoptions :: ([Option])
              _guardOorderedTypeSynonyms :: OrderedTypeSynonyms
              _guardOtypeConstructors :: (M.Map Name Int)
              _guardOvalueConstructors :: (M.Map Name TpScheme)
              _guardOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _guardIcollectInstances :: ([(Name, Instance)])
              _guardIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _guardIkindErrors :: ([Error])
              _guardImiscerrors :: ([Error])
              _guardIself :: Expression
              _guardIunboundNames :: Names
              _guardIwarnings :: ([Warning])
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _guardIcollectInstances  ++  _expressionIcollectInstances
              _lhsOunboundNames =
                  _guardIunboundNames ++ _expressionIunboundNames
              _self =
                  GuardedExpression_GuardedExpression _rangeIself _guardIself _expressionIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _lhsOkindErrors =
                  _expressionIkindErrors
              _lhsOmiscerrors =
                  _expressionImiscerrors
              _lhsOwarnings =
                  _expressionIwarnings
              _guardOallTypeConstructors =
                  _lhsIallTypeConstructors
              _guardOallValueConstructors =
                  _lhsIallValueConstructors
              _guardOclassEnvironment =
                  _lhsIclassEnvironment
              _guardOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _guardOkindErrors =
                  _lhsIkindErrors
              _guardOmiscerrors =
                  _lhsImiscerrors
              _guardOnamesInScope =
                  _lhsInamesInScope
              _guardOoptions =
                  _lhsIoptions
              _guardOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _guardOtypeConstructors =
                  _lhsItypeConstructors
              _guardOvalueConstructors =
                  _lhsIvalueConstructors
              _guardOwarnings =
                  _lhsIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _guardIcollectScopeInfos
              _expressionOkindErrors =
                  _guardIkindErrors
              _expressionOmiscerrors =
                  _guardImiscerrors
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _guardIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _guardIcollectInstances,_guardIcollectScopeInfos,_guardIkindErrors,_guardImiscerrors,_guardIself,_guardIunboundNames,_guardIwarnings) =
                  (guard_ _guardOallTypeConstructors _guardOallValueConstructors _guardOclassEnvironment _guardOcollectScopeInfos _guardOkindErrors _guardOmiscerrors _guardOnamesInScope _guardOoptions _guardOorderedTypeSynonyms _guardOtypeConstructors _guardOvalueConstructors _guardOwarnings )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- GuardedExpressions ------------------------------------------
-- cata
sem_GuardedExpressions :: GuardedExpressions ->
                          T_GuardedExpressions
sem_GuardedExpressions list  =
    (Prelude.foldr sem_GuardedExpressions_Cons sem_GuardedExpressions_Nil (Prelude.map sem_GuardedExpression list) )
-- semantic domain
type T_GuardedExpressions = Names ->
                            Names ->
                            ClassEnvironment ->
                            ([(ScopeInfo, Entity)]) ->
                            ([Error]) ->
                            ([Error]) ->
                            Names ->
                            ([Option]) ->
                            OrderedTypeSynonyms ->
                            (M.Map Name Int) ->
                            (M.Map Name TpScheme) ->
                            ([Warning]) ->
                            ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),GuardedExpressions,Names,([Warning]))
sem_GuardedExpressions_Cons :: T_GuardedExpression ->
                               T_GuardedExpressions ->
                               T_GuardedExpressions
sem_GuardedExpressions_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: GuardedExpressions
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOallValueConstructors :: Names
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOkindErrors :: ([Error])
              _hdOmiscerrors :: ([Error])
              _hdOnamesInScope :: Names
              _hdOoptions :: ([Option])
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOvalueConstructors :: (M.Map Name TpScheme)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOallValueConstructors :: Names
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlOkindErrors :: ([Error])
              _tlOmiscerrors :: ([Error])
              _tlOnamesInScope :: Names
              _tlOoptions :: ([Option])
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOvalueConstructors :: (M.Map Name TpScheme)
              _tlOwarnings :: ([Warning])
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdIkindErrors :: ([Error])
              _hdImiscerrors :: ([Error])
              _hdIself :: GuardedExpression
              _hdIunboundNames :: Names
              _hdIwarnings :: ([Warning])
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlIkindErrors :: ([Error])
              _tlImiscerrors :: ([Error])
              _tlIself :: GuardedExpressions
              _tlIunboundNames :: Names
              _tlIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _tlIcollectScopeInfos
              _lhsOkindErrors =
                  _tlIkindErrors
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOallValueConstructors =
                  _lhsIallValueConstructors
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _hdOkindErrors =
                  _lhsIkindErrors
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOoptions =
                  _lhsIoptions
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOvalueConstructors =
                  _lhsIvalueConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOallValueConstructors =
                  _lhsIallValueConstructors
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectScopeInfos =
                  _hdIcollectScopeInfos
              _tlOkindErrors =
                  _hdIkindErrors
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOoptions =
                  _lhsIoptions
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOvalueConstructors =
                  _lhsIvalueConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIcollectInstances,_hdIcollectScopeInfos,_hdIkindErrors,_hdImiscerrors,_hdIself,_hdIunboundNames,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings )
              ( _tlIcollectInstances,_tlIcollectScopeInfos,_tlIkindErrors,_tlImiscerrors,_tlIself,_tlIunboundNames,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_GuardedExpressions_Nil :: T_GuardedExpressions
sem_GuardedExpressions_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: GuardedExpressions
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- Import ------------------------------------------------------
-- cata
sem_Import :: Import ->
              T_Import
sem_Import (Import_TypeOrClass _range _name _names )  =
    (sem_Import_TypeOrClass (sem_Range _range ) (sem_Name _name ) (sem_MaybeNames _names ) )
sem_Import (Import_TypeOrClassComplete _range _name )  =
    (sem_Import_TypeOrClassComplete (sem_Range _range ) (sem_Name _name ) )
sem_Import (Import_Variable _range _name )  =
    (sem_Import_Variable (sem_Range _range ) (sem_Name _name ) )
-- semantic domain
type T_Import = ( Import)
sem_Import_TypeOrClass :: T_Range ->
                          T_Name ->
                          T_MaybeNames ->
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
sem_Import_TypeOrClassComplete :: T_Range ->
                                  T_Name ->
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
sem_Import_Variable :: T_Range ->
                       T_Name ->
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
sem_ImportDeclaration :: ImportDeclaration ->
                         T_ImportDeclaration
sem_ImportDeclaration (ImportDeclaration_Empty _range )  =
    (sem_ImportDeclaration_Empty (sem_Range _range ) )
sem_ImportDeclaration (ImportDeclaration_Import _range _qualified _name _asname _importspecification )  =
    (sem_ImportDeclaration_Import (sem_Range _range ) _qualified (sem_Name _name ) (sem_MaybeName _asname ) (sem_MaybeImportSpecification _importspecification ) )
-- semantic domain
type T_ImportDeclaration = Names ->
                           ( Names,ImportDeclaration)
sem_ImportDeclaration_Empty :: T_Range ->
                               T_ImportDeclaration
sem_ImportDeclaration_Empty range_  =
    (\ _lhsIimportedModules ->
         (let _lhsOself :: ImportDeclaration
              _lhsOimportedModules :: Names
              _rangeIself :: Range
              _self =
                  ImportDeclaration_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOimportedModules =
                  _lhsIimportedModules
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOimportedModules,_lhsOself)))
sem_ImportDeclaration_Import :: T_Range ->
                                Bool ->
                                T_Name ->
                                T_MaybeName ->
                                T_MaybeImportSpecification ->
                                T_ImportDeclaration
sem_ImportDeclaration_Import range_ qualified_ name_ asname_ importspecification_  =
    (\ _lhsIimportedModules ->
         (let _lhsOimportedModules :: Names
              _lhsOself :: ImportDeclaration
              _rangeIself :: Range
              _nameIself :: Name
              _asnameIself :: MaybeName
              _importspecificationIself :: MaybeImportSpecification
              _lhsOimportedModules =
                  _nameIself : _lhsIimportedModules
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
          in  ( _lhsOimportedModules,_lhsOself)))
-- ImportDeclarations ------------------------------------------
-- cata
sem_ImportDeclarations :: ImportDeclarations ->
                          T_ImportDeclarations
sem_ImportDeclarations list  =
    (Prelude.foldr sem_ImportDeclarations_Cons sem_ImportDeclarations_Nil (Prelude.map sem_ImportDeclaration list) )
-- semantic domain
type T_ImportDeclarations = Names ->
                            ( Names,ImportDeclarations)
sem_ImportDeclarations_Cons :: T_ImportDeclaration ->
                               T_ImportDeclarations ->
                               T_ImportDeclarations
sem_ImportDeclarations_Cons hd_ tl_  =
    (\ _lhsIimportedModules ->
         (let _lhsOself :: ImportDeclarations
              _lhsOimportedModules :: Names
              _hdOimportedModules :: Names
              _tlOimportedModules :: Names
              _hdIimportedModules :: Names
              _hdIself :: ImportDeclaration
              _tlIimportedModules :: Names
              _tlIself :: ImportDeclarations
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOimportedModules =
                  _tlIimportedModules
              _hdOimportedModules =
                  _lhsIimportedModules
              _tlOimportedModules =
                  _hdIimportedModules
              ( _hdIimportedModules,_hdIself) =
                  (hd_ _hdOimportedModules )
              ( _tlIimportedModules,_tlIself) =
                  (tl_ _tlOimportedModules )
          in  ( _lhsOimportedModules,_lhsOself)))
sem_ImportDeclarations_Nil :: T_ImportDeclarations
sem_ImportDeclarations_Nil  =
    (\ _lhsIimportedModules ->
         (let _lhsOself :: ImportDeclarations
              _lhsOimportedModules :: Names
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOimportedModules =
                  _lhsIimportedModules
          in  ( _lhsOimportedModules,_lhsOself)))
-- ImportSpecification -----------------------------------------
-- cata
sem_ImportSpecification :: ImportSpecification ->
                           T_ImportSpecification
sem_ImportSpecification (ImportSpecification_Import _range _hiding _imports )  =
    (sem_ImportSpecification_Import (sem_Range _range ) _hiding (sem_Imports _imports ) )
-- semantic domain
type T_ImportSpecification = ( ImportSpecification)
sem_ImportSpecification_Import :: T_Range ->
                                  Bool ->
                                  T_Imports ->
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
sem_Imports :: Imports ->
               T_Imports
sem_Imports list  =
    (Prelude.foldr sem_Imports_Cons sem_Imports_Nil (Prelude.map sem_Import list) )
-- semantic domain
type T_Imports = ( Imports)
sem_Imports_Cons :: T_Import ->
                    T_Imports ->
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
sem_LeftHandSide :: LeftHandSide ->
                    T_LeftHandSide
sem_LeftHandSide (LeftHandSide_Function _range _name _patterns )  =
    (sem_LeftHandSide_Function (sem_Range _range ) (sem_Name _name ) (sem_Patterns _patterns ) )
sem_LeftHandSide (LeftHandSide_Infix _range _leftPattern _operator _rightPattern )  =
    (sem_LeftHandSide_Infix (sem_Range _range ) (sem_Pattern _leftPattern ) (sem_Name _operator ) (sem_Pattern _rightPattern ) )
sem_LeftHandSide (LeftHandSide_Parenthesized _range _lefthandside _patterns )  =
    (sem_LeftHandSide_Parenthesized (sem_Range _range ) (sem_LeftHandSide _lefthandside ) (sem_Patterns _patterns ) )
-- semantic domain
type T_LeftHandSide = Names ->
                      Names ->
                      ([(ScopeInfo, Entity)]) ->
                      ([Error]) ->
                      Names ->
                      (M.Map Name Int) ->
                      (M.Map Name TpScheme) ->
                      ([Warning]) ->
                      ( ([(ScopeInfo, Entity)]),([Error]),Name,Int,Names,LeftHandSide,Names,([Warning]))
sem_LeftHandSide_Function :: T_Range ->
                             T_Name ->
                             T_Patterns ->
                             T_LeftHandSide
sem_LeftHandSide_Function range_ name_ patterns_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOname :: Name
              _patternsOlhsPattern :: Bool
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: LeftHandSide
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOnumberOfPatterns :: Int
              _lhsOwarnings :: ([Warning])
              _patternsOallTypeConstructors :: Names
              _patternsOallValueConstructors :: Names
              _patternsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsOmiscerrors :: ([Error])
              _patternsOnamesInScope :: Names
              _patternsOtypeConstructors :: (M.Map Name Int)
              _patternsOvalueConstructors :: (M.Map Name TpScheme)
              _patternsOwarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _patternsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsImiscerrors :: ([Error])
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _patternsIwarnings :: ([Warning])
              _lhsOname =
                  _nameIself
              _patternsOlhsPattern =
                  False
              _lhsOpatVarNames =
                  _patternsIpatVarNames
              _lhsOunboundNames =
                  _patternsIunboundNames
              _self =
                  LeftHandSide_Function _rangeIself _nameIself _patternsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _patternsIcollectScopeInfos
              _lhsOmiscerrors =
                  _patternsImiscerrors
              _lhsOnumberOfPatterns =
                  _patternsInumberOfPatterns
              _lhsOwarnings =
                  _patternsIwarnings
              _patternsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternsOallValueConstructors =
                  _lhsIallValueConstructors
              _patternsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternsOmiscerrors =
                  _lhsImiscerrors
              _patternsOnamesInScope =
                  _lhsInamesInScope
              _patternsOtypeConstructors =
                  _lhsItypeConstructors
              _patternsOvalueConstructors =
                  _lhsIvalueConstructors
              _patternsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternsIcollectScopeInfos,_patternsImiscerrors,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIself,_patternsIunboundNames,_patternsIwarnings) =
                  (patterns_ _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOname,_lhsOnumberOfPatterns,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_LeftHandSide_Infix :: T_Range ->
                          T_Pattern ->
                          T_Name ->
                          T_Pattern ->
                          T_LeftHandSide
sem_LeftHandSide_Infix range_ leftPattern_ operator_ rightPattern_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOname :: Name
              _lhsOnumberOfPatterns :: Int
              _leftPatternOlhsPattern :: Bool
              _rightPatternOlhsPattern :: Bool
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: LeftHandSide
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _leftPatternOallTypeConstructors :: Names
              _leftPatternOallValueConstructors :: Names
              _leftPatternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _leftPatternOmiscerrors :: ([Error])
              _leftPatternOnamesInScope :: Names
              _leftPatternOtypeConstructors :: (M.Map Name Int)
              _leftPatternOvalueConstructors :: (M.Map Name TpScheme)
              _leftPatternOwarnings :: ([Warning])
              _rightPatternOallTypeConstructors :: Names
              _rightPatternOallValueConstructors :: Names
              _rightPatternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _rightPatternOmiscerrors :: ([Error])
              _rightPatternOnamesInScope :: Names
              _rightPatternOtypeConstructors :: (M.Map Name Int)
              _rightPatternOvalueConstructors :: (M.Map Name TpScheme)
              _rightPatternOwarnings :: ([Warning])
              _rangeIself :: Range
              _leftPatternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _leftPatternImiscerrors :: ([Error])
              _leftPatternIpatVarNames :: Names
              _leftPatternIself :: Pattern
              _leftPatternIunboundNames :: Names
              _leftPatternIwarnings :: ([Warning])
              _operatorIself :: Name
              _rightPatternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _rightPatternImiscerrors :: ([Error])
              _rightPatternIpatVarNames :: Names
              _rightPatternIself :: Pattern
              _rightPatternIunboundNames :: Names
              _rightPatternIwarnings :: ([Warning])
              _lhsOname =
                  _operatorIself
              _lhsOnumberOfPatterns =
                  2
              _leftPatternOlhsPattern =
                  False
              _rightPatternOlhsPattern =
                  False
              _lhsOpatVarNames =
                  _leftPatternIpatVarNames ++ _rightPatternIpatVarNames
              _lhsOunboundNames =
                  _leftPatternIunboundNames ++ _rightPatternIunboundNames
              _self =
                  LeftHandSide_Infix _rangeIself _leftPatternIself _operatorIself _rightPatternIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _rightPatternIcollectScopeInfos
              _lhsOmiscerrors =
                  _rightPatternImiscerrors
              _lhsOwarnings =
                  _rightPatternIwarnings
              _leftPatternOallTypeConstructors =
                  _lhsIallTypeConstructors
              _leftPatternOallValueConstructors =
                  _lhsIallValueConstructors
              _leftPatternOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _leftPatternOmiscerrors =
                  _lhsImiscerrors
              _leftPatternOnamesInScope =
                  _lhsInamesInScope
              _leftPatternOtypeConstructors =
                  _lhsItypeConstructors
              _leftPatternOvalueConstructors =
                  _lhsIvalueConstructors
              _leftPatternOwarnings =
                  _lhsIwarnings
              _rightPatternOallTypeConstructors =
                  _lhsIallTypeConstructors
              _rightPatternOallValueConstructors =
                  _lhsIallValueConstructors
              _rightPatternOcollectScopeInfos =
                  _leftPatternIcollectScopeInfos
              _rightPatternOmiscerrors =
                  _leftPatternImiscerrors
              _rightPatternOnamesInScope =
                  _lhsInamesInScope
              _rightPatternOtypeConstructors =
                  _lhsItypeConstructors
              _rightPatternOvalueConstructors =
                  _lhsIvalueConstructors
              _rightPatternOwarnings =
                  _leftPatternIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _leftPatternIcollectScopeInfos,_leftPatternImiscerrors,_leftPatternIpatVarNames,_leftPatternIself,_leftPatternIunboundNames,_leftPatternIwarnings) =
                  (leftPattern_ _leftPatternOallTypeConstructors _leftPatternOallValueConstructors _leftPatternOcollectScopeInfos _leftPatternOlhsPattern _leftPatternOmiscerrors _leftPatternOnamesInScope _leftPatternOtypeConstructors _leftPatternOvalueConstructors _leftPatternOwarnings )
              ( _operatorIself) =
                  (operator_ )
              ( _rightPatternIcollectScopeInfos,_rightPatternImiscerrors,_rightPatternIpatVarNames,_rightPatternIself,_rightPatternIunboundNames,_rightPatternIwarnings) =
                  (rightPattern_ _rightPatternOallTypeConstructors _rightPatternOallValueConstructors _rightPatternOcollectScopeInfos _rightPatternOlhsPattern _rightPatternOmiscerrors _rightPatternOnamesInScope _rightPatternOtypeConstructors _rightPatternOvalueConstructors _rightPatternOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOname,_lhsOnumberOfPatterns,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_LeftHandSide_Parenthesized :: T_Range ->
                                  T_LeftHandSide ->
                                  T_Patterns ->
                                  T_LeftHandSide
sem_LeftHandSide_Parenthesized range_ lefthandside_ patterns_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOnumberOfPatterns :: Int
              _patternsOlhsPattern :: Bool
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: LeftHandSide
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOname :: Name
              _lhsOwarnings :: ([Warning])
              _lefthandsideOallTypeConstructors :: Names
              _lefthandsideOallValueConstructors :: Names
              _lefthandsideOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lefthandsideOmiscerrors :: ([Error])
              _lefthandsideOnamesInScope :: Names
              _lefthandsideOtypeConstructors :: (M.Map Name Int)
              _lefthandsideOvalueConstructors :: (M.Map Name TpScheme)
              _lefthandsideOwarnings :: ([Warning])
              _patternsOallTypeConstructors :: Names
              _patternsOallValueConstructors :: Names
              _patternsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsOmiscerrors :: ([Error])
              _patternsOnamesInScope :: Names
              _patternsOtypeConstructors :: (M.Map Name Int)
              _patternsOvalueConstructors :: (M.Map Name TpScheme)
              _patternsOwarnings :: ([Warning])
              _rangeIself :: Range
              _lefthandsideIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lefthandsideImiscerrors :: ([Error])
              _lefthandsideIname :: Name
              _lefthandsideInumberOfPatterns :: Int
              _lefthandsideIpatVarNames :: Names
              _lefthandsideIself :: LeftHandSide
              _lefthandsideIunboundNames :: Names
              _lefthandsideIwarnings :: ([Warning])
              _patternsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsImiscerrors :: ([Error])
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _patternsIwarnings :: ([Warning])
              _lhsOnumberOfPatterns =
                  _lefthandsideInumberOfPatterns + _patternsInumberOfPatterns
              _patternsOlhsPattern =
                  False
              _lhsOpatVarNames =
                  _lefthandsideIpatVarNames ++ _patternsIpatVarNames
              _lhsOunboundNames =
                  _lefthandsideIunboundNames ++ _patternsIunboundNames
              _self =
                  LeftHandSide_Parenthesized _rangeIself _lefthandsideIself _patternsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _patternsIcollectScopeInfos
              _lhsOmiscerrors =
                  _patternsImiscerrors
              _lhsOname =
                  _lefthandsideIname
              _lhsOwarnings =
                  _patternsIwarnings
              _lefthandsideOallTypeConstructors =
                  _lhsIallTypeConstructors
              _lefthandsideOallValueConstructors =
                  _lhsIallValueConstructors
              _lefthandsideOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lefthandsideOmiscerrors =
                  _lhsImiscerrors
              _lefthandsideOnamesInScope =
                  _lhsInamesInScope
              _lefthandsideOtypeConstructors =
                  _lhsItypeConstructors
              _lefthandsideOvalueConstructors =
                  _lhsIvalueConstructors
              _lefthandsideOwarnings =
                  _lhsIwarnings
              _patternsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternsOallValueConstructors =
                  _lhsIallValueConstructors
              _patternsOcollectScopeInfos =
                  _lefthandsideIcollectScopeInfos
              _patternsOmiscerrors =
                  _lefthandsideImiscerrors
              _patternsOnamesInScope =
                  _lhsInamesInScope
              _patternsOtypeConstructors =
                  _lhsItypeConstructors
              _patternsOvalueConstructors =
                  _lhsIvalueConstructors
              _patternsOwarnings =
                  _lefthandsideIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _lefthandsideIcollectScopeInfos,_lefthandsideImiscerrors,_lefthandsideIname,_lefthandsideInumberOfPatterns,_lefthandsideIpatVarNames,_lefthandsideIself,_lefthandsideIunboundNames,_lefthandsideIwarnings) =
                  (lefthandside_ _lefthandsideOallTypeConstructors _lefthandsideOallValueConstructors _lefthandsideOcollectScopeInfos _lefthandsideOmiscerrors _lefthandsideOnamesInScope _lefthandsideOtypeConstructors _lefthandsideOvalueConstructors _lefthandsideOwarnings )
              ( _patternsIcollectScopeInfos,_patternsImiscerrors,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIself,_patternsIunboundNames,_patternsIwarnings) =
                  (patterns_ _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOname,_lhsOnumberOfPatterns,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- Literal -----------------------------------------------------
-- cata
sem_Literal :: Literal ->
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
type T_Literal = ([(ScopeInfo, Entity)]) ->
                 ([Error]) ->
                 ( ([(ScopeInfo, Entity)]),([Error]),Literal)
sem_Literal_Char :: T_Range ->
                    String ->
                    T_Literal
sem_Literal_Char range_ value_  =
    (\ _lhsIcollectScopeInfos
       _lhsImiscerrors ->
         (let _lhsOself :: Literal
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _rangeIself :: Range
              _self =
                  Literal_Char _rangeIself value_
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOmiscerrors =
                  _lhsImiscerrors
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOself)))
sem_Literal_Float :: T_Range ->
                     String ->
                     T_Literal
sem_Literal_Float range_ value_  =
    (\ _lhsIcollectScopeInfos
       _lhsImiscerrors ->
         (let _lhsOself :: Literal
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _rangeIself :: Range
              _self =
                  Literal_Float _rangeIself value_
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOmiscerrors =
                  _lhsImiscerrors
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOself)))
sem_Literal_Int :: T_Range ->
                   String ->
                   T_Literal
sem_Literal_Int range_ value_  =
    (\ _lhsIcollectScopeInfos
       _lhsImiscerrors ->
         (let _lhsOmiscerrors :: ([Error])
              _lhsOself :: Literal
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _rangeIself :: Range
              _intLiteralTooBigErrors =
                  let val = read value_ :: Integer in
                  if length value_ > 9 && (val > maxInt || val < minInt)  then
                     [ IntLiteralTooBig _rangeIself value_ ]
                  else
                     []
              _lhsOmiscerrors =
                  _intLiteralTooBigErrors ++ _lhsImiscerrors
              _self =
                  Literal_Int _rangeIself value_
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOself)))
sem_Literal_String :: T_Range ->
                      String ->
                      T_Literal
sem_Literal_String range_ value_  =
    (\ _lhsIcollectScopeInfos
       _lhsImiscerrors ->
         (let _lhsOself :: Literal
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _rangeIself :: Range
              _self =
                  Literal_String _rangeIself value_
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOmiscerrors =
                  _lhsImiscerrors
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOself)))
-- MaybeDeclarations -------------------------------------------
-- cata
sem_MaybeDeclarations :: MaybeDeclarations ->
                         T_MaybeDeclarations
sem_MaybeDeclarations (MaybeDeclarations_Just _declarations )  =
    (sem_MaybeDeclarations_Just (sem_Declarations _declarations ) )
sem_MaybeDeclarations (MaybeDeclarations_Nothing )  =
    (sem_MaybeDeclarations_Nothing )
-- semantic domain
type T_MaybeDeclarations = Names ->
                           Names ->
                           ClassEnvironment ->
                           ([(ScopeInfo, Entity)]) ->
                           ([Error]) ->
                           ([Error]) ->
                           Names ->
                           ([Option]) ->
                           OrderedTypeSynonyms ->
                           (M.Map Name Int) ->
                           Names ->
                           (M.Map Name TpScheme) ->
                           ([Warning]) ->
                           ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),Names,MaybeDeclarations,Names,([Warning]))
sem_MaybeDeclarations_Just :: T_Declarations ->
                              T_MaybeDeclarations
sem_MaybeDeclarations_Just declarations_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _declarationsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOunboundNames :: Names
              _lhsOwarnings :: ([Warning])
              _declarationsOpreviousWasAlsoFB :: (Maybe Name)
              _declarationsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOmiscerrors :: ([Error])
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: MaybeDeclarations
              _lhsOkindErrors :: ([Error])
              _lhsOnamesInScope :: Names
              _declarationsOallTypeConstructors :: Names
              _declarationsOallValueConstructors :: Names
              _declarationsOclassEnvironment :: ClassEnvironment
              _declarationsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _declarationsOcollectTypeConstructors :: ([(Name,Int)])
              _declarationsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _declarationsOcollectValueConstructors :: ([(Name,TpScheme)])
              _declarationsOkindErrors :: ([Error])
              _declarationsOmiscerrors :: ([Error])
              _declarationsOnamesInScope :: Names
              _declarationsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _declarationsOoptions :: ([Option])
              _declarationsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _declarationsOtypeConstructors :: (M.Map Name Int)
              _declarationsOvalueConstructors :: (M.Map Name TpScheme)
              _declarationsOwarnings :: ([Warning])
              _declarationsIcollectInstances :: ([(Name, Instance)])
              _declarationsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _declarationsIcollectTypeConstructors :: ([(Name,Int)])
              _declarationsIcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _declarationsIcollectValueConstructors :: ([(Name,TpScheme)])
              _declarationsIdeclVarNames :: Names
              _declarationsIkindErrors :: ([Error])
              _declarationsImiscerrors :: ([Error])
              _declarationsIoperatorFixities :: ([(Name,(Int,Assoc))])
              _declarationsIpreviousWasAlsoFB :: (Maybe Name)
              _declarationsIrestrictedNames :: Names
              _declarationsIself :: Declarations
              _declarationsIsuspiciousFBs :: ([(Name,Name)])
              _declarationsItypeSignatures :: ([(Name,TpScheme)])
              _declarationsIunboundNames :: Names
              _declarationsIwarnings :: ([Warning])
              _declarationsOtypeSignatures =
                  []
              __tup14 =
                  changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup14
              (_,_unboundNames,_) =
                  __tup14
              (_,_,_scopeInfo) =
                  __tup14
              _lhsOunboundNames =
                  _unboundNames
              _lhsOwarnings =
                  _declarationsIwarnings ++
                  _suspiciousErrors
              _declarationsOpreviousWasAlsoFB =
                  Nothing
              _declarationsOsuspiciousFBs =
                  []
              _suspiciousErrors =
                  findSimilarFunctionBindings _declarationsItypeSignatures _declarationsIsuspiciousFBs
              _lhsOmiscerrors =
                  _typeSignatureErrors ++ _declarationsImiscerrors
              __tup15 =
                  uniqueAppearance (map fst _declarationsItypeSignatures)
              (_,_doubles) =
                  __tup15
              _typeSignatureErrors =
                  checkTypeSignatures _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
              __tup16 =
                  internalError "PartialSyntax.ag" "n/a" "toplevel MaybeDeclaration"
              (_collectTypeConstructors,_,_,_,_,_) =
                  __tup16
              (_,_collectValueConstructors,_,_,_,_) =
                  __tup16
              (_,_,_collectTypeSynonyms,_,_,_) =
                  __tup16
              (_,_,_,_collectConstructorEnv,_,_) =
                  __tup16
              (_,_,_,_,_derivedFunctions,_) =
                  __tup16
              (_,_,_,_,_,_operatorFixities) =
                  __tup16
              _lhsOcollectScopeInfos =
                  (_scopeInfo, Definition) : _declarationsIcollectScopeInfos
              _lhsOcollectInstances =
                  _declarationsIcollectInstances
              _self =
                  MaybeDeclarations_Just _declarationsIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _declarationsIkindErrors
              _lhsOnamesInScope =
                  _namesInScope
              _declarationsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _declarationsOallValueConstructors =
                  _lhsIallValueConstructors
              _declarationsOclassEnvironment =
                  _lhsIclassEnvironment
              _declarationsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _declarationsOcollectTypeConstructors =
                  _collectTypeConstructors
              _declarationsOcollectTypeSynonyms =
                  _collectTypeSynonyms
              _declarationsOcollectValueConstructors =
                  _collectValueConstructors
              _declarationsOkindErrors =
                  _lhsIkindErrors
              _declarationsOmiscerrors =
                  _lhsImiscerrors
              _declarationsOnamesInScope =
                  _namesInScope
              _declarationsOoperatorFixities =
                  _operatorFixities
              _declarationsOoptions =
                  _lhsIoptions
              _declarationsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _declarationsOtypeConstructors =
                  _lhsItypeConstructors
              _declarationsOvalueConstructors =
                  _lhsIvalueConstructors
              _declarationsOwarnings =
                  _lhsIwarnings
              ( _declarationsIcollectInstances,_declarationsIcollectScopeInfos,_declarationsIcollectTypeConstructors,_declarationsIcollectTypeSynonyms,_declarationsIcollectValueConstructors,_declarationsIdeclVarNames,_declarationsIkindErrors,_declarationsImiscerrors,_declarationsIoperatorFixities,_declarationsIpreviousWasAlsoFB,_declarationsIrestrictedNames,_declarationsIself,_declarationsIsuspiciousFBs,_declarationsItypeSignatures,_declarationsIunboundNames,_declarationsIwarnings) =
                  (declarations_ _declarationsOallTypeConstructors _declarationsOallValueConstructors _declarationsOclassEnvironment _declarationsOcollectScopeInfos _declarationsOcollectTypeConstructors _declarationsOcollectTypeSynonyms _declarationsOcollectValueConstructors _declarationsOkindErrors _declarationsOmiscerrors _declarationsOnamesInScope _declarationsOoperatorFixities _declarationsOoptions _declarationsOorderedTypeSynonyms _declarationsOpreviousWasAlsoFB _declarationsOsuspiciousFBs _declarationsOtypeConstructors _declarationsOtypeSignatures _declarationsOvalueConstructors _declarationsOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_MaybeDeclarations_Nothing :: T_MaybeDeclarations
sem_MaybeDeclarations_Nothing  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: MaybeDeclarations
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOnamesInScope :: Names
              _lhsOunboundNames :: Names
              _lhsOwarnings :: ([Warning])
              _lhsOcollectInstances =
                  []
              _self =
                  MaybeDeclarations_Nothing
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOunboundNames =
                  _lhsIunboundNames
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- MaybeExports ------------------------------------------------
-- cata
sem_MaybeExports :: MaybeExports ->
                    T_MaybeExports
sem_MaybeExports (MaybeExports_Just _exports )  =
    (sem_MaybeExports_Just (sem_Exports _exports ) )
sem_MaybeExports (MaybeExports_Nothing )  =
    (sem_MaybeExports_Nothing )
-- semantic domain
type T_MaybeExports = Names ->
                      Names ->
                      Names ->
                      Names ->
                      ( ([Error]),MaybeExports)
sem_MaybeExports_Just :: T_Exports ->
                         T_MaybeExports
sem_MaybeExports_Just exports_  =
    (\ _lhsIconsInScope
       _lhsImodulesInScope
       _lhsInamesInScop
       _lhsItyconsInScope ->
         (let _lhsOexportErrors :: ([Error])
              _lhsOself :: MaybeExports
              _exportsOconsInScope :: Names
              _exportsOmodulesInScope :: Names
              _exportsOnamesInScop :: Names
              _exportsOtyconsInScope :: Names
              _exportsIexportErrors :: ([Error])
              _exportsIself :: Exports
              _lhsOexportErrors =
                  _exportsIexportErrors
              _self =
                  MaybeExports_Just _exportsIself
              _lhsOself =
                  _self
              _exportsOconsInScope =
                  _lhsIconsInScope
              _exportsOmodulesInScope =
                  _lhsImodulesInScope
              _exportsOnamesInScop =
                  _lhsInamesInScop
              _exportsOtyconsInScope =
                  _lhsItyconsInScope
              ( _exportsIexportErrors,_exportsIself) =
                  (exports_ _exportsOconsInScope _exportsOmodulesInScope _exportsOnamesInScop _exportsOtyconsInScope )
          in  ( _lhsOexportErrors,_lhsOself)))
sem_MaybeExports_Nothing :: T_MaybeExports
sem_MaybeExports_Nothing  =
    (\ _lhsIconsInScope
       _lhsImodulesInScope
       _lhsInamesInScop
       _lhsItyconsInScope ->
         (let _lhsOexportErrors :: ([Error])
              _lhsOself :: MaybeExports
              _lhsOexportErrors =
                  []
              _self =
                  MaybeExports_Nothing
              _lhsOself =
                  _self
          in  ( _lhsOexportErrors,_lhsOself)))
-- MaybeExpression ---------------------------------------------
-- cata
sem_MaybeExpression :: MaybeExpression ->
                       T_MaybeExpression
sem_MaybeExpression (MaybeExpression_Just _expression )  =
    (sem_MaybeExpression_Just (sem_Expression _expression ) )
sem_MaybeExpression (MaybeExpression_Nothing )  =
    (sem_MaybeExpression_Nothing )
-- semantic domain
type T_MaybeExpression = Names ->
                         Names ->
                         ClassEnvironment ->
                         ([(ScopeInfo, Entity)]) ->
                         ([Error]) ->
                         ([Error]) ->
                         Names ->
                         ([Option]) ->
                         OrderedTypeSynonyms ->
                         (M.Map Name Int) ->
                         (M.Map Name TpScheme) ->
                         ([Warning]) ->
                         ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),MaybeExpression,Names,([Warning]))
sem_MaybeExpression_Just :: T_Expression ->
                            T_MaybeExpression
sem_MaybeExpression_Just expression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: MaybeExpression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  MaybeExpression_Just _expressionIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _lhsOkindErrors =
                  _expressionIkindErrors
              _lhsOmiscerrors =
                  _expressionImiscerrors
              _lhsOwarnings =
                  _expressionIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _lhsImiscerrors
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _lhsIwarnings
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_MaybeExpression_Nothing :: T_MaybeExpression
sem_MaybeExpression_Nothing  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: MaybeExpression
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  MaybeExpression_Nothing
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- MaybeImportSpecification ------------------------------------
-- cata
sem_MaybeImportSpecification :: MaybeImportSpecification ->
                                T_MaybeImportSpecification
sem_MaybeImportSpecification (MaybeImportSpecification_Just _importspecification )  =
    (sem_MaybeImportSpecification_Just (sem_ImportSpecification _importspecification ) )
sem_MaybeImportSpecification (MaybeImportSpecification_Nothing )  =
    (sem_MaybeImportSpecification_Nothing )
-- semantic domain
type T_MaybeImportSpecification = ( MaybeImportSpecification)
sem_MaybeImportSpecification_Just :: T_ImportSpecification ->
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
sem_MaybeInt :: MaybeInt ->
                T_MaybeInt
sem_MaybeInt (MaybeInt_Just _int )  =
    (sem_MaybeInt_Just _int )
sem_MaybeInt (MaybeInt_Nothing )  =
    (sem_MaybeInt_Nothing )
-- semantic domain
type T_MaybeInt = ( MaybeInt)
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
sem_MaybeName :: MaybeName ->
                 T_MaybeName
sem_MaybeName (MaybeName_Just _name )  =
    (sem_MaybeName_Just (sem_Name _name ) )
sem_MaybeName (MaybeName_Nothing )  =
    (sem_MaybeName_Nothing )
-- semantic domain
type T_MaybeName = ( MaybeName)
sem_MaybeName_Just :: T_Name ->
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
sem_MaybeNames :: MaybeNames ->
                  T_MaybeNames
sem_MaybeNames (MaybeNames_Just _names )  =
    (sem_MaybeNames_Just (sem_Names _names ) )
sem_MaybeNames (MaybeNames_Nothing )  =
    (sem_MaybeNames_Nothing )
-- semantic domain
type T_MaybeNames = ( MaybeNames)
sem_MaybeNames_Just :: T_Names ->
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
sem_Module :: Module ->
              T_Module
sem_Module (Module_Module _range _name _exports _body )  =
    (sem_Module_Module (sem_Range _range ) (sem_MaybeName _name ) (sem_MaybeExports _exports ) (sem_Body _body ) )
-- semantic domain
type T_Module = String ->
                ImportEnvironments ->
                ([Option]) ->
                ( ImportEnvironment,Errors,Module,([(Name,TpScheme)]),Warnings)
sem_Module_Module :: T_Range ->
                     T_MaybeName ->
                     T_MaybeExports ->
                     T_Body ->
                     T_Module
sem_Module_Module range_ name_ exports_ body_  =
    (\ _lhsIbaseName
       _lhsIimportEnvironments
       _lhsIoptions ->
         (let _lhsOerrors :: Errors
              _lhsOwarnings :: Warnings
              _bodyOcollectTypeConstructors :: ([(Name,Int)])
              _bodyOcollectValueConstructors :: ([(Name,TpScheme)])
              _bodyOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _bodyOoperatorFixities :: ([(Name,(Int,Assoc))])
              _bodyOorderedTypeSynonyms :: OrderedTypeSynonyms
              _bodyOclassEnvironment :: ClassEnvironment
              _bodyOkindErrors :: ([Error])
              _bodyOwarnings :: ([Warning])
              _bodyOmiscerrors :: ([Error])
              _exportsOnamesInScop :: Names
              _exportsOmodulesInScope :: Names
              _exportsOtyconsInScope :: Names
              _exportsOconsInScope :: Names
              _bodyOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOself :: Module
              _lhsOcollectEnvironment :: ImportEnvironment
              _lhsOtypeSignatures :: ([(Name,TpScheme)])
              _bodyOallTypeConstructors :: Names
              _bodyOallValueConstructors :: Names
              _bodyOnamesInScope :: Names
              _bodyOoptions :: ([Option])
              _bodyOtypeConstructors :: (M.Map Name Int)
              _bodyOvalueConstructors :: (M.Map Name TpScheme)
              _rangeIself :: Range
              _nameIself :: MaybeName
              _exportsIexportErrors :: ([Error])
              _exportsIself :: MaybeExports
              _bodyIcollectInstances :: ([(Name, Instance)])
              _bodyIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _bodyIcollectTypeConstructors :: ([(Name,Int)])
              _bodyIcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _bodyIcollectValueConstructors :: ([(Name,TpScheme)])
              _bodyIdeclVarNames :: Names
              _bodyIimportedModules :: Names
              _bodyIkindErrors :: ([Error])
              _bodyImiscerrors :: ([Error])
              _bodyIoperatorFixities :: ([(Name,(Int,Assoc))])
              _bodyIself :: Body
              _bodyItypeSignatures :: ([(Name,TpScheme)])
              _bodyIunboundNames :: Names
              _bodyIwarnings :: ([Warning])
              _lhsOerrors =
                  filter (\err -> filterRemovedNames _removedEntities err
                               && filterDerivedNames _derivedRanges err) _allErrors
              _lhsOwarnings =
                  _scopeWarnings ++ _warnings
              _allErrors =
                  concat [ _exportErrors
                         , _scopeErrors
                         , _miscerrors
                         , if KindInferencing `elem` _lhsIoptions then [] else _kindErrors
                         , _topLevelErrors
                         ]
              _removedEntities =
                  [ (name,TypeConstructor) | name:_ <- _duplicatedTypeConstructors  ] ++
                  [ (name,Constructor    ) | name:_ <- _duplicatedValueConstructors ]
              _derivedRanges =
                  map getNameRange (map fst _derivedFunctions)
              _initialScope =
                  map fst _derivedFunctions ++
                  concatMap (M.keys . typeEnvironment) _lhsIimportEnvironments
              _collectEnvironment =
                  setValueConstructors   (M.fromList _bodyIcollectValueConstructors)
                  . setTypeConstructors  (M.fromList _bodyIcollectTypeConstructors)
                  . setTypeSynonyms      (M.fromList _bodyIcollectTypeSynonyms)
                  . setOperatorTable     (M.fromList _bodyIoperatorFixities)
                  . addToTypeEnvironment (M.fromList _derivedFunctions)
                  $ emptyEnvironment
              _derivedFunctions =
                  let f (n,i) = ( nameOfShowFunction n
                                , typeOfShowFunction n (take i [ nameFromString s | s <- variableList])
                                )
                      g (n,(i,_)) = f (n,i)
                  in map f _bodyIcollectTypeConstructors ++
                     map g _bodyIcollectTypeSynonyms
              _bodyOcollectTypeConstructors =
                  []
              _bodyOcollectValueConstructors =
                  []
              _bodyOcollectTypeSynonyms =
                  []
              _bodyOoperatorFixities =
                  []
              __tup17 =
                  uniqueKeys (  _bodyIcollectValueConstructors
                             ++ concatMap (M.assocs . valueConstructors) _lhsIimportEnvironments
                             )
              (_uniqueValueConstructors,_) =
                  __tup17
              (_,_duplicatedValueConstructors) =
                  __tup17
              _allValueConstructors =
                  map fst _uniqueValueConstructors ++ map head _duplicatedValueConstructors
              _valueConstructors =
                  M.fromList _uniqueValueConstructors
              __tup18 =
                  uniqueKeys (  _bodyIcollectTypeConstructors
                             ++ concatMap (M.assocs . typeConstructors) _lhsIimportEnvironments
                             ++ [ (n,i) | (n,(i,_)) <- _bodyIcollectTypeSynonyms ]
                             )
              (_uniqueTypeConstructors,_) =
                  __tup18
              (_,_duplicatedTypeConstructors) =
                  __tup18
              _allTypeConstructors =
                  map fst _uniqueTypeConstructors ++ map head _duplicatedTypeConstructors
              _typeConstructors =
                  M.fromList _uniqueTypeConstructors
              _bodyOorderedTypeSynonyms =
                  let list     = concatMap (M.assocs . typeSynonyms) _lhsIimportEnvironments ++
                                 _bodyIcollectTypeSynonyms
                      newmap   = M.fromList [ (show name, t) | (name, t) <- list ]
                      ordering = fst (getTypeSynonymOrdering newmap)
                  in (ordering, newmap)
              _bodyOclassEnvironment =
                  let importEnv = foldr combineImportEnvironments emptyEnvironment _lhsIimportEnvironments
                  in foldr (\(n, i) -> insertInstance (show n) i)
                           (createClassEnvironment importEnv)
                           _bodyIcollectInstances
              __tup19 =
                  changeOfScope (_initialScope ++ _bodyIdeclVarNames) _bodyIunboundNames []
              (_namesInScope,_,_) =
                  __tup19
              (_,_unboundNames,_) =
                  __tup19
              (_,_,_scopeInfo) =
                  __tup19
              _bodyOkindErrors =
                  []
              _kindErrors =
                  _bodyIkindErrors
              _bodyOwarnings =
                  []
              _warnings =
                  _bodyIwarnings
              _topLevelErrors =
                  concat [ _typeConstructorErrors
                         , _valueConstructorErrors
                         , _fixityErrors
                         , _fixityButNoFunDefErrors
                         , _wrongFlagErrors
                         , _recursiveTypeSynonymErrors
                         , _wrongFileNameErrors
                         ]
              _typeConstructorErrors =
                  makeDuplicated TypeConstructor _duplicatedTypeConstructors
              _valueConstructorErrors =
                  makeDuplicated Constructor _duplicatedValueConstructors
              _fixityErrors =
                  makeDuplicated Fixity _duplicatedFixities
              __tup20 =
                  let (xs,ys) = partition ((>1) . length) . group . sort $ (map fst _bodyIoperatorFixities)
                  in (xs,map head ys)
              (_duplicatedFixities,_) =
                  __tup20
              (_,_correctFixities) =
                  __tup20
              _fixityButNoFunDefErrors =
                  let list = nub (_bodyIdeclVarNames ++ _allValueConstructors)
                  in makeNoFunDef Fixity (filter (`notElem` list) _correctFixities) list
              _wrongFlagErrors =
                  [ WrongOverloadingFlag flag
                  | let flag = Overloading `elem` _lhsIoptions
                        imp  = any isOverloaded (concatMap (M.elems . typeEnvironment) _lhsIimportEnvironments)
                  , flag /= imp
                  ]
              _recursiveTypeSynonymErrors =
                  let converted  = map (\(name, tuple) -> (show name, tuple)) _bodyIcollectTypeSynonyms
                      recursives = snd . getTypeSynonymOrdering . M.fromList $ converted
                      makeError = let f = foldr add (Just [])
                                      add s ml = case (g s, ml) of
                                                    ([n], Just ns) -> Just (n:ns)
                                                    _              -> Nothing
                                      g s = [ n | n <- map fst _bodyIcollectTypeSynonyms, show n == s ]
                                  in maybe [] (\x -> [RecursiveTypeSynonyms x]) . f
                  in concatMap makeError recursives
              _wrongFileNameErrors =
                  let moduleString = getNameName  _moduleName
                      moduleRange  = getNameRange _moduleName
                  in if moduleString == "" || _lhsIbaseName == moduleString
                    then []
                    else [ WrongFileName _lhsIbaseName moduleString moduleRange ]
              _moduleName =
                  case _nameIself of
                     MaybeName_Just name -> name
                     MaybeName_Nothing   -> Name_Identifier noRange [] ""
              _fileName =
                  Name_Identifier noRange [] _lhsIbaseName
              _bodyOmiscerrors =
                  []
              _miscerrors =
                  _bodyImiscerrors
              _exportsOnamesInScop =
                  concat [ _bodyIdeclVarNames
                          , concatMap (M.keys . typeEnvironment) _lhsIimportEnvironments
                          , map fst _derivedFunctions
                          ]
              _exportsOmodulesInScope =
                  (_moduleName : _fileName : _bodyIimportedModules)
              _exportsOtyconsInScope =
                  _allTypeConstructors
              _exportsOconsInScope =
                  _allValueConstructors
              _exportErrors =
                  _exportsIexportErrors
              _bodyOcollectScopeInfos =
                  []
              _scopeErrors =
                  makeErrors   _collectScopeInfos
              _scopeWarnings =
                  makeWarnings _collectScopeInfos
              _collectScopeInfos =
                  (topLevelScopeInfo _scopeInfo, Definition) : _bodyIcollectScopeInfos
              _self =
                  Module_Module _rangeIself _nameIself _exportsIself _bodyIself
              _lhsOself =
                  _self
              _lhsOcollectEnvironment =
                  _collectEnvironment
              _lhsOtypeSignatures =
                  _bodyItypeSignatures
              _bodyOallTypeConstructors =
                  _allTypeConstructors
              _bodyOallValueConstructors =
                  _allValueConstructors
              _bodyOnamesInScope =
                  _namesInScope
              _bodyOoptions =
                  _lhsIoptions
              _bodyOtypeConstructors =
                  _typeConstructors
              _bodyOvalueConstructors =
                  _valueConstructors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _exportsIexportErrors,_exportsIself) =
                  (exports_ _exportsOconsInScope _exportsOmodulesInScope _exportsOnamesInScop _exportsOtyconsInScope )
              ( _bodyIcollectInstances,_bodyIcollectScopeInfos,_bodyIcollectTypeConstructors,_bodyIcollectTypeSynonyms,_bodyIcollectValueConstructors,_bodyIdeclVarNames,_bodyIimportedModules,_bodyIkindErrors,_bodyImiscerrors,_bodyIoperatorFixities,_bodyIself,_bodyItypeSignatures,_bodyIunboundNames,_bodyIwarnings) =
                  (body_ _bodyOallTypeConstructors _bodyOallValueConstructors _bodyOclassEnvironment _bodyOcollectScopeInfos _bodyOcollectTypeConstructors _bodyOcollectTypeSynonyms _bodyOcollectValueConstructors _bodyOkindErrors _bodyOmiscerrors _bodyOnamesInScope _bodyOoperatorFixities _bodyOoptions _bodyOorderedTypeSynonyms _bodyOtypeConstructors _bodyOvalueConstructors _bodyOwarnings )
          in  ( _lhsOcollectEnvironment,_lhsOerrors,_lhsOself,_lhsOtypeSignatures,_lhsOwarnings)))
-- Name --------------------------------------------------------
-- cata
sem_Name :: Name ->
            T_Name
sem_Name (Name_Identifier _range _module _name )  =
    (sem_Name_Identifier (sem_Range _range ) (sem_Strings _module ) _name )
sem_Name (Name_Operator _range _module _name )  =
    (sem_Name_Operator (sem_Range _range ) (sem_Strings _module ) _name )
sem_Name (Name_Special _range _module _name )  =
    (sem_Name_Special (sem_Range _range ) (sem_Strings _module ) _name )
-- semantic domain
type T_Name = ( Name)
sem_Name_Identifier :: T_Range ->
                       T_Strings ->
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
sem_Name_Operator :: T_Range ->
                     T_Strings ->
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
sem_Name_Special :: T_Range ->
                    T_Strings ->
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
sem_Names :: Names ->
             T_Names
sem_Names list  =
    (Prelude.foldr sem_Names_Cons sem_Names_Nil (Prelude.map sem_Name list) )
-- semantic domain
type T_Names = ( Names)
sem_Names_Cons :: T_Name ->
                  T_Names ->
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
sem_Pattern :: Pattern ->
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
type T_Pattern = Names ->
                 Names ->
                 ([(ScopeInfo, Entity)]) ->
                 Bool ->
                 ([Error]) ->
                 Names ->
                 (M.Map Name Int) ->
                 (M.Map Name TpScheme) ->
                 ([Warning]) ->
                 ( ([(ScopeInfo, Entity)]),([Error]),Names,Pattern,Names,([Warning]))
sem_Pattern_As :: T_Range ->
                  T_Name ->
                  T_Pattern ->
                  T_Pattern
sem_Pattern_As range_ name_ pattern_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _patternOallTypeConstructors :: Names
              _patternOallValueConstructors :: Names
              _patternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternOlhsPattern :: Bool
              _patternOmiscerrors :: ([Error])
              _patternOnamesInScope :: Names
              _patternOtypeConstructors :: (M.Map Name Int)
              _patternOvalueConstructors :: (M.Map Name TpScheme)
              _patternOwarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _patternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternImiscerrors :: ([Error])
              _patternIpatVarNames :: Names
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _patternIwarnings :: ([Warning])
              _lhsOpatVarNames =
                  _nameIself : _patternIpatVarNames
              _lhsOunboundNames =
                  _patternIunboundNames
              _self =
                  Pattern_As _rangeIself _nameIself _patternIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _patternIcollectScopeInfos
              _lhsOmiscerrors =
                  _patternImiscerrors
              _lhsOwarnings =
                  _patternIwarnings
              _patternOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternOallValueConstructors =
                  _lhsIallValueConstructors
              _patternOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternOlhsPattern =
                  _lhsIlhsPattern
              _patternOmiscerrors =
                  _lhsImiscerrors
              _patternOnamesInScope =
                  _lhsInamesInScope
              _patternOtypeConstructors =
                  _lhsItypeConstructors
              _patternOvalueConstructors =
                  _lhsIvalueConstructors
              _patternOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternIcollectScopeInfos,_patternImiscerrors,_patternIpatVarNames,_patternIself,_patternIunboundNames,_patternIwarnings) =
                  (pattern_ _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_Constructor :: T_Range ->
                           T_Name ->
                           T_Patterns ->
                           T_Pattern
sem_Pattern_Constructor range_ name_ patterns_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOmiscerrors :: ([Error])
              _patternsOlhsPattern :: Bool
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOwarnings :: ([Warning])
              _patternsOallTypeConstructors :: Names
              _patternsOallValueConstructors :: Names
              _patternsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsOmiscerrors :: ([Error])
              _patternsOnamesInScope :: Names
              _patternsOtypeConstructors :: (M.Map Name Int)
              _patternsOvalueConstructors :: (M.Map Name TpScheme)
              _patternsOwarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _patternsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsImiscerrors :: ([Error])
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _patternsIwarnings :: ([Warning])
              _lhsOmiscerrors =
                  _patConstructorErrors ++ _patternsImiscerrors
              _patConstructorErrors =
                  patternConstructorErrors _maybetp _nameIself _lhsIallValueConstructors _patternsInumberOfPatterns _lhsIlhsPattern _lhsIallTypeConstructors
              _maybetp =
                  M.lookup _nameIself _lhsIvalueConstructors
              _patternsOlhsPattern =
                  False
              _lhsOpatVarNames =
                  _patternsIpatVarNames
              _lhsOunboundNames =
                  _patternsIunboundNames
              _self =
                  Pattern_Constructor _rangeIself _nameIself _patternsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _patternsIcollectScopeInfos
              _lhsOwarnings =
                  _patternsIwarnings
              _patternsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternsOallValueConstructors =
                  _lhsIallValueConstructors
              _patternsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternsOmiscerrors =
                  _lhsImiscerrors
              _patternsOnamesInScope =
                  _lhsInamesInScope
              _patternsOtypeConstructors =
                  _lhsItypeConstructors
              _patternsOvalueConstructors =
                  _lhsIvalueConstructors
              _patternsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternsIcollectScopeInfos,_patternsImiscerrors,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIself,_patternsIunboundNames,_patternsIwarnings) =
                  (patterns_ _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_InfixConstructor :: T_Range ->
                                T_Pattern ->
                                T_Name ->
                                T_Pattern ->
                                T_Pattern
sem_Pattern_InfixConstructor range_ leftPattern_ constructorOperator_ rightPattern_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOmiscerrors :: ([Error])
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOwarnings :: ([Warning])
              _leftPatternOallTypeConstructors :: Names
              _leftPatternOallValueConstructors :: Names
              _leftPatternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _leftPatternOlhsPattern :: Bool
              _leftPatternOmiscerrors :: ([Error])
              _leftPatternOnamesInScope :: Names
              _leftPatternOtypeConstructors :: (M.Map Name Int)
              _leftPatternOvalueConstructors :: (M.Map Name TpScheme)
              _leftPatternOwarnings :: ([Warning])
              _rightPatternOallTypeConstructors :: Names
              _rightPatternOallValueConstructors :: Names
              _rightPatternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _rightPatternOlhsPattern :: Bool
              _rightPatternOmiscerrors :: ([Error])
              _rightPatternOnamesInScope :: Names
              _rightPatternOtypeConstructors :: (M.Map Name Int)
              _rightPatternOvalueConstructors :: (M.Map Name TpScheme)
              _rightPatternOwarnings :: ([Warning])
              _rangeIself :: Range
              _leftPatternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _leftPatternImiscerrors :: ([Error])
              _leftPatternIpatVarNames :: Names
              _leftPatternIself :: Pattern
              _leftPatternIunboundNames :: Names
              _leftPatternIwarnings :: ([Warning])
              _constructorOperatorIself :: Name
              _rightPatternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _rightPatternImiscerrors :: ([Error])
              _rightPatternIpatVarNames :: Names
              _rightPatternIself :: Pattern
              _rightPatternIunboundNames :: Names
              _rightPatternIwarnings :: ([Warning])
              _lhsOmiscerrors =
                  _patConstructorErrors ++ _rightPatternImiscerrors
              _patConstructorErrors =
                  patternConstructorErrors _maybetp _constructorOperatorIself _lhsIallValueConstructors 2 False _lhsIallTypeConstructors
              _maybetp =
                  M.lookup _constructorOperatorIself _lhsIvalueConstructors
              _lhsOpatVarNames =
                  _leftPatternIpatVarNames ++ _rightPatternIpatVarNames
              _lhsOunboundNames =
                  _leftPatternIunboundNames ++ _rightPatternIunboundNames
              _self =
                  Pattern_InfixConstructor _rangeIself _leftPatternIself _constructorOperatorIself _rightPatternIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _rightPatternIcollectScopeInfos
              _lhsOwarnings =
                  _rightPatternIwarnings
              _leftPatternOallTypeConstructors =
                  _lhsIallTypeConstructors
              _leftPatternOallValueConstructors =
                  _lhsIallValueConstructors
              _leftPatternOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _leftPatternOlhsPattern =
                  _lhsIlhsPattern
              _leftPatternOmiscerrors =
                  _lhsImiscerrors
              _leftPatternOnamesInScope =
                  _lhsInamesInScope
              _leftPatternOtypeConstructors =
                  _lhsItypeConstructors
              _leftPatternOvalueConstructors =
                  _lhsIvalueConstructors
              _leftPatternOwarnings =
                  _lhsIwarnings
              _rightPatternOallTypeConstructors =
                  _lhsIallTypeConstructors
              _rightPatternOallValueConstructors =
                  _lhsIallValueConstructors
              _rightPatternOcollectScopeInfos =
                  _leftPatternIcollectScopeInfos
              _rightPatternOlhsPattern =
                  _lhsIlhsPattern
              _rightPatternOmiscerrors =
                  _leftPatternImiscerrors
              _rightPatternOnamesInScope =
                  _lhsInamesInScope
              _rightPatternOtypeConstructors =
                  _lhsItypeConstructors
              _rightPatternOvalueConstructors =
                  _lhsIvalueConstructors
              _rightPatternOwarnings =
                  _leftPatternIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _leftPatternIcollectScopeInfos,_leftPatternImiscerrors,_leftPatternIpatVarNames,_leftPatternIself,_leftPatternIunboundNames,_leftPatternIwarnings) =
                  (leftPattern_ _leftPatternOallTypeConstructors _leftPatternOallValueConstructors _leftPatternOcollectScopeInfos _leftPatternOlhsPattern _leftPatternOmiscerrors _leftPatternOnamesInScope _leftPatternOtypeConstructors _leftPatternOvalueConstructors _leftPatternOwarnings )
              ( _constructorOperatorIself) =
                  (constructorOperator_ )
              ( _rightPatternIcollectScopeInfos,_rightPatternImiscerrors,_rightPatternIpatVarNames,_rightPatternIself,_rightPatternIunboundNames,_rightPatternIwarnings) =
                  (rightPattern_ _rightPatternOallTypeConstructors _rightPatternOallValueConstructors _rightPatternOcollectScopeInfos _rightPatternOlhsPattern _rightPatternOmiscerrors _rightPatternOnamesInScope _rightPatternOtypeConstructors _rightPatternOvalueConstructors _rightPatternOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_Irrefutable :: T_Range ->
                           T_Pattern ->
                           T_Pattern
sem_Pattern_Irrefutable range_ pattern_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _patternOallTypeConstructors :: Names
              _patternOallValueConstructors :: Names
              _patternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternOlhsPattern :: Bool
              _patternOmiscerrors :: ([Error])
              _patternOnamesInScope :: Names
              _patternOtypeConstructors :: (M.Map Name Int)
              _patternOvalueConstructors :: (M.Map Name TpScheme)
              _patternOwarnings :: ([Warning])
              _rangeIself :: Range
              _patternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternImiscerrors :: ([Error])
              _patternIpatVarNames :: Names
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _patternIwarnings :: ([Warning])
              _lhsOpatVarNames =
                  _patternIpatVarNames
              _lhsOunboundNames =
                  _patternIunboundNames
              _self =
                  Pattern_Irrefutable _rangeIself _patternIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _patternIcollectScopeInfos
              _lhsOmiscerrors =
                  _patternImiscerrors
              _lhsOwarnings =
                  _patternIwarnings
              _patternOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternOallValueConstructors =
                  _lhsIallValueConstructors
              _patternOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternOlhsPattern =
                  _lhsIlhsPattern
              _patternOmiscerrors =
                  _lhsImiscerrors
              _patternOnamesInScope =
                  _lhsInamesInScope
              _patternOtypeConstructors =
                  _lhsItypeConstructors
              _patternOvalueConstructors =
                  _lhsIvalueConstructors
              _patternOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternIcollectScopeInfos,_patternImiscerrors,_patternIpatVarNames,_patternIself,_patternIunboundNames,_patternIwarnings) =
                  (pattern_ _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_List :: T_Range ->
                    T_Patterns ->
                    T_Pattern
sem_Pattern_List range_ patterns_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _patternsOallTypeConstructors :: Names
              _patternsOallValueConstructors :: Names
              _patternsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsOlhsPattern :: Bool
              _patternsOmiscerrors :: ([Error])
              _patternsOnamesInScope :: Names
              _patternsOtypeConstructors :: (M.Map Name Int)
              _patternsOvalueConstructors :: (M.Map Name TpScheme)
              _patternsOwarnings :: ([Warning])
              _rangeIself :: Range
              _patternsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsImiscerrors :: ([Error])
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _patternsIwarnings :: ([Warning])
              _lhsOpatVarNames =
                  _patternsIpatVarNames
              _lhsOunboundNames =
                  _patternsIunboundNames
              _self =
                  Pattern_List _rangeIself _patternsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _patternsIcollectScopeInfos
              _lhsOmiscerrors =
                  _patternsImiscerrors
              _lhsOwarnings =
                  _patternsIwarnings
              _patternsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternsOallValueConstructors =
                  _lhsIallValueConstructors
              _patternsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternsOlhsPattern =
                  _lhsIlhsPattern
              _patternsOmiscerrors =
                  _lhsImiscerrors
              _patternsOnamesInScope =
                  _lhsInamesInScope
              _patternsOtypeConstructors =
                  _lhsItypeConstructors
              _patternsOvalueConstructors =
                  _lhsIvalueConstructors
              _patternsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternsIcollectScopeInfos,_patternsImiscerrors,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIself,_patternsIunboundNames,_patternsIwarnings) =
                  (patterns_ _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_Literal :: T_Range ->
                       T_Literal ->
                       T_Pattern
sem_Pattern_Literal range_ literal_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _literalOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _literalOmiscerrors :: ([Error])
              _rangeIself :: Range
              _literalIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _literalImiscerrors :: ([Error])
              _literalIself :: Literal
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_Literal _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _literalIcollectScopeInfos
              _lhsOmiscerrors =
                  _literalImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              _literalOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _literalOmiscerrors =
                  _lhsImiscerrors
              ( _rangeIself) =
                  (range_ )
              ( _literalIcollectScopeInfos,_literalImiscerrors,_literalIself) =
                  (literal_ _literalOcollectScopeInfos _literalOmiscerrors )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_Negate :: T_Range ->
                      T_Literal ->
                      T_Pattern
sem_Pattern_Negate range_ literal_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _literalOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _literalOmiscerrors :: ([Error])
              _rangeIself :: Range
              _literalIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _literalImiscerrors :: ([Error])
              _literalIself :: Literal
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_Negate _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _literalIcollectScopeInfos
              _lhsOmiscerrors =
                  _literalImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              _literalOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _literalOmiscerrors =
                  _lhsImiscerrors
              ( _rangeIself) =
                  (range_ )
              ( _literalIcollectScopeInfos,_literalImiscerrors,_literalIself) =
                  (literal_ _literalOcollectScopeInfos _literalOmiscerrors )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_NegateFloat :: T_Range ->
                           T_Literal ->
                           T_Pattern
sem_Pattern_NegateFloat range_ literal_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _literalOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _literalOmiscerrors :: ([Error])
              _rangeIself :: Range
              _literalIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _literalImiscerrors :: ([Error])
              _literalIself :: Literal
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_NegateFloat _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _literalIcollectScopeInfos
              _lhsOmiscerrors =
                  _literalImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              _literalOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _literalOmiscerrors =
                  _lhsImiscerrors
              ( _rangeIself) =
                  (range_ )
              ( _literalIcollectScopeInfos,_literalImiscerrors,_literalIself) =
                  (literal_ _literalOcollectScopeInfos _literalOmiscerrors )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_Parenthesized :: T_Range ->
                             T_Pattern ->
                             T_Pattern
sem_Pattern_Parenthesized range_ pattern_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _patternOallTypeConstructors :: Names
              _patternOallValueConstructors :: Names
              _patternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternOlhsPattern :: Bool
              _patternOmiscerrors :: ([Error])
              _patternOnamesInScope :: Names
              _patternOtypeConstructors :: (M.Map Name Int)
              _patternOvalueConstructors :: (M.Map Name TpScheme)
              _patternOwarnings :: ([Warning])
              _rangeIself :: Range
              _patternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternImiscerrors :: ([Error])
              _patternIpatVarNames :: Names
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _patternIwarnings :: ([Warning])
              _lhsOpatVarNames =
                  _patternIpatVarNames
              _lhsOunboundNames =
                  _patternIunboundNames
              _self =
                  Pattern_Parenthesized _rangeIself _patternIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _patternIcollectScopeInfos
              _lhsOmiscerrors =
                  _patternImiscerrors
              _lhsOwarnings =
                  _patternIwarnings
              _patternOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternOallValueConstructors =
                  _lhsIallValueConstructors
              _patternOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternOlhsPattern =
                  _lhsIlhsPattern
              _patternOmiscerrors =
                  _lhsImiscerrors
              _patternOnamesInScope =
                  _lhsInamesInScope
              _patternOtypeConstructors =
                  _lhsItypeConstructors
              _patternOvalueConstructors =
                  _lhsIvalueConstructors
              _patternOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternIcollectScopeInfos,_patternImiscerrors,_patternIpatVarNames,_patternIself,_patternIunboundNames,_patternIwarnings) =
                  (pattern_ _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_Record :: T_Range ->
                      T_Name ->
                      T_RecordPatternBindings ->
                      T_Pattern
sem_Pattern_Record range_ name_ recordPatternBindings_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _recordPatternBindingsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _recordPatternBindingsOnamesInScope :: Names
              _rangeIself :: Range
              _nameIself :: Name
              _recordPatternBindingsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _recordPatternBindingsIself :: RecordPatternBindings
              _recordPatternBindingsIunboundNames :: Names
              __tup21 =
                  internalError "PartialSyntax.ag" "n/a" "Pattern.Record"
              (_beta,_,_) =
                  __tup21
              (_,_constraints,_) =
                  __tup21
              (_,_,_environment) =
                  __tup21
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  _recordPatternBindingsIunboundNames
              _self =
                  Pattern_Record _rangeIself _nameIself _recordPatternBindingsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _recordPatternBindingsIcollectScopeInfos
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              _recordPatternBindingsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _recordPatternBindingsOnamesInScope =
                  _lhsInamesInScope
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _recordPatternBindingsIcollectScopeInfos,_recordPatternBindingsIself,_recordPatternBindingsIunboundNames) =
                  (recordPatternBindings_ _recordPatternBindingsOcollectScopeInfos _recordPatternBindingsOnamesInScope )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_Successor :: T_Range ->
                         T_Name ->
                         T_Literal ->
                         T_Pattern
sem_Pattern_Successor range_ name_ literal_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _literalOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _literalOmiscerrors :: ([Error])
              _rangeIself :: Range
              _nameIself :: Name
              _literalIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _literalImiscerrors :: ([Error])
              _literalIself :: Literal
              __tup22 =
                  internalError "PartialSyntax.ag" "n/a" "Pattern.Successor"
              (_beta,_,_) =
                  __tup22
              (_,_constraints,_) =
                  __tup22
              (_,_,_environment) =
                  __tup22
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_Successor _rangeIself _nameIself _literalIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _literalIcollectScopeInfos
              _lhsOmiscerrors =
                  _literalImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              _literalOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _literalOmiscerrors =
                  _lhsImiscerrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _literalIcollectScopeInfos,_literalImiscerrors,_literalIself) =
                  (literal_ _literalOcollectScopeInfos _literalOmiscerrors )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_Tuple :: T_Range ->
                     T_Patterns ->
                     T_Pattern
sem_Pattern_Tuple range_ patterns_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _patternsOallTypeConstructors :: Names
              _patternsOallValueConstructors :: Names
              _patternsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsOlhsPattern :: Bool
              _patternsOmiscerrors :: ([Error])
              _patternsOnamesInScope :: Names
              _patternsOtypeConstructors :: (M.Map Name Int)
              _patternsOvalueConstructors :: (M.Map Name TpScheme)
              _patternsOwarnings :: ([Warning])
              _rangeIself :: Range
              _patternsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternsImiscerrors :: ([Error])
              _patternsInumberOfPatterns :: Int
              _patternsIpatVarNames :: Names
              _patternsIself :: Patterns
              _patternsIunboundNames :: Names
              _patternsIwarnings :: ([Warning])
              _lhsOpatVarNames =
                  _patternsIpatVarNames
              _lhsOunboundNames =
                  _patternsIunboundNames
              _self =
                  Pattern_Tuple _rangeIself _patternsIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _patternsIcollectScopeInfos
              _lhsOmiscerrors =
                  _patternsImiscerrors
              _lhsOwarnings =
                  _patternsIwarnings
              _patternsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternsOallValueConstructors =
                  _lhsIallValueConstructors
              _patternsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternsOlhsPattern =
                  _lhsIlhsPattern
              _patternsOmiscerrors =
                  _lhsImiscerrors
              _patternsOnamesInScope =
                  _lhsInamesInScope
              _patternsOtypeConstructors =
                  _lhsItypeConstructors
              _patternsOvalueConstructors =
                  _lhsIvalueConstructors
              _patternsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternsIcollectScopeInfos,_patternsImiscerrors,_patternsInumberOfPatterns,_patternsIpatVarNames,_patternsIself,_patternsIunboundNames,_patternsIwarnings) =
                  (patterns_ _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_Variable :: T_Range ->
                        T_Name ->
                        T_Pattern
sem_Pattern_Variable range_ name_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOpatVarNames =
                  [ _nameIself ]
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_Variable _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Pattern_Wildcard :: T_Range ->
                        T_Pattern
sem_Pattern_Wildcard range_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Pattern
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _rangeIself :: Range
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  Pattern_Wildcard _rangeIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- Patterns ----------------------------------------------------
-- cata
sem_Patterns :: Patterns ->
                T_Patterns
sem_Patterns list  =
    (Prelude.foldr sem_Patterns_Cons sem_Patterns_Nil (Prelude.map sem_Pattern list) )
-- semantic domain
type T_Patterns = Names ->
                  Names ->
                  ([(ScopeInfo, Entity)]) ->
                  Bool ->
                  ([Error]) ->
                  Names ->
                  (M.Map Name Int) ->
                  (M.Map Name TpScheme) ->
                  ([Warning]) ->
                  ( ([(ScopeInfo, Entity)]),([Error]),Int,Names,Patterns,Names,([Warning]))
sem_Patterns_Cons :: T_Pattern ->
                     T_Patterns ->
                     T_Patterns
sem_Patterns_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOnumberOfPatterns :: Int
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Patterns
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOallValueConstructors :: Names
              _hdOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOlhsPattern :: Bool
              _hdOmiscerrors :: ([Error])
              _hdOnamesInScope :: Names
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOvalueConstructors :: (M.Map Name TpScheme)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOallValueConstructors :: Names
              _tlOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlOlhsPattern :: Bool
              _tlOmiscerrors :: ([Error])
              _tlOnamesInScope :: Names
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOvalueConstructors :: (M.Map Name TpScheme)
              _tlOwarnings :: ([Warning])
              _hdIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdImiscerrors :: ([Error])
              _hdIpatVarNames :: Names
              _hdIself :: Pattern
              _hdIunboundNames :: Names
              _hdIwarnings :: ([Warning])
              _tlIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlImiscerrors :: ([Error])
              _tlInumberOfPatterns :: Int
              _tlIpatVarNames :: Names
              _tlIself :: Patterns
              _tlIunboundNames :: Names
              _tlIwarnings :: ([Warning])
              _lhsOnumberOfPatterns =
                  1 + _tlInumberOfPatterns
              _lhsOpatVarNames =
                  _hdIpatVarNames ++ _tlIpatVarNames
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _tlIcollectScopeInfos
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOallValueConstructors =
                  _lhsIallValueConstructors
              _hdOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _hdOlhsPattern =
                  _lhsIlhsPattern
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOvalueConstructors =
                  _lhsIvalueConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOallValueConstructors =
                  _lhsIallValueConstructors
              _tlOcollectScopeInfos =
                  _hdIcollectScopeInfos
              _tlOlhsPattern =
                  _lhsIlhsPattern
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOvalueConstructors =
                  _lhsIvalueConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIcollectScopeInfos,_hdImiscerrors,_hdIpatVarNames,_hdIself,_hdIunboundNames,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOallValueConstructors _hdOcollectScopeInfos _hdOlhsPattern _hdOmiscerrors _hdOnamesInScope _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings )
              ( _tlIcollectScopeInfos,_tlImiscerrors,_tlInumberOfPatterns,_tlIpatVarNames,_tlIself,_tlIunboundNames,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOallValueConstructors _tlOcollectScopeInfos _tlOlhsPattern _tlOmiscerrors _tlOnamesInScope _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOnumberOfPatterns,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Patterns_Nil :: T_Patterns
sem_Patterns_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIcollectScopeInfos
       _lhsIlhsPattern
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOnumberOfPatterns :: Int
              _lhsOpatVarNames :: Names
              _lhsOunboundNames :: Names
              _lhsOself :: Patterns
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _lhsOnumberOfPatterns =
                  0
              _lhsOpatVarNames =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOcollectScopeInfos,_lhsOmiscerrors,_lhsOnumberOfPatterns,_lhsOpatVarNames,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- Position ----------------------------------------------------
-- cata
sem_Position :: Position ->
                T_Position
sem_Position (Position_Position _filename _line _column )  =
    (sem_Position_Position _filename _line _column )
sem_Position (Position_Unknown )  =
    (sem_Position_Unknown )
-- semantic domain
type T_Position = ( Position)
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
sem_Qualifier :: Qualifier ->
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
type T_Qualifier = Names ->
                   Names ->
                   ClassEnvironment ->
                   ([(ScopeInfo, Entity)]) ->
                   ([Error]) ->
                   ([Error]) ->
                   Names ->
                   ([Option]) ->
                   OrderedTypeSynonyms ->
                   (M.Map Name Int) ->
                   Names ->
                   (M.Map Name TpScheme) ->
                   ([Warning]) ->
                   ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),Names,Qualifier,Names,([Warning]))
sem_Qualifier_Empty :: T_Range ->
                       T_Qualifier
sem_Qualifier_Empty range_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifier
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOnamesInScope :: Names
              _lhsOunboundNames :: Names
              _lhsOwarnings :: ([Warning])
              _rangeIself :: Range
              _lhsOcollectInstances =
                  []
              _self =
                  Qualifier_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOunboundNames =
                  _lhsIunboundNames
              _lhsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Qualifier_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Qualifier
sem_Qualifier_Generator range_ pattern_ expression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOnamesInScope :: Names
              _lhsOunboundNames :: Names
              _expressionOnamesInScope :: Names
              _patternOlhsPattern :: Bool
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifier
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _patternOallTypeConstructors :: Names
              _patternOallValueConstructors :: Names
              _patternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternOmiscerrors :: ([Error])
              _patternOnamesInScope :: Names
              _patternOtypeConstructors :: (M.Map Name Int)
              _patternOvalueConstructors :: (M.Map Name TpScheme)
              _patternOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _patternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternImiscerrors :: ([Error])
              _patternIpatVarNames :: Names
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _patternIwarnings :: ([Warning])
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              __tup23 =
                  changeOfScope _patternIpatVarNames (_expressionIunboundNames  ++ _lhsIunboundNames)  _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup23
              (_,_unboundNames,_) =
                  __tup23
              (_,_,_scopeInfo) =
                  __tup23
              _lhsOnamesInScope =
                  _namesInScope
              _lhsOunboundNames =
                  _unboundNames
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _patternOlhsPattern =
                  False
              _lhsOcollectScopeInfos =
                  (_scopeInfo, Variable)   : _expressionIcollectScopeInfos
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _self =
                  Qualifier_Generator _rangeIself _patternIself _expressionIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _expressionIkindErrors
              _lhsOmiscerrors =
                  _expressionImiscerrors
              _lhsOwarnings =
                  _expressionIwarnings
              _patternOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternOallValueConstructors =
                  _lhsIallValueConstructors
              _patternOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternOmiscerrors =
                  _lhsImiscerrors
              _patternOnamesInScope =
                  _namesInScope
              _patternOtypeConstructors =
                  _lhsItypeConstructors
              _patternOvalueConstructors =
                  _lhsIvalueConstructors
              _patternOwarnings =
                  _lhsIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _patternIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _patternImiscerrors
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _patternIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternIcollectScopeInfos,_patternImiscerrors,_patternIpatVarNames,_patternIself,_patternIunboundNames,_patternIwarnings) =
                  (pattern_ _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Qualifier_Guard :: T_Range ->
                       T_Expression ->
                       T_Qualifier
sem_Qualifier_Guard range_ guard_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifier
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOnamesInScope :: Names
              _lhsOwarnings :: ([Warning])
              _guardOallTypeConstructors :: Names
              _guardOallValueConstructors :: Names
              _guardOclassEnvironment :: ClassEnvironment
              _guardOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _guardOkindErrors :: ([Error])
              _guardOmiscerrors :: ([Error])
              _guardOnamesInScope :: Names
              _guardOoptions :: ([Option])
              _guardOorderedTypeSynonyms :: OrderedTypeSynonyms
              _guardOtypeConstructors :: (M.Map Name Int)
              _guardOvalueConstructors :: (M.Map Name TpScheme)
              _guardOwarnings :: ([Warning])
              _rangeIself :: Range
              _guardIcollectInstances :: ([(Name, Instance)])
              _guardIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _guardIkindErrors :: ([Error])
              _guardImiscerrors :: ([Error])
              _guardIself :: Expression
              _guardIunboundNames :: Names
              _guardIwarnings :: ([Warning])
              _lhsOunboundNames =
                  _guardIunboundNames ++ _lhsIunboundNames
              _lhsOcollectInstances =
                  _guardIcollectInstances
              _self =
                  Qualifier_Guard _rangeIself _guardIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _guardIcollectScopeInfos
              _lhsOkindErrors =
                  _guardIkindErrors
              _lhsOmiscerrors =
                  _guardImiscerrors
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOwarnings =
                  _guardIwarnings
              _guardOallTypeConstructors =
                  _lhsIallTypeConstructors
              _guardOallValueConstructors =
                  _lhsIallValueConstructors
              _guardOclassEnvironment =
                  _lhsIclassEnvironment
              _guardOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _guardOkindErrors =
                  _lhsIkindErrors
              _guardOmiscerrors =
                  _lhsImiscerrors
              _guardOnamesInScope =
                  _lhsInamesInScope
              _guardOoptions =
                  _lhsIoptions
              _guardOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _guardOtypeConstructors =
                  _lhsItypeConstructors
              _guardOvalueConstructors =
                  _lhsIvalueConstructors
              _guardOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _guardIcollectInstances,_guardIcollectScopeInfos,_guardIkindErrors,_guardImiscerrors,_guardIself,_guardIunboundNames,_guardIwarnings) =
                  (guard_ _guardOallTypeConstructors _guardOallValueConstructors _guardOclassEnvironment _guardOcollectScopeInfos _guardOkindErrors _guardOmiscerrors _guardOnamesInScope _guardOoptions _guardOorderedTypeSynonyms _guardOtypeConstructors _guardOvalueConstructors _guardOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Qualifier_Let :: T_Range ->
                     T_Declarations ->
                     T_Qualifier
sem_Qualifier_Let range_ declarations_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _declarationsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOunboundNames :: Names
              _lhsOwarnings :: ([Warning])
              _declarationsOpreviousWasAlsoFB :: (Maybe Name)
              _declarationsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOmiscerrors :: ([Error])
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifier
              _lhsOkindErrors :: ([Error])
              _lhsOnamesInScope :: Names
              _declarationsOallTypeConstructors :: Names
              _declarationsOallValueConstructors :: Names
              _declarationsOclassEnvironment :: ClassEnvironment
              _declarationsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _declarationsOcollectTypeConstructors :: ([(Name,Int)])
              _declarationsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _declarationsOcollectValueConstructors :: ([(Name,TpScheme)])
              _declarationsOkindErrors :: ([Error])
              _declarationsOmiscerrors :: ([Error])
              _declarationsOnamesInScope :: Names
              _declarationsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _declarationsOoptions :: ([Option])
              _declarationsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _declarationsOtypeConstructors :: (M.Map Name Int)
              _declarationsOvalueConstructors :: (M.Map Name TpScheme)
              _declarationsOwarnings :: ([Warning])
              _rangeIself :: Range
              _declarationsIcollectInstances :: ([(Name, Instance)])
              _declarationsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _declarationsIcollectTypeConstructors :: ([(Name,Int)])
              _declarationsIcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _declarationsIcollectValueConstructors :: ([(Name,TpScheme)])
              _declarationsIdeclVarNames :: Names
              _declarationsIkindErrors :: ([Error])
              _declarationsImiscerrors :: ([Error])
              _declarationsIoperatorFixities :: ([(Name,(Int,Assoc))])
              _declarationsIpreviousWasAlsoFB :: (Maybe Name)
              _declarationsIrestrictedNames :: Names
              _declarationsIself :: Declarations
              _declarationsIsuspiciousFBs :: ([(Name,Name)])
              _declarationsItypeSignatures :: ([(Name,TpScheme)])
              _declarationsIunboundNames :: Names
              _declarationsIwarnings :: ([Warning])
              _declarationsOtypeSignatures =
                  []
              __tup24 =
                  changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup24
              (_,_unboundNames,_) =
                  __tup24
              (_,_,_scopeInfo) =
                  __tup24
              _lhsOunboundNames =
                  _unboundNames
              _lhsOwarnings =
                  _declarationsIwarnings ++
                  _suspiciousErrors
              _declarationsOpreviousWasAlsoFB =
                  Nothing
              _declarationsOsuspiciousFBs =
                  []
              _suspiciousErrors =
                  findSimilarFunctionBindings _declarationsItypeSignatures _declarationsIsuspiciousFBs
              _lhsOmiscerrors =
                  _typeSignatureErrors ++ _declarationsImiscerrors
              __tup25 =
                  uniqueAppearance (map fst _declarationsItypeSignatures)
              (_,_doubles) =
                  __tup25
              _typeSignatureErrors =
                  checkTypeSignatures _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
              __tup26 =
                  internalError "PartialSyntax.ag" "n/a" "toplevel Qualifier"
              (_collectTypeConstructors,_,_,_,_,_) =
                  __tup26
              (_,_collectValueConstructors,_,_,_,_) =
                  __tup26
              (_,_,_collectTypeSynonyms,_,_,_) =
                  __tup26
              (_,_,_,_collectConstructorEnv,_,_) =
                  __tup26
              (_,_,_,_,_derivedFunctions,_) =
                  __tup26
              (_,_,_,_,_,_operatorFixities) =
                  __tup26
              _lhsOcollectScopeInfos =
                  (_scopeInfo, Definition) : _declarationsIcollectScopeInfos
              _lhsOcollectInstances =
                  _declarationsIcollectInstances
              _self =
                  Qualifier_Let _rangeIself _declarationsIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _declarationsIkindErrors
              _lhsOnamesInScope =
                  _namesInScope
              _declarationsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _declarationsOallValueConstructors =
                  _lhsIallValueConstructors
              _declarationsOclassEnvironment =
                  _lhsIclassEnvironment
              _declarationsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _declarationsOcollectTypeConstructors =
                  _collectTypeConstructors
              _declarationsOcollectTypeSynonyms =
                  _collectTypeSynonyms
              _declarationsOcollectValueConstructors =
                  _collectValueConstructors
              _declarationsOkindErrors =
                  _lhsIkindErrors
              _declarationsOmiscerrors =
                  _lhsImiscerrors
              _declarationsOnamesInScope =
                  _namesInScope
              _declarationsOoperatorFixities =
                  _operatorFixities
              _declarationsOoptions =
                  _lhsIoptions
              _declarationsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _declarationsOtypeConstructors =
                  _lhsItypeConstructors
              _declarationsOvalueConstructors =
                  _lhsIvalueConstructors
              _declarationsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIcollectInstances,_declarationsIcollectScopeInfos,_declarationsIcollectTypeConstructors,_declarationsIcollectTypeSynonyms,_declarationsIcollectValueConstructors,_declarationsIdeclVarNames,_declarationsIkindErrors,_declarationsImiscerrors,_declarationsIoperatorFixities,_declarationsIpreviousWasAlsoFB,_declarationsIrestrictedNames,_declarationsIself,_declarationsIsuspiciousFBs,_declarationsItypeSignatures,_declarationsIunboundNames,_declarationsIwarnings) =
                  (declarations_ _declarationsOallTypeConstructors _declarationsOallValueConstructors _declarationsOclassEnvironment _declarationsOcollectScopeInfos _declarationsOcollectTypeConstructors _declarationsOcollectTypeSynonyms _declarationsOcollectValueConstructors _declarationsOkindErrors _declarationsOmiscerrors _declarationsOnamesInScope _declarationsOoperatorFixities _declarationsOoptions _declarationsOorderedTypeSynonyms _declarationsOpreviousWasAlsoFB _declarationsOsuspiciousFBs _declarationsOtypeConstructors _declarationsOtypeSignatures _declarationsOvalueConstructors _declarationsOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- Qualifiers --------------------------------------------------
-- cata
sem_Qualifiers :: Qualifiers ->
                  T_Qualifiers
sem_Qualifiers list  =
    (Prelude.foldr sem_Qualifiers_Cons sem_Qualifiers_Nil (Prelude.map sem_Qualifier list) )
-- semantic domain
type T_Qualifiers = Names ->
                    Names ->
                    ClassEnvironment ->
                    ([(ScopeInfo, Entity)]) ->
                    ([Error]) ->
                    ([Error]) ->
                    Names ->
                    ([Option]) ->
                    OrderedTypeSynonyms ->
                    (M.Map Name Int) ->
                    Names ->
                    (M.Map Name TpScheme) ->
                    ([Warning]) ->
                    ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),Names,Qualifiers,Names,([Warning]))
sem_Qualifiers_Cons :: T_Qualifier ->
                       T_Qualifiers ->
                       T_Qualifiers
sem_Qualifiers_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _tlOunboundNames :: Names
              _hdOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifiers
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOnamesInScope :: Names
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOallValueConstructors :: Names
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOkindErrors :: ([Error])
              _hdOmiscerrors :: ([Error])
              _hdOnamesInScope :: Names
              _hdOoptions :: ([Option])
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOvalueConstructors :: (M.Map Name TpScheme)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOallValueConstructors :: Names
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlOkindErrors :: ([Error])
              _tlOmiscerrors :: ([Error])
              _tlOnamesInScope :: Names
              _tlOoptions :: ([Option])
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOvalueConstructors :: (M.Map Name TpScheme)
              _tlOwarnings :: ([Warning])
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdIkindErrors :: ([Error])
              _hdImiscerrors :: ([Error])
              _hdInamesInScope :: Names
              _hdIself :: Qualifier
              _hdIunboundNames :: Names
              _hdIwarnings :: ([Warning])
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlIkindErrors :: ([Error])
              _tlImiscerrors :: ([Error])
              _tlInamesInScope :: Names
              _tlIself :: Qualifiers
              _tlIunboundNames :: Names
              _tlIwarnings :: ([Warning])
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
              _lhsOcollectScopeInfos =
                  _tlIcollectScopeInfos
              _lhsOkindErrors =
                  _tlIkindErrors
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOnamesInScope =
                  _tlInamesInScope
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOallValueConstructors =
                  _lhsIallValueConstructors
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _hdOkindErrors =
                  _lhsIkindErrors
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOoptions =
                  _lhsIoptions
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOvalueConstructors =
                  _lhsIvalueConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOallValueConstructors =
                  _lhsIallValueConstructors
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectScopeInfos =
                  _hdIcollectScopeInfos
              _tlOkindErrors =
                  _hdIkindErrors
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOnamesInScope =
                  _hdInamesInScope
              _tlOoptions =
                  _lhsIoptions
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOvalueConstructors =
                  _lhsIvalueConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIcollectInstances,_hdIcollectScopeInfos,_hdIkindErrors,_hdImiscerrors,_hdInamesInScope,_hdIself,_hdIunboundNames,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOunboundNames _hdOvalueConstructors _hdOwarnings )
              ( _tlIcollectInstances,_tlIcollectScopeInfos,_tlIkindErrors,_tlImiscerrors,_tlInamesInScope,_tlIself,_tlIunboundNames,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOunboundNames _tlOvalueConstructors _tlOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Qualifiers_Nil :: T_Qualifiers
sem_Qualifiers_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Qualifiers
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOnamesInScope :: Names
              _lhsOwarnings :: ([Warning])
              _lhsOunboundNames =
                  _lhsIunboundNames
              _lhsOcollectInstances =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- Range -------------------------------------------------------
-- cata
sem_Range :: Range ->
             T_Range
sem_Range (Range_Range _start _stop )  =
    (sem_Range_Range (sem_Position _start ) (sem_Position _stop ) )
-- semantic domain
type T_Range = ( Range)
sem_Range_Range :: T_Position ->
                   T_Position ->
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
sem_RecordExpressionBinding :: RecordExpressionBinding ->
                               T_RecordExpressionBinding
sem_RecordExpressionBinding (RecordExpressionBinding_RecordExpressionBinding _range _name _expression )  =
    (sem_RecordExpressionBinding_RecordExpressionBinding (sem_Range _range ) (sem_Name _name ) (sem_Expression _expression ) )
-- semantic domain
type T_RecordExpressionBinding = ClassEnvironment ->
                                 ([(ScopeInfo, Entity)]) ->
                                 Names ->
                                 ([Option]) ->
                                 OrderedTypeSynonyms ->
                                 ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),RecordExpressionBinding,Names)
sem_RecordExpressionBinding_RecordExpressionBinding :: T_Range ->
                                                       T_Name ->
                                                       T_Expression ->
                                                       T_RecordExpressionBinding
sem_RecordExpressionBinding_RecordExpressionBinding range_ name_ expression_  =
    (\ _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: RecordExpressionBinding
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              __tup27 =
                  internalError "PartialSyntax.ag" "n/a" "RecordExpressionBinding.RecordExpressionBinding"
              (_monos,_,_,_,_,_,_,_,_,_,_) =
                  __tup27
              (_,_constructorenv,_,_,_,_,_,_,_,_,_) =
                  __tup27
              (_,_,_betaUnique,_,_,_,_,_,_,_,_) =
                  __tup27
              (_,_,_,_miscerrors,_,_,_,_,_,_,_) =
                  __tup27
              (_,_,_,_,_warnings,_,_,_,_,_,_) =
                  __tup27
              (_,_,_,_,_,_kindErrors,_,_,_,_,_) =
                  __tup27
              (_,_,_,_,_,_,_valueConstructors,_,_,_,_) =
                  __tup27
              (_,_,_,_,_,_,_,_allValueConstructors,_,_,_) =
                  __tup27
              (_,_,_,_,_,_,_,_,_typeConstructors,_,_) =
                  __tup27
              (_,_,_,_,_,_,_,_,_,_allTypeConstructors,_) =
                  __tup27
              (_,_,_,_,_,_,_,_,_,_,_importEnvironment) =
                  __tup27
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _lhsOunboundNames =
                  _expressionIunboundNames
              _self =
                  RecordExpressionBinding_RecordExpressionBinding _rangeIself _nameIself _expressionIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _expressionOallTypeConstructors =
                  _allTypeConstructors
              _expressionOallValueConstructors =
                  _allValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionOkindErrors =
                  _kindErrors
              _expressionOmiscerrors =
                  _miscerrors
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _typeConstructors
              _expressionOvalueConstructors =
                  _valueConstructors
              _expressionOwarnings =
                  _warnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOself,_lhsOunboundNames)))
-- RecordExpressionBindings ------------------------------------
-- cata
sem_RecordExpressionBindings :: RecordExpressionBindings ->
                                T_RecordExpressionBindings
sem_RecordExpressionBindings list  =
    (Prelude.foldr sem_RecordExpressionBindings_Cons sem_RecordExpressionBindings_Nil (Prelude.map sem_RecordExpressionBinding list) )
-- semantic domain
type T_RecordExpressionBindings = ClassEnvironment ->
                                  ([(ScopeInfo, Entity)]) ->
                                  Names ->
                                  ([Option]) ->
                                  OrderedTypeSynonyms ->
                                  ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),RecordExpressionBindings,Names)
sem_RecordExpressionBindings_Cons :: T_RecordExpressionBinding ->
                                     T_RecordExpressionBindings ->
                                     T_RecordExpressionBindings
sem_RecordExpressionBindings_Cons hd_ tl_  =
    (\ _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: RecordExpressionBindings
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOnamesInScope :: Names
              _hdOoptions :: ([Option])
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlOnamesInScope :: Names
              _tlOoptions :: ([Option])
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdIself :: RecordExpressionBinding
              _hdIunboundNames :: Names
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlIself :: RecordExpressionBindings
              _tlIunboundNames :: Names
              _lhsOcollectInstances =
                  _hdIcollectInstances  ++  _tlIcollectInstances
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _tlIcollectScopeInfos
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOoptions =
                  _lhsIoptions
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectScopeInfos =
                  _hdIcollectScopeInfos
              _tlOnamesInScope =
                  _lhsInamesInScope
              _tlOoptions =
                  _lhsIoptions
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              ( _hdIcollectInstances,_hdIcollectScopeInfos,_hdIself,_hdIunboundNames) =
                  (hd_ _hdOclassEnvironment _hdOcollectScopeInfos _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms )
              ( _tlIcollectInstances,_tlIcollectScopeInfos,_tlIself,_tlIunboundNames) =
                  (tl_ _tlOclassEnvironment _tlOcollectScopeInfos _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOself,_lhsOunboundNames)))
sem_RecordExpressionBindings_Nil :: T_RecordExpressionBindings
sem_RecordExpressionBindings_Nil  =
    (\ _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOunboundNames :: Names
              _lhsOself :: RecordExpressionBindings
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectInstances =
                  []
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOself,_lhsOunboundNames)))
-- RecordPatternBinding ----------------------------------------
-- cata
sem_RecordPatternBinding :: RecordPatternBinding ->
                            T_RecordPatternBinding
sem_RecordPatternBinding (RecordPatternBinding_RecordPatternBinding _range _name _pattern )  =
    (sem_RecordPatternBinding_RecordPatternBinding (sem_Range _range ) (sem_Name _name ) (sem_Pattern _pattern ) )
-- semantic domain
type T_RecordPatternBinding = ([(ScopeInfo, Entity)]) ->
                              Names ->
                              ( ([(ScopeInfo, Entity)]),RecordPatternBinding,Names)
sem_RecordPatternBinding_RecordPatternBinding :: T_Range ->
                                                 T_Name ->
                                                 T_Pattern ->
                                                 T_RecordPatternBinding
sem_RecordPatternBinding_RecordPatternBinding range_ name_ pattern_  =
    (\ _lhsIcollectScopeInfos
       _lhsInamesInScope ->
         (let _patternOlhsPattern :: Bool
              _lhsOunboundNames :: Names
              _lhsOself :: RecordPatternBinding
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternOallTypeConstructors :: Names
              _patternOallValueConstructors :: Names
              _patternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternOmiscerrors :: ([Error])
              _patternOnamesInScope :: Names
              _patternOtypeConstructors :: (M.Map Name Int)
              _patternOvalueConstructors :: (M.Map Name TpScheme)
              _patternOwarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _patternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternImiscerrors :: ([Error])
              _patternIpatVarNames :: Names
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _patternIwarnings :: ([Warning])
              _patternOlhsPattern =
                  False
              __tup28 =
                  internalError "PartialSyntax.ag" "n/a" "RecordPatternBinding.RecordPatternBinding"
              (_monos,_,_,_,_,_,_,_,_,_) =
                  __tup28
              (_,_constructorenv,_,_,_,_,_,_,_,_) =
                  __tup28
              (_,_,_betaUnique,_,_,_,_,_,_,_) =
                  __tup28
              (_,_,_,_miscerrors,_,_,_,_,_,_) =
                  __tup28
              (_,_,_,_,_warnings,_,_,_,_,_) =
                  __tup28
              (_,_,_,_,_,_valueConstructors,_,_,_,_) =
                  __tup28
              (_,_,_,_,_,_,_allValueConstructors,_,_,_) =
                  __tup28
              (_,_,_,_,_,_,_,_typeConstructors,_,_) =
                  __tup28
              (_,_,_,_,_,_,_,_,_allTypeConstructors,_) =
                  __tup28
              (_,_,_,_,_,_,_,_,_,_importEnvironment) =
                  __tup28
              _lhsOunboundNames =
                  _patternIunboundNames
              _self =
                  RecordPatternBinding_RecordPatternBinding _rangeIself _nameIself _patternIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _patternIcollectScopeInfos
              _patternOallTypeConstructors =
                  _allTypeConstructors
              _patternOallValueConstructors =
                  _allValueConstructors
              _patternOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternOmiscerrors =
                  _miscerrors
              _patternOnamesInScope =
                  _lhsInamesInScope
              _patternOtypeConstructors =
                  _typeConstructors
              _patternOvalueConstructors =
                  _valueConstructors
              _patternOwarnings =
                  _warnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
              ( _patternIcollectScopeInfos,_patternImiscerrors,_patternIpatVarNames,_patternIself,_patternIunboundNames,_patternIwarnings) =
                  (pattern_ _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings )
          in  ( _lhsOcollectScopeInfos,_lhsOself,_lhsOunboundNames)))
-- RecordPatternBindings ---------------------------------------
-- cata
sem_RecordPatternBindings :: RecordPatternBindings ->
                             T_RecordPatternBindings
sem_RecordPatternBindings list  =
    (Prelude.foldr sem_RecordPatternBindings_Cons sem_RecordPatternBindings_Nil (Prelude.map sem_RecordPatternBinding list) )
-- semantic domain
type T_RecordPatternBindings = ([(ScopeInfo, Entity)]) ->
                               Names ->
                               ( ([(ScopeInfo, Entity)]),RecordPatternBindings,Names)
sem_RecordPatternBindings_Cons :: T_RecordPatternBinding ->
                                  T_RecordPatternBindings ->
                                  T_RecordPatternBindings
sem_RecordPatternBindings_Cons hd_ tl_  =
    (\ _lhsIcollectScopeInfos
       _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: RecordPatternBindings
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOnamesInScope :: Names
              _tlOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlOnamesInScope :: Names
              _hdIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdIself :: RecordPatternBinding
              _hdIunboundNames :: Names
              _tlIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlIself :: RecordPatternBindings
              _tlIunboundNames :: Names
              _lhsOunboundNames =
                  _hdIunboundNames ++ _tlIunboundNames
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _tlIcollectScopeInfos
              _hdOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _hdOnamesInScope =
                  _lhsInamesInScope
              _tlOcollectScopeInfos =
                  _hdIcollectScopeInfos
              _tlOnamesInScope =
                  _lhsInamesInScope
              ( _hdIcollectScopeInfos,_hdIself,_hdIunboundNames) =
                  (hd_ _hdOcollectScopeInfos _hdOnamesInScope )
              ( _tlIcollectScopeInfos,_tlIself,_tlIunboundNames) =
                  (tl_ _tlOcollectScopeInfos _tlOnamesInScope )
          in  ( _lhsOcollectScopeInfos,_lhsOself,_lhsOunboundNames)))
sem_RecordPatternBindings_Nil :: T_RecordPatternBindings
sem_RecordPatternBindings_Nil  =
    (\ _lhsIcollectScopeInfos
       _lhsInamesInScope ->
         (let _lhsOunboundNames :: Names
              _lhsOself :: RecordPatternBindings
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOunboundNames =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
          in  ( _lhsOcollectScopeInfos,_lhsOself,_lhsOunboundNames)))
-- RightHandSide -----------------------------------------------
-- cata
sem_RightHandSide :: RightHandSide ->
                     T_RightHandSide
sem_RightHandSide (RightHandSide_Expression _range _expression _where )  =
    (sem_RightHandSide_Expression (sem_Range _range ) (sem_Expression _expression ) (sem_MaybeDeclarations _where ) )
sem_RightHandSide (RightHandSide_Guarded _range _guardedexpressions _where )  =
    (sem_RightHandSide_Guarded (sem_Range _range ) (sem_GuardedExpressions _guardedexpressions ) (sem_MaybeDeclarations _where ) )
-- semantic domain
type T_RightHandSide = Names ->
                       Names ->
                       ClassEnvironment ->
                       ([(ScopeInfo, Entity)]) ->
                       ([Error]) ->
                       ([Error]) ->
                       Names ->
                       ([Option]) ->
                       OrderedTypeSynonyms ->
                       (M.Map Name Int) ->
                       (M.Map Name TpScheme) ->
                       ([Warning]) ->
                       ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),([Error]),RightHandSide,Names,([Warning]))
sem_RightHandSide_Expression :: T_Range ->
                                T_Expression ->
                                T_MaybeDeclarations ->
                                T_RightHandSide
sem_RightHandSide_Expression range_ expression_ where_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _expressionOnamesInScope :: Names
              _whereOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: RightHandSide
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _whereOallTypeConstructors :: Names
              _whereOallValueConstructors :: Names
              _whereOclassEnvironment :: ClassEnvironment
              _whereOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _whereOkindErrors :: ([Error])
              _whereOmiscerrors :: ([Error])
              _whereOnamesInScope :: Names
              _whereOoptions :: ([Option])
              _whereOorderedTypeSynonyms :: OrderedTypeSynonyms
              _whereOtypeConstructors :: (M.Map Name Int)
              _whereOvalueConstructors :: (M.Map Name TpScheme)
              _whereOwarnings :: ([Warning])
              _rangeIself :: Range
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _whereIcollectInstances :: ([(Name, Instance)])
              _whereIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _whereIkindErrors :: ([Error])
              _whereImiscerrors :: ([Error])
              _whereInamesInScope :: Names
              _whereIself :: MaybeDeclarations
              _whereIunboundNames :: Names
              _whereIwarnings :: ([Warning])
              _lhsOunboundNames =
                  _whereIunboundNames
              _expressionOnamesInScope =
                  _whereInamesInScope
              _whereOunboundNames =
                  _expressionIunboundNames
              _lhsOcollectInstances =
                  _expressionIcollectInstances  ++  _whereIcollectInstances
              _self =
                  RightHandSide_Expression _rangeIself _expressionIself _whereIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _whereIcollectScopeInfos
              _lhsOkindErrors =
                  _whereIkindErrors
              _lhsOmiscerrors =
                  _whereImiscerrors
              _lhsOwarnings =
                  _whereIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _lhsImiscerrors
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _lhsIwarnings
              _whereOallTypeConstructors =
                  _lhsIallTypeConstructors
              _whereOallValueConstructors =
                  _lhsIallValueConstructors
              _whereOclassEnvironment =
                  _lhsIclassEnvironment
              _whereOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _whereOkindErrors =
                  _expressionIkindErrors
              _whereOmiscerrors =
                  _expressionImiscerrors
              _whereOnamesInScope =
                  _lhsInamesInScope
              _whereOoptions =
                  _lhsIoptions
              _whereOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _whereOtypeConstructors =
                  _lhsItypeConstructors
              _whereOvalueConstructors =
                  _lhsIvalueConstructors
              _whereOwarnings =
                  _expressionIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
              ( _whereIcollectInstances,_whereIcollectScopeInfos,_whereIkindErrors,_whereImiscerrors,_whereInamesInScope,_whereIself,_whereIunboundNames,_whereIwarnings) =
                  (where_ _whereOallTypeConstructors _whereOallValueConstructors _whereOclassEnvironment _whereOcollectScopeInfos _whereOkindErrors _whereOmiscerrors _whereOnamesInScope _whereOoptions _whereOorderedTypeSynonyms _whereOtypeConstructors _whereOunboundNames _whereOvalueConstructors _whereOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_RightHandSide_Guarded :: T_Range ->
                             T_GuardedExpressions ->
                             T_MaybeDeclarations ->
                             T_RightHandSide
sem_RightHandSide_Guarded range_ guardedexpressions_ where_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _guardedexpressionsOnamesInScope :: Names
              _whereOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: RightHandSide
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _guardedexpressionsOallTypeConstructors :: Names
              _guardedexpressionsOallValueConstructors :: Names
              _guardedexpressionsOclassEnvironment :: ClassEnvironment
              _guardedexpressionsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _guardedexpressionsOkindErrors :: ([Error])
              _guardedexpressionsOmiscerrors :: ([Error])
              _guardedexpressionsOoptions :: ([Option])
              _guardedexpressionsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _guardedexpressionsOtypeConstructors :: (M.Map Name Int)
              _guardedexpressionsOvalueConstructors :: (M.Map Name TpScheme)
              _guardedexpressionsOwarnings :: ([Warning])
              _whereOallTypeConstructors :: Names
              _whereOallValueConstructors :: Names
              _whereOclassEnvironment :: ClassEnvironment
              _whereOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _whereOkindErrors :: ([Error])
              _whereOmiscerrors :: ([Error])
              _whereOnamesInScope :: Names
              _whereOoptions :: ([Option])
              _whereOorderedTypeSynonyms :: OrderedTypeSynonyms
              _whereOtypeConstructors :: (M.Map Name Int)
              _whereOvalueConstructors :: (M.Map Name TpScheme)
              _whereOwarnings :: ([Warning])
              _rangeIself :: Range
              _guardedexpressionsIcollectInstances :: ([(Name, Instance)])
              _guardedexpressionsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _guardedexpressionsIkindErrors :: ([Error])
              _guardedexpressionsImiscerrors :: ([Error])
              _guardedexpressionsIself :: GuardedExpressions
              _guardedexpressionsIunboundNames :: Names
              _guardedexpressionsIwarnings :: ([Warning])
              _whereIcollectInstances :: ([(Name, Instance)])
              _whereIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _whereIkindErrors :: ([Error])
              _whereImiscerrors :: ([Error])
              _whereInamesInScope :: Names
              _whereIself :: MaybeDeclarations
              _whereIunboundNames :: Names
              _whereIwarnings :: ([Warning])
              _lhsOunboundNames =
                  _whereIunboundNames
              _guardedexpressionsOnamesInScope =
                  _whereInamesInScope
              _whereOunboundNames =
                  _guardedexpressionsIunboundNames
              _lhsOcollectInstances =
                  _guardedexpressionsIcollectInstances  ++  _whereIcollectInstances
              _self =
                  RightHandSide_Guarded _rangeIself _guardedexpressionsIself _whereIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _whereIcollectScopeInfos
              _lhsOkindErrors =
                  _whereIkindErrors
              _lhsOmiscerrors =
                  _whereImiscerrors
              _lhsOwarnings =
                  _whereIwarnings
              _guardedexpressionsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _guardedexpressionsOallValueConstructors =
                  _lhsIallValueConstructors
              _guardedexpressionsOclassEnvironment =
                  _lhsIclassEnvironment
              _guardedexpressionsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _guardedexpressionsOkindErrors =
                  _lhsIkindErrors
              _guardedexpressionsOmiscerrors =
                  _lhsImiscerrors
              _guardedexpressionsOoptions =
                  _lhsIoptions
              _guardedexpressionsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _guardedexpressionsOtypeConstructors =
                  _lhsItypeConstructors
              _guardedexpressionsOvalueConstructors =
                  _lhsIvalueConstructors
              _guardedexpressionsOwarnings =
                  _lhsIwarnings
              _whereOallTypeConstructors =
                  _lhsIallTypeConstructors
              _whereOallValueConstructors =
                  _lhsIallValueConstructors
              _whereOclassEnvironment =
                  _lhsIclassEnvironment
              _whereOcollectScopeInfos =
                  _guardedexpressionsIcollectScopeInfos
              _whereOkindErrors =
                  _guardedexpressionsIkindErrors
              _whereOmiscerrors =
                  _guardedexpressionsImiscerrors
              _whereOnamesInScope =
                  _lhsInamesInScope
              _whereOoptions =
                  _lhsIoptions
              _whereOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _whereOtypeConstructors =
                  _lhsItypeConstructors
              _whereOvalueConstructors =
                  _lhsIvalueConstructors
              _whereOwarnings =
                  _guardedexpressionsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _guardedexpressionsIcollectInstances,_guardedexpressionsIcollectScopeInfos,_guardedexpressionsIkindErrors,_guardedexpressionsImiscerrors,_guardedexpressionsIself,_guardedexpressionsIunboundNames,_guardedexpressionsIwarnings) =
                  (guardedexpressions_ _guardedexpressionsOallTypeConstructors _guardedexpressionsOallValueConstructors _guardedexpressionsOclassEnvironment _guardedexpressionsOcollectScopeInfos _guardedexpressionsOkindErrors _guardedexpressionsOmiscerrors _guardedexpressionsOnamesInScope _guardedexpressionsOoptions _guardedexpressionsOorderedTypeSynonyms _guardedexpressionsOtypeConstructors _guardedexpressionsOvalueConstructors _guardedexpressionsOwarnings )
              ( _whereIcollectInstances,_whereIcollectScopeInfos,_whereIkindErrors,_whereImiscerrors,_whereInamesInScope,_whereIself,_whereIunboundNames,_whereIwarnings) =
                  (where_ _whereOallTypeConstructors _whereOallValueConstructors _whereOclassEnvironment _whereOcollectScopeInfos _whereOkindErrors _whereOmiscerrors _whereOnamesInScope _whereOoptions _whereOorderedTypeSynonyms _whereOtypeConstructors _whereOunboundNames _whereOvalueConstructors _whereOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOmiscerrors,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- SimpleType --------------------------------------------------
-- cata
sem_SimpleType :: SimpleType ->
                  T_SimpleType
sem_SimpleType (SimpleType_SimpleType _range _name _typevariables )  =
    (sem_SimpleType_SimpleType (sem_Range _range ) (sem_Name _name ) (sem_Names _typevariables ) )
-- semantic domain
type T_SimpleType = ( Name,SimpleType,Names)
sem_SimpleType_SimpleType :: T_Range ->
                             T_Name ->
                             T_Names ->
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
sem_Statement :: Statement ->
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
type T_Statement = Names ->
                   Names ->
                   ClassEnvironment ->
                   ([(ScopeInfo, Entity)]) ->
                   ([Error]) ->
                   Bool ->
                   ([Error]) ->
                   Names ->
                   ([Option]) ->
                   OrderedTypeSynonyms ->
                   (M.Map Name Int) ->
                   Names ->
                   (M.Map Name TpScheme) ->
                   ([Warning]) ->
                   ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),Bool,([Error]),Names,Statement,Names,([Warning]))
sem_Statement_Empty :: T_Range ->
                       T_Statement
sem_Statement_Empty range_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsIlastStatementIsExpr
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statement
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOlastStatementIsExpr :: Bool
              _lhsOmiscerrors :: ([Error])
              _lhsOnamesInScope :: Names
              _lhsOunboundNames :: Names
              _lhsOwarnings :: ([Warning])
              _rangeIself :: Range
              _lhsOcollectInstances =
                  []
              _self =
                  Statement_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOlastStatementIsExpr =
                  _lhsIlastStatementIsExpr
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOunboundNames =
                  _lhsIunboundNames
              _lhsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOlastStatementIsExpr,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Statement_Expression :: T_Range ->
                            T_Expression ->
                            T_Statement
sem_Statement_Expression range_ expression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsIlastStatementIsExpr
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _lhsOlastStatementIsExpr :: Bool
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statement
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOnamesInScope :: Names
              _lhsOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOnamesInScope :: Names
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              _lhsOunboundNames =
                  _expressionIunboundNames ++ _lhsIunboundNames
              _lhsOlastStatementIsExpr =
                  True
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _self =
                  Statement_Expression _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _expressionIcollectScopeInfos
              _lhsOkindErrors =
                  _expressionIkindErrors
              _lhsOmiscerrors =
                  _expressionImiscerrors
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOwarnings =
                  _expressionIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _lhsImiscerrors
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOlastStatementIsExpr,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Statement_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Statement
sem_Statement_Generator range_ pattern_ expression_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsIlastStatementIsExpr
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOnamesInScope :: Names
              _lhsOunboundNames :: Names
              _expressionOnamesInScope :: Names
              _lhsOlastStatementIsExpr :: Bool
              _patternOlhsPattern :: Bool
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statement
              _lhsOkindErrors :: ([Error])
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _patternOallTypeConstructors :: Names
              _patternOallValueConstructors :: Names
              _patternOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternOmiscerrors :: ([Error])
              _patternOnamesInScope :: Names
              _patternOtypeConstructors :: (M.Map Name Int)
              _patternOvalueConstructors :: (M.Map Name TpScheme)
              _patternOwarnings :: ([Warning])
              _expressionOallTypeConstructors :: Names
              _expressionOallValueConstructors :: Names
              _expressionOclassEnvironment :: ClassEnvironment
              _expressionOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionOkindErrors :: ([Error])
              _expressionOmiscerrors :: ([Error])
              _expressionOoptions :: ([Option])
              _expressionOorderedTypeSynonyms :: OrderedTypeSynonyms
              _expressionOtypeConstructors :: (M.Map Name Int)
              _expressionOvalueConstructors :: (M.Map Name TpScheme)
              _expressionOwarnings :: ([Warning])
              _rangeIself :: Range
              _patternIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _patternImiscerrors :: ([Error])
              _patternIpatVarNames :: Names
              _patternIself :: Pattern
              _patternIunboundNames :: Names
              _patternIwarnings :: ([Warning])
              _expressionIcollectInstances :: ([(Name, Instance)])
              _expressionIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _expressionIkindErrors :: ([Error])
              _expressionImiscerrors :: ([Error])
              _expressionIself :: Expression
              _expressionIunboundNames :: Names
              _expressionIwarnings :: ([Warning])
              __tup29 =
                  changeOfScope _patternIpatVarNames (_expressionIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup29
              (_,_unboundNames,_) =
                  __tup29
              (_,_,_scopeInfo) =
                  __tup29
              _lhsOnamesInScope =
                  _namesInScope
              _lhsOunboundNames =
                  _unboundNames
              _expressionOnamesInScope =
                  _lhsInamesInScope
              _lhsOlastStatementIsExpr =
                  False
              _patternOlhsPattern =
                  False
              _lhsOcollectScopeInfos =
                  (_scopeInfo, Variable)   : _expressionIcollectScopeInfos
              _lhsOcollectInstances =
                  _expressionIcollectInstances
              _self =
                  Statement_Generator _rangeIself _patternIself _expressionIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _expressionIkindErrors
              _lhsOmiscerrors =
                  _expressionImiscerrors
              _lhsOwarnings =
                  _expressionIwarnings
              _patternOallTypeConstructors =
                  _lhsIallTypeConstructors
              _patternOallValueConstructors =
                  _lhsIallValueConstructors
              _patternOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _patternOmiscerrors =
                  _lhsImiscerrors
              _patternOnamesInScope =
                  _namesInScope
              _patternOtypeConstructors =
                  _lhsItypeConstructors
              _patternOvalueConstructors =
                  _lhsIvalueConstructors
              _patternOwarnings =
                  _lhsIwarnings
              _expressionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _expressionOallValueConstructors =
                  _lhsIallValueConstructors
              _expressionOclassEnvironment =
                  _lhsIclassEnvironment
              _expressionOcollectScopeInfos =
                  _patternIcollectScopeInfos
              _expressionOkindErrors =
                  _lhsIkindErrors
              _expressionOmiscerrors =
                  _patternImiscerrors
              _expressionOoptions =
                  _lhsIoptions
              _expressionOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _expressionOtypeConstructors =
                  _lhsItypeConstructors
              _expressionOvalueConstructors =
                  _lhsIvalueConstructors
              _expressionOwarnings =
                  _patternIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _patternIcollectScopeInfos,_patternImiscerrors,_patternIpatVarNames,_patternIself,_patternIunboundNames,_patternIwarnings) =
                  (pattern_ _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings )
              ( _expressionIcollectInstances,_expressionIcollectScopeInfos,_expressionIkindErrors,_expressionImiscerrors,_expressionIself,_expressionIunboundNames,_expressionIwarnings) =
                  (expression_ _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOlastStatementIsExpr,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Statement_Let :: T_Range ->
                     T_Declarations ->
                     T_Statement
sem_Statement_Let range_ declarations_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsIlastStatementIsExpr
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _declarationsOtypeSignatures :: ([(Name,TpScheme)])
              _lhsOunboundNames :: Names
              _lhsOwarnings :: ([Warning])
              _declarationsOpreviousWasAlsoFB :: (Maybe Name)
              _declarationsOsuspiciousFBs :: ([(Name,Name)])
              _lhsOlastStatementIsExpr :: Bool
              _lhsOmiscerrors :: ([Error])
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statement
              _lhsOkindErrors :: ([Error])
              _lhsOnamesInScope :: Names
              _declarationsOallTypeConstructors :: Names
              _declarationsOallValueConstructors :: Names
              _declarationsOclassEnvironment :: ClassEnvironment
              _declarationsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _declarationsOcollectTypeConstructors :: ([(Name,Int)])
              _declarationsOcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _declarationsOcollectValueConstructors :: ([(Name,TpScheme)])
              _declarationsOkindErrors :: ([Error])
              _declarationsOmiscerrors :: ([Error])
              _declarationsOnamesInScope :: Names
              _declarationsOoperatorFixities :: ([(Name,(Int,Assoc))])
              _declarationsOoptions :: ([Option])
              _declarationsOorderedTypeSynonyms :: OrderedTypeSynonyms
              _declarationsOtypeConstructors :: (M.Map Name Int)
              _declarationsOvalueConstructors :: (M.Map Name TpScheme)
              _declarationsOwarnings :: ([Warning])
              _rangeIself :: Range
              _declarationsIcollectInstances :: ([(Name, Instance)])
              _declarationsIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _declarationsIcollectTypeConstructors :: ([(Name,Int)])
              _declarationsIcollectTypeSynonyms :: ([(Name,(Int,Tps -> Tp))])
              _declarationsIcollectValueConstructors :: ([(Name,TpScheme)])
              _declarationsIdeclVarNames :: Names
              _declarationsIkindErrors :: ([Error])
              _declarationsImiscerrors :: ([Error])
              _declarationsIoperatorFixities :: ([(Name,(Int,Assoc))])
              _declarationsIpreviousWasAlsoFB :: (Maybe Name)
              _declarationsIrestrictedNames :: Names
              _declarationsIself :: Declarations
              _declarationsIsuspiciousFBs :: ([(Name,Name)])
              _declarationsItypeSignatures :: ([(Name,TpScheme)])
              _declarationsIunboundNames :: Names
              _declarationsIwarnings :: ([Warning])
              _declarationsOtypeSignatures =
                  []
              __tup30 =
                  changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
              (_namesInScope,_,_) =
                  __tup30
              (_,_unboundNames,_) =
                  __tup30
              (_,_,_scopeInfo) =
                  __tup30
              _lhsOunboundNames =
                  _unboundNames
              _lhsOwarnings =
                  _declarationsIwarnings ++
                  _suspiciousErrors
              _declarationsOpreviousWasAlsoFB =
                  Nothing
              _declarationsOsuspiciousFBs =
                  []
              _suspiciousErrors =
                  findSimilarFunctionBindings _declarationsItypeSignatures _declarationsIsuspiciousFBs
              _lhsOlastStatementIsExpr =
                  False
              _lhsOmiscerrors =
                  _typeSignatureErrors ++ _declarationsImiscerrors
              __tup31 =
                  uniqueAppearance (map fst _declarationsItypeSignatures)
              (_,_doubles) =
                  __tup31
              _typeSignatureErrors =
                  checkTypeSignatures _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
              __tup32 =
                  internalError "PartialSyntax.ag" "n/a" "toplevel Statement"
              (_collectTypeConstructors,_,_,_,_,_) =
                  __tup32
              (_,_collectValueConstructors,_,_,_,_) =
                  __tup32
              (_,_,_collectTypeSynonyms,_,_,_) =
                  __tup32
              (_,_,_,_collectConstructorEnv,_,_) =
                  __tup32
              (_,_,_,_,_derivedFunctions,_) =
                  __tup32
              (_,_,_,_,_,_operatorFixities) =
                  __tup32
              _lhsOcollectScopeInfos =
                  (_scopeInfo, Definition) : _declarationsIcollectScopeInfos
              _lhsOcollectInstances =
                  _declarationsIcollectInstances
              _self =
                  Statement_Let _rangeIself _declarationsIself
              _lhsOself =
                  _self
              _lhsOkindErrors =
                  _declarationsIkindErrors
              _lhsOnamesInScope =
                  _namesInScope
              _declarationsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _declarationsOallValueConstructors =
                  _lhsIallValueConstructors
              _declarationsOclassEnvironment =
                  _lhsIclassEnvironment
              _declarationsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _declarationsOcollectTypeConstructors =
                  _collectTypeConstructors
              _declarationsOcollectTypeSynonyms =
                  _collectTypeSynonyms
              _declarationsOcollectValueConstructors =
                  _collectValueConstructors
              _declarationsOkindErrors =
                  _lhsIkindErrors
              _declarationsOmiscerrors =
                  _lhsImiscerrors
              _declarationsOnamesInScope =
                  _namesInScope
              _declarationsOoperatorFixities =
                  _operatorFixities
              _declarationsOoptions =
                  _lhsIoptions
              _declarationsOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _declarationsOtypeConstructors =
                  _lhsItypeConstructors
              _declarationsOvalueConstructors =
                  _lhsIvalueConstructors
              _declarationsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _declarationsIcollectInstances,_declarationsIcollectScopeInfos,_declarationsIcollectTypeConstructors,_declarationsIcollectTypeSynonyms,_declarationsIcollectValueConstructors,_declarationsIdeclVarNames,_declarationsIkindErrors,_declarationsImiscerrors,_declarationsIoperatorFixities,_declarationsIpreviousWasAlsoFB,_declarationsIrestrictedNames,_declarationsIself,_declarationsIsuspiciousFBs,_declarationsItypeSignatures,_declarationsIunboundNames,_declarationsIwarnings) =
                  (declarations_ _declarationsOallTypeConstructors _declarationsOallValueConstructors _declarationsOclassEnvironment _declarationsOcollectScopeInfos _declarationsOcollectTypeConstructors _declarationsOcollectTypeSynonyms _declarationsOcollectValueConstructors _declarationsOkindErrors _declarationsOmiscerrors _declarationsOnamesInScope _declarationsOoperatorFixities _declarationsOoptions _declarationsOorderedTypeSynonyms _declarationsOpreviousWasAlsoFB _declarationsOsuspiciousFBs _declarationsOtypeConstructors _declarationsOtypeSignatures _declarationsOvalueConstructors _declarationsOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOlastStatementIsExpr,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- Statements --------------------------------------------------
-- cata
sem_Statements :: Statements ->
                  T_Statements
sem_Statements list  =
    (Prelude.foldr sem_Statements_Cons sem_Statements_Nil (Prelude.map sem_Statement list) )
-- semantic domain
type T_Statements = Names ->
                    Names ->
                    ClassEnvironment ->
                    ([(ScopeInfo, Entity)]) ->
                    ([Error]) ->
                    Bool ->
                    ([Error]) ->
                    Names ->
                    ([Option]) ->
                    OrderedTypeSynonyms ->
                    (M.Map Name Int) ->
                    Names ->
                    (M.Map Name TpScheme) ->
                    ([Warning]) ->
                    ( ([(Name, Instance)]),([(ScopeInfo, Entity)]),([Error]),Bool,([Error]),Names,Statements,Names,([Warning]))
sem_Statements_Cons :: T_Statement ->
                       T_Statements ->
                       T_Statements
sem_Statements_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsIlastStatementIsExpr
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _tlOunboundNames :: Names
              _hdOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statements
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOlastStatementIsExpr :: Bool
              _lhsOmiscerrors :: ([Error])
              _lhsOnamesInScope :: Names
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOallValueConstructors :: Names
              _hdOclassEnvironment :: ClassEnvironment
              _hdOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdOkindErrors :: ([Error])
              _hdOlastStatementIsExpr :: Bool
              _hdOmiscerrors :: ([Error])
              _hdOnamesInScope :: Names
              _hdOoptions :: ([Option])
              _hdOorderedTypeSynonyms :: OrderedTypeSynonyms
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOvalueConstructors :: (M.Map Name TpScheme)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOallValueConstructors :: Names
              _tlOclassEnvironment :: ClassEnvironment
              _tlOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlOkindErrors :: ([Error])
              _tlOlastStatementIsExpr :: Bool
              _tlOmiscerrors :: ([Error])
              _tlOnamesInScope :: Names
              _tlOoptions :: ([Option])
              _tlOorderedTypeSynonyms :: OrderedTypeSynonyms
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOvalueConstructors :: (M.Map Name TpScheme)
              _tlOwarnings :: ([Warning])
              _hdIcollectInstances :: ([(Name, Instance)])
              _hdIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _hdIkindErrors :: ([Error])
              _hdIlastStatementIsExpr :: Bool
              _hdImiscerrors :: ([Error])
              _hdInamesInScope :: Names
              _hdIself :: Statement
              _hdIunboundNames :: Names
              _hdIwarnings :: ([Warning])
              _tlIcollectInstances :: ([(Name, Instance)])
              _tlIcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _tlIkindErrors :: ([Error])
              _tlIlastStatementIsExpr :: Bool
              _tlImiscerrors :: ([Error])
              _tlInamesInScope :: Names
              _tlIself :: Statements
              _tlIunboundNames :: Names
              _tlIwarnings :: ([Warning])
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
              _lhsOcollectScopeInfos =
                  _tlIcollectScopeInfos
              _lhsOkindErrors =
                  _tlIkindErrors
              _lhsOlastStatementIsExpr =
                  _tlIlastStatementIsExpr
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOnamesInScope =
                  _tlInamesInScope
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOallValueConstructors =
                  _lhsIallValueConstructors
              _hdOclassEnvironment =
                  _lhsIclassEnvironment
              _hdOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _hdOkindErrors =
                  _lhsIkindErrors
              _hdOlastStatementIsExpr =
                  _lhsIlastStatementIsExpr
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOnamesInScope =
                  _lhsInamesInScope
              _hdOoptions =
                  _lhsIoptions
              _hdOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOvalueConstructors =
                  _lhsIvalueConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOallValueConstructors =
                  _lhsIallValueConstructors
              _tlOclassEnvironment =
                  _lhsIclassEnvironment
              _tlOcollectScopeInfos =
                  _hdIcollectScopeInfos
              _tlOkindErrors =
                  _hdIkindErrors
              _tlOlastStatementIsExpr =
                  _hdIlastStatementIsExpr
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOnamesInScope =
                  _hdInamesInScope
              _tlOoptions =
                  _lhsIoptions
              _tlOorderedTypeSynonyms =
                  _lhsIorderedTypeSynonyms
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOvalueConstructors =
                  _lhsIvalueConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIcollectInstances,_hdIcollectScopeInfos,_hdIkindErrors,_hdIlastStatementIsExpr,_hdImiscerrors,_hdInamesInScope,_hdIself,_hdIunboundNames,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOkindErrors _hdOlastStatementIsExpr _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOunboundNames _hdOvalueConstructors _hdOwarnings )
              ( _tlIcollectInstances,_tlIcollectScopeInfos,_tlIkindErrors,_tlIlastStatementIsExpr,_tlImiscerrors,_tlInamesInScope,_tlIself,_tlIunboundNames,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOkindErrors _tlOlastStatementIsExpr _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOunboundNames _tlOvalueConstructors _tlOwarnings )
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOlastStatementIsExpr,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
sem_Statements_Nil :: T_Statements
sem_Statements_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsIallValueConstructors
       _lhsIclassEnvironment
       _lhsIcollectScopeInfos
       _lhsIkindErrors
       _lhsIlastStatementIsExpr
       _lhsImiscerrors
       _lhsInamesInScope
       _lhsIoptions
       _lhsIorderedTypeSynonyms
       _lhsItypeConstructors
       _lhsIunboundNames
       _lhsIvalueConstructors
       _lhsIwarnings ->
         (let _lhsOunboundNames :: Names
              _lhsOcollectInstances :: ([(Name, Instance)])
              _lhsOself :: Statements
              _lhsOcollectScopeInfos :: ([(ScopeInfo, Entity)])
              _lhsOkindErrors :: ([Error])
              _lhsOlastStatementIsExpr :: Bool
              _lhsOmiscerrors :: ([Error])
              _lhsOnamesInScope :: Names
              _lhsOwarnings :: ([Warning])
              _lhsOunboundNames =
                  _lhsIunboundNames
              _lhsOcollectInstances =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOcollectScopeInfos =
                  _lhsIcollectScopeInfos
              _lhsOkindErrors =
                  _lhsIkindErrors
              _lhsOlastStatementIsExpr =
                  _lhsIlastStatementIsExpr
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOnamesInScope =
                  _lhsInamesInScope
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOcollectInstances,_lhsOcollectScopeInfos,_lhsOkindErrors,_lhsOlastStatementIsExpr,_lhsOmiscerrors,_lhsOnamesInScope,_lhsOself,_lhsOunboundNames,_lhsOwarnings)))
-- Strings -----------------------------------------------------
-- cata
sem_Strings :: Strings ->
               T_Strings
sem_Strings list  =
    (Prelude.foldr sem_Strings_Cons sem_Strings_Nil list )
-- semantic domain
type T_Strings = ( Strings)
sem_Strings_Cons :: String ->
                    T_Strings ->
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
sem_Type :: Type ->
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
type T_Type = Names ->
              ([Error]) ->
              ([Option]) ->
              (M.Map Name Int) ->
              ([Warning]) ->
              ( Range,([Error]),Type,Names,([Warning]))
sem_Type_Application :: T_Range ->
                        Bool ->
                        T_Type ->
                        T_Types ->
                        T_Type
sem_Type_Application range_ prefix_ function_ arguments_  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOtypevariables :: Names
              _lhsOself :: Type
              _lhsOcontextRange :: Range
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _functionOallTypeConstructors :: Names
              _functionOmiscerrors :: ([Error])
              _functionOoptions :: ([Option])
              _functionOtypeConstructors :: (M.Map Name Int)
              _functionOwarnings :: ([Warning])
              _argumentsOallTypeConstructors :: Names
              _argumentsOmiscerrors :: ([Error])
              _argumentsOoptions :: ([Option])
              _argumentsOtypeConstructors :: (M.Map Name Int)
              _argumentsOwarnings :: ([Warning])
              _rangeIself :: Range
              _functionIcontextRange :: Range
              _functionImiscerrors :: ([Error])
              _functionIself :: Type
              _functionItypevariables :: Names
              _functionIwarnings :: ([Warning])
              _argumentsImiscerrors :: ([Error])
              _argumentsIself :: Types
              _argumentsItypevariables :: Names
              _argumentsIwarnings :: ([Warning])
              _lhsOtypevariables =
                  _functionItypevariables  ++  _argumentsItypevariables
              _self =
                  Type_Application _rangeIself prefix_ _functionIself _argumentsIself
              _lhsOself =
                  _self
              _lhsOcontextRange =
                  _functionIcontextRange
              _lhsOmiscerrors =
                  _argumentsImiscerrors
              _lhsOwarnings =
                  _argumentsIwarnings
              _functionOallTypeConstructors =
                  _lhsIallTypeConstructors
              _functionOmiscerrors =
                  _lhsImiscerrors
              _functionOoptions =
                  _lhsIoptions
              _functionOtypeConstructors =
                  _lhsItypeConstructors
              _functionOwarnings =
                  _lhsIwarnings
              _argumentsOallTypeConstructors =
                  _lhsIallTypeConstructors
              _argumentsOmiscerrors =
                  _functionImiscerrors
              _argumentsOoptions =
                  _lhsIoptions
              _argumentsOtypeConstructors =
                  _lhsItypeConstructors
              _argumentsOwarnings =
                  _functionIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _functionIcontextRange,_functionImiscerrors,_functionIself,_functionItypevariables,_functionIwarnings) =
                  (function_ _functionOallTypeConstructors _functionOmiscerrors _functionOoptions _functionOtypeConstructors _functionOwarnings )
              ( _argumentsImiscerrors,_argumentsIself,_argumentsItypevariables,_argumentsIwarnings) =
                  (arguments_ _argumentsOallTypeConstructors _argumentsOmiscerrors _argumentsOoptions _argumentsOtypeConstructors _argumentsOwarnings )
          in  ( _lhsOcontextRange,_lhsOmiscerrors,_lhsOself,_lhsOtypevariables,_lhsOwarnings)))
sem_Type_Constructor :: T_Range ->
                        T_Name ->
                        T_Type
sem_Type_Constructor range_ name_  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOcontextRange :: Range
              _lhsOtypevariables :: Names
              _lhsOself :: Type
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOcontextRange =
                  noRange
              _lhsOtypevariables =
                  []
              _self =
                  Type_Constructor _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOcontextRange,_lhsOmiscerrors,_lhsOself,_lhsOtypevariables,_lhsOwarnings)))
sem_Type_Exists :: T_Range ->
                   T_Names ->
                   T_Type ->
                   T_Type
sem_Type_Exists range_ typevariables_ type_  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOtypevariables :: Names
              _lhsOself :: Type
              _lhsOcontextRange :: Range
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _typeOallTypeConstructors :: Names
              _typeOmiscerrors :: ([Error])
              _typeOoptions :: ([Option])
              _typeOtypeConstructors :: (M.Map Name Int)
              _typeOwarnings :: ([Warning])
              _rangeIself :: Range
              _typevariablesIself :: Names
              _typeIcontextRange :: Range
              _typeImiscerrors :: ([Error])
              _typeIself :: Type
              _typeItypevariables :: Names
              _typeIwarnings :: ([Warning])
              _lhsOtypevariables =
                  _typeItypevariables
              _self =
                  Type_Exists _rangeIself _typevariablesIself _typeIself
              _lhsOself =
                  _self
              _lhsOcontextRange =
                  _typeIcontextRange
              _lhsOmiscerrors =
                  _typeImiscerrors
              _lhsOwarnings =
                  _typeIwarnings
              _typeOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typeOmiscerrors =
                  _lhsImiscerrors
              _typeOoptions =
                  _lhsIoptions
              _typeOtypeConstructors =
                  _lhsItypeConstructors
              _typeOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _typevariablesIself) =
                  (typevariables_ )
              ( _typeIcontextRange,_typeImiscerrors,_typeIself,_typeItypevariables,_typeIwarnings) =
                  (type_ _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings )
          in  ( _lhsOcontextRange,_lhsOmiscerrors,_lhsOself,_lhsOtypevariables,_lhsOwarnings)))
sem_Type_Forall :: T_Range ->
                   T_Names ->
                   T_Type ->
                   T_Type
sem_Type_Forall range_ typevariables_ type_  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOtypevariables :: Names
              _lhsOself :: Type
              _lhsOcontextRange :: Range
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _typeOallTypeConstructors :: Names
              _typeOmiscerrors :: ([Error])
              _typeOoptions :: ([Option])
              _typeOtypeConstructors :: (M.Map Name Int)
              _typeOwarnings :: ([Warning])
              _rangeIself :: Range
              _typevariablesIself :: Names
              _typeIcontextRange :: Range
              _typeImiscerrors :: ([Error])
              _typeIself :: Type
              _typeItypevariables :: Names
              _typeIwarnings :: ([Warning])
              _lhsOtypevariables =
                  _typeItypevariables
              _self =
                  Type_Forall _rangeIself _typevariablesIself _typeIself
              _lhsOself =
                  _self
              _lhsOcontextRange =
                  _typeIcontextRange
              _lhsOmiscerrors =
                  _typeImiscerrors
              _lhsOwarnings =
                  _typeIwarnings
              _typeOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typeOmiscerrors =
                  _lhsImiscerrors
              _typeOoptions =
                  _lhsIoptions
              _typeOtypeConstructors =
                  _lhsItypeConstructors
              _typeOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _typevariablesIself) =
                  (typevariables_ )
              ( _typeIcontextRange,_typeImiscerrors,_typeIself,_typeItypevariables,_typeIwarnings) =
                  (type_ _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings )
          in  ( _lhsOcontextRange,_lhsOmiscerrors,_lhsOself,_lhsOtypevariables,_lhsOwarnings)))
sem_Type_Parenthesized :: T_Range ->
                          T_Type ->
                          T_Type
sem_Type_Parenthesized range_ type_  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOtypevariables :: Names
              _lhsOself :: Type
              _lhsOcontextRange :: Range
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _typeOallTypeConstructors :: Names
              _typeOmiscerrors :: ([Error])
              _typeOoptions :: ([Option])
              _typeOtypeConstructors :: (M.Map Name Int)
              _typeOwarnings :: ([Warning])
              _rangeIself :: Range
              _typeIcontextRange :: Range
              _typeImiscerrors :: ([Error])
              _typeIself :: Type
              _typeItypevariables :: Names
              _typeIwarnings :: ([Warning])
              _lhsOtypevariables =
                  _typeItypevariables
              _self =
                  Type_Parenthesized _rangeIself _typeIself
              _lhsOself =
                  _self
              _lhsOcontextRange =
                  _typeIcontextRange
              _lhsOmiscerrors =
                  _typeImiscerrors
              _lhsOwarnings =
                  _typeIwarnings
              _typeOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typeOmiscerrors =
                  _lhsImiscerrors
              _typeOoptions =
                  _lhsIoptions
              _typeOtypeConstructors =
                  _lhsItypeConstructors
              _typeOwarnings =
                  _lhsIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _typeIcontextRange,_typeImiscerrors,_typeIself,_typeItypevariables,_typeIwarnings) =
                  (type_ _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings )
          in  ( _lhsOcontextRange,_lhsOmiscerrors,_lhsOself,_lhsOtypevariables,_lhsOwarnings)))
sem_Type_Qualified :: T_Range ->
                      T_ContextItems ->
                      T_Type ->
                      T_Type
sem_Type_Qualified range_ context_ type_  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOcontextRange :: Range
              _lhsOmiscerrors :: ([Error])
              _lhsOtypevariables :: Names
              _lhsOself :: Type
              _lhsOwarnings :: ([Warning])
              _contextOallTypeConstructors :: Names
              _contextOmiscerrors :: ([Error])
              _contextOoptions :: ([Option])
              _contextOtypeConstructors :: (M.Map Name Int)
              _contextOwarnings :: ([Warning])
              _typeOallTypeConstructors :: Names
              _typeOmiscerrors :: ([Error])
              _typeOoptions :: ([Option])
              _typeOtypeConstructors :: (M.Map Name Int)
              _typeOwarnings :: ([Warning])
              _rangeIself :: Range
              _contextIcontextRanges :: ([Range])
              _contextIcontextVars :: ([Name])
              _contextImiscerrors :: ([Error])
              _contextIself :: ContextItems
              _contextIwarnings :: ([Warning])
              _typeIcontextRange :: Range
              _typeImiscerrors :: ([Error])
              _typeIself :: Type
              _typeItypevariables :: Names
              _typeIwarnings :: ([Warning])
              _lhsOcontextRange =
                  if null _contextIcontextRanges
                    then noRange
                    else foldr1 mergeRanges _contextIcontextRanges
              _lhsOmiscerrors =
                  ( if Overloading `elem` _lhsIoptions then
                      [ AmbiguousContext v | v <-  _contextIcontextVars, v `notElem` _typeItypevariables ]
                    else
                      [ OverloadingDisabled _rangeIself ]
                  )
                  ++
                  _typeImiscerrors
              _lhsOtypevariables =
                  _typeItypevariables
              _self =
                  Type_Qualified _rangeIself _contextIself _typeIself
              _lhsOself =
                  _self
              _lhsOwarnings =
                  _typeIwarnings
              _contextOallTypeConstructors =
                  _lhsIallTypeConstructors
              _contextOmiscerrors =
                  _lhsImiscerrors
              _contextOoptions =
                  _lhsIoptions
              _contextOtypeConstructors =
                  _lhsItypeConstructors
              _contextOwarnings =
                  _lhsIwarnings
              _typeOallTypeConstructors =
                  _lhsIallTypeConstructors
              _typeOmiscerrors =
                  _contextImiscerrors
              _typeOoptions =
                  _lhsIoptions
              _typeOtypeConstructors =
                  _lhsItypeConstructors
              _typeOwarnings =
                  _contextIwarnings
              ( _rangeIself) =
                  (range_ )
              ( _contextIcontextRanges,_contextIcontextVars,_contextImiscerrors,_contextIself,_contextIwarnings) =
                  (context_ _contextOallTypeConstructors _contextOmiscerrors _contextOoptions _contextOtypeConstructors _contextOwarnings )
              ( _typeIcontextRange,_typeImiscerrors,_typeIself,_typeItypevariables,_typeIwarnings) =
                  (type_ _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings )
          in  ( _lhsOcontextRange,_lhsOmiscerrors,_lhsOself,_lhsOtypevariables,_lhsOwarnings)))
sem_Type_Variable :: T_Range ->
                     T_Name ->
                     T_Type
sem_Type_Variable range_ name_  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOtypevariables :: Names
              _lhsOwarnings :: ([Warning])
              _lhsOcontextRange :: Range
              _lhsOself :: Type
              _lhsOmiscerrors :: ([Error])
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOtypevariables =
                  [ _nameIself ]
              _lhsOwarnings =
                  let xs = [ SuspiciousTypeVariable _nameIself tc
                           | length (show _nameIself) > 1
                           , tc <- _lhsIallTypeConstructors
                           , capitalize (show _nameIself) == (show tc)
                           ]
                  in xs ++ _lhsIwarnings
              _lhsOcontextRange =
                  noRange
              _self =
                  Type_Variable _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsOmiscerrors =
                  _lhsImiscerrors
              ( _rangeIself) =
                  (range_ )
              ( _nameIself) =
                  (name_ )
          in  ( _lhsOcontextRange,_lhsOmiscerrors,_lhsOself,_lhsOtypevariables,_lhsOwarnings)))
-- Types -------------------------------------------------------
-- cata
sem_Types :: Types ->
             T_Types
sem_Types list  =
    (Prelude.foldr sem_Types_Cons sem_Types_Nil (Prelude.map sem_Type list) )
-- semantic domain
type T_Types = Names ->
               ([Error]) ->
               ([Option]) ->
               (M.Map Name Int) ->
               ([Warning]) ->
               ( ([Error]),Types,Names,([Warning]))
sem_Types_Cons :: T_Type ->
                  T_Types ->
                  T_Types
sem_Types_Cons hd_ tl_  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOtypevariables :: Names
              _lhsOself :: Types
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _hdOallTypeConstructors :: Names
              _hdOmiscerrors :: ([Error])
              _hdOoptions :: ([Option])
              _hdOtypeConstructors :: (M.Map Name Int)
              _hdOwarnings :: ([Warning])
              _tlOallTypeConstructors :: Names
              _tlOmiscerrors :: ([Error])
              _tlOoptions :: ([Option])
              _tlOtypeConstructors :: (M.Map Name Int)
              _tlOwarnings :: ([Warning])
              _hdIcontextRange :: Range
              _hdImiscerrors :: ([Error])
              _hdIself :: Type
              _hdItypevariables :: Names
              _hdIwarnings :: ([Warning])
              _tlImiscerrors :: ([Error])
              _tlIself :: Types
              _tlItypevariables :: Names
              _tlIwarnings :: ([Warning])
              _lhsOtypevariables =
                  _hdItypevariables  ++  _tlItypevariables
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOmiscerrors =
                  _tlImiscerrors
              _lhsOwarnings =
                  _tlIwarnings
              _hdOallTypeConstructors =
                  _lhsIallTypeConstructors
              _hdOmiscerrors =
                  _lhsImiscerrors
              _hdOoptions =
                  _lhsIoptions
              _hdOtypeConstructors =
                  _lhsItypeConstructors
              _hdOwarnings =
                  _lhsIwarnings
              _tlOallTypeConstructors =
                  _lhsIallTypeConstructors
              _tlOmiscerrors =
                  _hdImiscerrors
              _tlOoptions =
                  _lhsIoptions
              _tlOtypeConstructors =
                  _lhsItypeConstructors
              _tlOwarnings =
                  _hdIwarnings
              ( _hdIcontextRange,_hdImiscerrors,_hdIself,_hdItypevariables,_hdIwarnings) =
                  (hd_ _hdOallTypeConstructors _hdOmiscerrors _hdOoptions _hdOtypeConstructors _hdOwarnings )
              ( _tlImiscerrors,_tlIself,_tlItypevariables,_tlIwarnings) =
                  (tl_ _tlOallTypeConstructors _tlOmiscerrors _tlOoptions _tlOtypeConstructors _tlOwarnings )
          in  ( _lhsOmiscerrors,_lhsOself,_lhsOtypevariables,_lhsOwarnings)))
sem_Types_Nil :: T_Types
sem_Types_Nil  =
    (\ _lhsIallTypeConstructors
       _lhsImiscerrors
       _lhsIoptions
       _lhsItypeConstructors
       _lhsIwarnings ->
         (let _lhsOtypevariables :: Names
              _lhsOself :: Types
              _lhsOmiscerrors :: ([Error])
              _lhsOwarnings :: ([Warning])
              _lhsOtypevariables =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOmiscerrors =
                  _lhsImiscerrors
              _lhsOwarnings =
                  _lhsIwarnings
          in  ( _lhsOmiscerrors,_lhsOself,_lhsOtypevariables,_lhsOwarnings)))