{-# LANGUAGE Rank2Types, GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Helium.StaticAnalysis.StaticChecks.StaticChecks where

import Helium.Utils.Similarity ( similar )
import Helium.Main.Args
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import Helium.Syntax.UHA_Range
import Top.Types

import Helium.StaticAnalysis.Messages.StaticErrors
import Helium.StaticAnalysis.Messages.Warnings
import Helium.StaticAnalysis.Messages.Messages
import Data.List
import Helium.Utils.Utils ( internalError, minInt, maxInt )
import Helium.StaticAnalysis.Miscellaneous.TypeConversion
import Helium.CodeGeneration.DerivingShow

import qualified Data.Map as M

import Helium.ModuleSystem.ImportEnvironment
import Helium.Parser.OperatorTable
import Data.Char ( isUpper )

import Control.Monad.Identity (Identity)
import qualified Control.Monad.Identity

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
uniqueAppearance = Prelude.foldr myInsert ([],[]) . group . sort
   where myInsert [x] (as,bs) = (x:as,bs)
         myInsert xs  (as,bs) = (as,xs:bs)
       
nextUnique :: Num a => a -> (a, a)         
nextUnique n = (n+1, n)


checkType :: M.Map Name Int -> Names -> Type -> [Error]
checkType theTypeConstructors namesInScope t =
    let (f, xs) = walkSpine t
        xsErrors = concatMap (checkType theTypeConstructors namesInScope) xs
    in
        xsErrors
        ++
        case f of
            Type_Constructor r c ->
                checkKind c theTypeConstructors (length xs) namesInScope
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
            let (t', ys) = walkSpine f
            in (t', ys ++ xs)
        Type_Parenthesized _ t' -> walkSpine t'
        Type_Qualified _ _ t' -> walkSpine t'
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

checkKind tycon theTypeConstructors useArity namesInScope =
    case M.lookup tycon theTypeConstructors of
        Nothing ->
            let hint = [ "Constructor "++show (show tycon)++" cannot be used in a type"
                       | tycon `elem` namesInScope
                       ]
            in [ Undefined TypeConstructor tycon (M.keys theTypeConstructors) hint ]
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



checkExport :: Entity -> Name -> [Name] -> [Error]
checkExport entity name inScope =
    makeUndefined entity
        (if name `elem` inScope then
            []
         else
            [name]
        )
        (nubBy equalName inScope)

equalName :: Name -> Name -> Bool       
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
-- wrapper
data Inh_Alternative  = Inh_Alternative { allTypeConstructors_Inh_Alternative :: (Names), allValueConstructors_Inh_Alternative :: (Names), classEnvironment_Inh_Alternative :: (ClassEnvironment), collectScopeInfos_Inh_Alternative :: ([(ScopeInfo, Entity)]), counter_Inh_Alternative :: (Int), kindErrors_Inh_Alternative :: ([Error]), miscerrors_Inh_Alternative :: ([Error]), namesInScope_Inh_Alternative :: (Names), options_Inh_Alternative :: ([Option]), orderedTypeSynonyms_Inh_Alternative :: (OrderedTypeSynonyms), typeConstructors_Inh_Alternative :: (M.Map Name Int), valueConstructors_Inh_Alternative :: (M.Map Name TpScheme), warnings_Inh_Alternative :: ([Warning]) }
data Syn_Alternative  = Syn_Alternative { collectInstances_Syn_Alternative :: ([(Name, Instance)]), collectScopeInfos_Syn_Alternative :: ([(ScopeInfo, Entity)]), counter_Syn_Alternative :: (Int), kindErrors_Syn_Alternative :: ([Error]), miscerrors_Syn_Alternative :: ([Error]), self_Syn_Alternative :: (Alternative), unboundNames_Syn_Alternative :: (Names), warnings_Syn_Alternative :: ([Warning]) }
{-# INLINABLE wrap_Alternative #-}
wrap_Alternative :: T_Alternative  -> Inh_Alternative  -> (Syn_Alternative )
wrap_Alternative (T_Alternative act) (Inh_Alternative _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Alternative_vIn1 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_Alternative_vOut1 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_Alternative_s2 sem arg)
        return (Syn_Alternative _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Alternative #-}
sem_Alternative :: Alternative  -> T_Alternative 
sem_Alternative ( Alternative_Hole range_ id_ ) = sem_Alternative_Hole ( sem_Range range_ ) id_
sem_Alternative ( Alternative_Feedback range_ feedback_ alternative_ ) = sem_Alternative_Feedback ( sem_Range range_ ) feedback_ ( sem_Alternative alternative_ )
sem_Alternative ( Alternative_Alternative range_ pattern_ righthandside_ ) = sem_Alternative_Alternative ( sem_Range range_ ) ( sem_Pattern pattern_ ) ( sem_RightHandSide righthandside_ )
sem_Alternative ( Alternative_Empty range_ ) = sem_Alternative_Empty ( sem_Range range_ )

-- semantic domain
newtype T_Alternative  = T_Alternative {
                                       attach_T_Alternative :: Identity (T_Alternative_s2 )
                                       }
newtype T_Alternative_s2  = C_Alternative_s2 {
                                             inv_Alternative_s2 :: (T_Alternative_v1 )
                                             }
data T_Alternative_s3  = C_Alternative_s3
type T_Alternative_v1  = (T_Alternative_vIn1 ) -> (T_Alternative_vOut1 )
data T_Alternative_vIn1  = T_Alternative_vIn1 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_Alternative_vOut1  = T_Alternative_vOut1 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Alternative) (Names) ([Warning])
{-# NOINLINE sem_Alternative_Hole #-}
sem_Alternative_Hole :: T_Range  -> (Integer) -> T_Alternative 
sem_Alternative_Hole arg_range_ arg_id_ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule0  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1  ()
         _self = rule2 _rangeIself arg_id_
         _lhsOself :: Alternative
         _lhsOself = rule3 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule4 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule5 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule6 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule7 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule8 _lhsIwarnings
         __result_ = T_Alternative_vOut1 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule0 #-}
   rule0 = \  (_ :: ()) ->
     []
   {-# INLINE rule1 #-}
   rule1 = \  (_ :: ()) ->
     []
   {-# INLINE rule2 #-}
   rule2 = \ ((_rangeIself) :: Range) id_ ->
     Alternative_Hole _rangeIself id_
   {-# INLINE rule3 #-}
   rule3 = \ _self ->
     _self
   {-# INLINE rule4 #-}
   rule4 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule5 #-}
   rule5 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule6 #-}
   rule6 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule7 #-}
   rule7 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule8 #-}
   rule8 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Alternative_Feedback #-}
sem_Alternative_Feedback :: T_Range  -> (String) -> T_Alternative  -> T_Alternative 
sem_Alternative_Feedback arg_range_ arg_feedback_ arg_alternative_ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _alternativeX2 = Control.Monad.Identity.runIdentity (attach_T_Alternative (arg_alternative_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Alternative_vOut1 _alternativeIcollectInstances _alternativeIcollectScopeInfos _alternativeIcounter _alternativeIkindErrors _alternativeImiscerrors _alternativeIself _alternativeIunboundNames _alternativeIwarnings) = inv_Alternative_s2 _alternativeX2 (T_Alternative_vIn1 _alternativeOallTypeConstructors _alternativeOallValueConstructors _alternativeOclassEnvironment _alternativeOcollectScopeInfos _alternativeOcounter _alternativeOkindErrors _alternativeOmiscerrors _alternativeOnamesInScope _alternativeOoptions _alternativeOorderedTypeSynonyms _alternativeOtypeConstructors _alternativeOvalueConstructors _alternativeOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule9 _alternativeIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule10 _alternativeIunboundNames
         _self = rule11 _alternativeIself _rangeIself arg_feedback_
         _lhsOself :: Alternative
         _lhsOself = rule12 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule13 _alternativeIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule14 _alternativeIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule15 _alternativeIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule16 _alternativeImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule17 _alternativeIwarnings
         _alternativeOallTypeConstructors = rule18 _lhsIallTypeConstructors
         _alternativeOallValueConstructors = rule19 _lhsIallValueConstructors
         _alternativeOclassEnvironment = rule20 _lhsIclassEnvironment
         _alternativeOcollectScopeInfos = rule21 _lhsIcollectScopeInfos
         _alternativeOcounter = rule22 _lhsIcounter
         _alternativeOkindErrors = rule23 _lhsIkindErrors
         _alternativeOmiscerrors = rule24 _lhsImiscerrors
         _alternativeOnamesInScope = rule25 _lhsInamesInScope
         _alternativeOoptions = rule26 _lhsIoptions
         _alternativeOorderedTypeSynonyms = rule27 _lhsIorderedTypeSynonyms
         _alternativeOtypeConstructors = rule28 _lhsItypeConstructors
         _alternativeOvalueConstructors = rule29 _lhsIvalueConstructors
         _alternativeOwarnings = rule30 _lhsIwarnings
         __result_ = T_Alternative_vOut1 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule9 #-}
   rule9 = \ ((_alternativeIcollectInstances) :: [(Name, Instance)]) ->
     _alternativeIcollectInstances
   {-# INLINE rule10 #-}
   rule10 = \ ((_alternativeIunboundNames) :: Names) ->
     _alternativeIunboundNames
   {-# INLINE rule11 #-}
   rule11 = \ ((_alternativeIself) :: Alternative) ((_rangeIself) :: Range) feedback_ ->
     Alternative_Feedback _rangeIself feedback_ _alternativeIself
   {-# INLINE rule12 #-}
   rule12 = \ _self ->
     _self
   {-# INLINE rule13 #-}
   rule13 = \ ((_alternativeIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _alternativeIcollectScopeInfos
   {-# INLINE rule14 #-}
   rule14 = \ ((_alternativeIcounter) :: Int) ->
     _alternativeIcounter
   {-# INLINE rule15 #-}
   rule15 = \ ((_alternativeIkindErrors) :: [Error]) ->
     _alternativeIkindErrors
   {-# INLINE rule16 #-}
   rule16 = \ ((_alternativeImiscerrors) :: [Error]) ->
     _alternativeImiscerrors
   {-# INLINE rule17 #-}
   rule17 = \ ((_alternativeIwarnings) :: [Warning]) ->
     _alternativeIwarnings
   {-# INLINE rule18 #-}
   rule18 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule19 #-}
   rule19 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule20 #-}
   rule20 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule21 #-}
   rule21 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule22 #-}
   rule22 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule23 #-}
   rule23 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule24 #-}
   rule24 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule25 #-}
   rule25 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule26 #-}
   rule26 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule27 #-}
   rule27 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule28 #-}
   rule28 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule29 #-}
   rule29 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule30 #-}
   rule30 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Alternative_Alternative #-}
sem_Alternative_Alternative :: T_Range  -> T_Pattern  -> T_RightHandSide  -> T_Alternative 
sem_Alternative_Alternative arg_range_ arg_pattern_ arg_righthandside_ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _righthandsideX149 = Control.Monad.Identity.runIdentity (attach_T_RightHandSide (arg_righthandside_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIcollectScopeInfos _patternIcounter _patternImiscerrors _patternIpatVarNames _patternIself _patternIunboundNames _patternIwarnings) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOcounter _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings)
         (T_RightHandSide_vOut148 _righthandsideIcollectInstances _righthandsideIcollectScopeInfos _righthandsideIcounter _righthandsideIkindErrors _righthandsideImiscerrors _righthandsideIself _righthandsideIunboundNames _righthandsideIwarnings) = inv_RightHandSide_s149 _righthandsideX149 (T_RightHandSide_vIn148 _righthandsideOallTypeConstructors _righthandsideOallValueConstructors _righthandsideOclassEnvironment _righthandsideOcollectScopeInfos _righthandsideOcounter _righthandsideOkindErrors _righthandsideOmiscerrors _righthandsideOnamesInScope _righthandsideOoptions _righthandsideOorderedTypeSynonyms _righthandsideOtypeConstructors _righthandsideOvalueConstructors _righthandsideOwarnings)
         (_namesInScope,_unboundNames,_scopeInfo) = rule31 _lhsInamesInScope _patternIpatVarNames _righthandsideIunboundNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule32 _unboundNames
         _patternOlhsPattern = rule33  ()
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule34 _righthandsideIcollectScopeInfos _scopeInfo
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule35 _righthandsideIcollectInstances
         _self = rule36 _patternIself _rangeIself _righthandsideIself
         _lhsOself :: Alternative
         _lhsOself = rule37 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule38 _righthandsideIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule39 _righthandsideIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule40 _righthandsideImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule41 _righthandsideIwarnings
         _patternOallTypeConstructors = rule42 _lhsIallTypeConstructors
         _patternOallValueConstructors = rule43 _lhsIallValueConstructors
         _patternOcollectScopeInfos = rule44 _lhsIcollectScopeInfos
         _patternOcounter = rule45 _lhsIcounter
         _patternOmiscerrors = rule46 _lhsImiscerrors
         _patternOnamesInScope = rule47 _namesInScope
         _patternOtypeConstructors = rule48 _lhsItypeConstructors
         _patternOvalueConstructors = rule49 _lhsIvalueConstructors
         _patternOwarnings = rule50 _lhsIwarnings
         _righthandsideOallTypeConstructors = rule51 _lhsIallTypeConstructors
         _righthandsideOallValueConstructors = rule52 _lhsIallValueConstructors
         _righthandsideOclassEnvironment = rule53 _lhsIclassEnvironment
         _righthandsideOcollectScopeInfos = rule54 _patternIcollectScopeInfos
         _righthandsideOcounter = rule55 _patternIcounter
         _righthandsideOkindErrors = rule56 _lhsIkindErrors
         _righthandsideOmiscerrors = rule57 _patternImiscerrors
         _righthandsideOnamesInScope = rule58 _namesInScope
         _righthandsideOoptions = rule59 _lhsIoptions
         _righthandsideOorderedTypeSynonyms = rule60 _lhsIorderedTypeSynonyms
         _righthandsideOtypeConstructors = rule61 _lhsItypeConstructors
         _righthandsideOvalueConstructors = rule62 _lhsIvalueConstructors
         _righthandsideOwarnings = rule63 _patternIwarnings
         __result_ = T_Alternative_vOut1 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule31 #-}
   rule31 = \ ((_lhsInamesInScope) :: Names) ((_patternIpatVarNames) :: Names) ((_righthandsideIunboundNames) :: Names) ->
                                                                        changeOfScope _patternIpatVarNames _righthandsideIunboundNames _lhsInamesInScope
   {-# INLINE rule32 #-}
   rule32 = \ _unboundNames ->
                                             _unboundNames
   {-# INLINE rule33 #-}
   rule33 = \  (_ :: ()) ->
                                                                False
   {-# INLINE rule34 #-}
   rule34 = \ ((_righthandsideIcollectScopeInfos) :: [(ScopeInfo, Entity)]) _scopeInfo ->
                                                 (_scopeInfo, Variable)   : _righthandsideIcollectScopeInfos
   {-# INLINE rule35 #-}
   rule35 = \ ((_righthandsideIcollectInstances) :: [(Name, Instance)]) ->
     _righthandsideIcollectInstances
   {-# INLINE rule36 #-}
   rule36 = \ ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ((_righthandsideIself) :: RightHandSide) ->
     Alternative_Alternative _rangeIself _patternIself _righthandsideIself
   {-# INLINE rule37 #-}
   rule37 = \ _self ->
     _self
   {-# INLINE rule38 #-}
   rule38 = \ ((_righthandsideIcounter) :: Int) ->
     _righthandsideIcounter
   {-# INLINE rule39 #-}
   rule39 = \ ((_righthandsideIkindErrors) :: [Error]) ->
     _righthandsideIkindErrors
   {-# INLINE rule40 #-}
   rule40 = \ ((_righthandsideImiscerrors) :: [Error]) ->
     _righthandsideImiscerrors
   {-# INLINE rule41 #-}
   rule41 = \ ((_righthandsideIwarnings) :: [Warning]) ->
     _righthandsideIwarnings
   {-# INLINE rule42 #-}
   rule42 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule43 #-}
   rule43 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule44 #-}
   rule44 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule45 #-}
   rule45 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule46 #-}
   rule46 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule47 #-}
   rule47 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule48 #-}
   rule48 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule49 #-}
   rule49 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule50 #-}
   rule50 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule51 #-}
   rule51 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule52 #-}
   rule52 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule53 #-}
   rule53 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule54 #-}
   rule54 = \ ((_patternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternIcollectScopeInfos
   {-# INLINE rule55 #-}
   rule55 = \ ((_patternIcounter) :: Int) ->
     _patternIcounter
   {-# INLINE rule56 #-}
   rule56 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule57 #-}
   rule57 = \ ((_patternImiscerrors) :: [Error]) ->
     _patternImiscerrors
   {-# INLINE rule58 #-}
   rule58 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule59 #-}
   rule59 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule60 #-}
   rule60 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule61 #-}
   rule61 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule62 #-}
   rule62 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule63 #-}
   rule63 = \ ((_patternIwarnings) :: [Warning]) ->
     _patternIwarnings
{-# NOINLINE sem_Alternative_Empty #-}
sem_Alternative_Empty :: T_Range  -> T_Alternative 
sem_Alternative_Empty arg_range_ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule64  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule65  ()
         _self = rule66 _rangeIself
         _lhsOself :: Alternative
         _lhsOself = rule67 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule68 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule69 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule70 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule71 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule72 _lhsIwarnings
         __result_ = T_Alternative_vOut1 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule64 #-}
   rule64 = \  (_ :: ()) ->
     []
   {-# INLINE rule65 #-}
   rule65 = \  (_ :: ()) ->
     []
   {-# INLINE rule66 #-}
   rule66 = \ ((_rangeIself) :: Range) ->
     Alternative_Empty _rangeIself
   {-# INLINE rule67 #-}
   rule67 = \ _self ->
     _self
   {-# INLINE rule68 #-}
   rule68 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule69 #-}
   rule69 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule70 #-}
   rule70 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule71 #-}
   rule71 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule72 #-}
   rule72 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Alternatives ------------------------------------------------
-- wrapper
data Inh_Alternatives  = Inh_Alternatives { allTypeConstructors_Inh_Alternatives :: (Names), allValueConstructors_Inh_Alternatives :: (Names), classEnvironment_Inh_Alternatives :: (ClassEnvironment), collectScopeInfos_Inh_Alternatives :: ([(ScopeInfo, Entity)]), counter_Inh_Alternatives :: (Int), kindErrors_Inh_Alternatives :: ([Error]), miscerrors_Inh_Alternatives :: ([Error]), namesInScope_Inh_Alternatives :: (Names), options_Inh_Alternatives :: ([Option]), orderedTypeSynonyms_Inh_Alternatives :: (OrderedTypeSynonyms), typeConstructors_Inh_Alternatives :: (M.Map Name Int), valueConstructors_Inh_Alternatives :: (M.Map Name TpScheme), warnings_Inh_Alternatives :: ([Warning]) }
data Syn_Alternatives  = Syn_Alternatives { collectInstances_Syn_Alternatives :: ([(Name, Instance)]), collectScopeInfos_Syn_Alternatives :: ([(ScopeInfo, Entity)]), counter_Syn_Alternatives :: (Int), kindErrors_Syn_Alternatives :: ([Error]), miscerrors_Syn_Alternatives :: ([Error]), self_Syn_Alternatives :: (Alternatives), unboundNames_Syn_Alternatives :: (Names), warnings_Syn_Alternatives :: ([Warning]) }
{-# INLINABLE wrap_Alternatives #-}
wrap_Alternatives :: T_Alternatives  -> Inh_Alternatives  -> (Syn_Alternatives )
wrap_Alternatives (T_Alternatives act) (Inh_Alternatives _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Alternatives_vIn4 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_Alternatives_vOut4 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_Alternatives_s5 sem arg)
        return (Syn_Alternatives _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Alternatives #-}
sem_Alternatives :: Alternatives  -> T_Alternatives 
sem_Alternatives list = Prelude.foldr sem_Alternatives_Cons sem_Alternatives_Nil (Prelude.map sem_Alternative list)

-- semantic domain
newtype T_Alternatives  = T_Alternatives {
                                         attach_T_Alternatives :: Identity (T_Alternatives_s5 )
                                         }
newtype T_Alternatives_s5  = C_Alternatives_s5 {
                                               inv_Alternatives_s5 :: (T_Alternatives_v4 )
                                               }
data T_Alternatives_s6  = C_Alternatives_s6
type T_Alternatives_v4  = (T_Alternatives_vIn4 ) -> (T_Alternatives_vOut4 )
data T_Alternatives_vIn4  = T_Alternatives_vIn4 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_Alternatives_vOut4  = T_Alternatives_vOut4 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Alternatives) (Names) ([Warning])
{-# NOINLINE sem_Alternatives_Cons #-}
sem_Alternatives_Cons :: T_Alternative  -> T_Alternatives  -> T_Alternatives 
sem_Alternatives_Cons arg_hd_ arg_tl_ = T_Alternatives (return st5) where
   {-# NOINLINE st5 #-}
   st5 = let
      v4 :: T_Alternatives_v4 
      v4 = \ (T_Alternatives_vIn4 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _hdX2 = Control.Monad.Identity.runIdentity (attach_T_Alternative (arg_hd_))
         _tlX5 = Control.Monad.Identity.runIdentity (attach_T_Alternatives (arg_tl_))
         (T_Alternative_vOut1 _hdIcollectInstances _hdIcollectScopeInfos _hdIcounter _hdIkindErrors _hdImiscerrors _hdIself _hdIunboundNames _hdIwarnings) = inv_Alternative_s2 _hdX2 (T_Alternative_vIn1 _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOcounter _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings)
         (T_Alternatives_vOut4 _tlIcollectInstances _tlIcollectScopeInfos _tlIcounter _tlIkindErrors _tlImiscerrors _tlIself _tlIunboundNames _tlIwarnings) = inv_Alternatives_s5 _tlX5 (T_Alternatives_vIn4 _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOcounter _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule73 _hdIcollectInstances _tlIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule74 _hdIunboundNames _tlIunboundNames
         _self = rule75 _hdIself _tlIself
         _lhsOself :: Alternatives
         _lhsOself = rule76 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule77 _tlIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule78 _tlIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule79 _tlIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule80 _tlImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule81 _tlIwarnings
         _hdOallTypeConstructors = rule82 _lhsIallTypeConstructors
         _hdOallValueConstructors = rule83 _lhsIallValueConstructors
         _hdOclassEnvironment = rule84 _lhsIclassEnvironment
         _hdOcollectScopeInfos = rule85 _lhsIcollectScopeInfos
         _hdOcounter = rule86 _lhsIcounter
         _hdOkindErrors = rule87 _lhsIkindErrors
         _hdOmiscerrors = rule88 _lhsImiscerrors
         _hdOnamesInScope = rule89 _lhsInamesInScope
         _hdOoptions = rule90 _lhsIoptions
         _hdOorderedTypeSynonyms = rule91 _lhsIorderedTypeSynonyms
         _hdOtypeConstructors = rule92 _lhsItypeConstructors
         _hdOvalueConstructors = rule93 _lhsIvalueConstructors
         _hdOwarnings = rule94 _lhsIwarnings
         _tlOallTypeConstructors = rule95 _lhsIallTypeConstructors
         _tlOallValueConstructors = rule96 _lhsIallValueConstructors
         _tlOclassEnvironment = rule97 _lhsIclassEnvironment
         _tlOcollectScopeInfos = rule98 _hdIcollectScopeInfos
         _tlOcounter = rule99 _hdIcounter
         _tlOkindErrors = rule100 _hdIkindErrors
         _tlOmiscerrors = rule101 _hdImiscerrors
         _tlOnamesInScope = rule102 _lhsInamesInScope
         _tlOoptions = rule103 _lhsIoptions
         _tlOorderedTypeSynonyms = rule104 _lhsIorderedTypeSynonyms
         _tlOtypeConstructors = rule105 _lhsItypeConstructors
         _tlOvalueConstructors = rule106 _lhsIvalueConstructors
         _tlOwarnings = rule107 _hdIwarnings
         __result_ = T_Alternatives_vOut4 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Alternatives_s5 v4
   {-# INLINE rule73 #-}
   rule73 = \ ((_hdIcollectInstances) :: [(Name, Instance)]) ((_tlIcollectInstances) :: [(Name, Instance)]) ->
     _hdIcollectInstances  ++  _tlIcollectInstances
   {-# INLINE rule74 #-}
   rule74 = \ ((_hdIunboundNames) :: Names) ((_tlIunboundNames) :: Names) ->
     _hdIunboundNames ++ _tlIunboundNames
   {-# INLINE rule75 #-}
   rule75 = \ ((_hdIself) :: Alternative) ((_tlIself) :: Alternatives) ->
     (:) _hdIself _tlIself
   {-# INLINE rule76 #-}
   rule76 = \ _self ->
     _self
   {-# INLINE rule77 #-}
   rule77 = \ ((_tlIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _tlIcollectScopeInfos
   {-# INLINE rule78 #-}
   rule78 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule79 #-}
   rule79 = \ ((_tlIkindErrors) :: [Error]) ->
     _tlIkindErrors
   {-# INLINE rule80 #-}
   rule80 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule81 #-}
   rule81 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule82 #-}
   rule82 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule83 #-}
   rule83 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule84 #-}
   rule84 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule85 #-}
   rule85 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule86 #-}
   rule86 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule87 #-}
   rule87 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule88 #-}
   rule88 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule89 #-}
   rule89 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule90 #-}
   rule90 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule91 #-}
   rule91 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule92 #-}
   rule92 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule93 #-}
   rule93 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule94 #-}
   rule94 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule95 #-}
   rule95 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule96 #-}
   rule96 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule97 #-}
   rule97 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule98 #-}
   rule98 = \ ((_hdIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _hdIcollectScopeInfos
   {-# INLINE rule99 #-}
   rule99 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule100 #-}
   rule100 = \ ((_hdIkindErrors) :: [Error]) ->
     _hdIkindErrors
   {-# INLINE rule101 #-}
   rule101 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule102 #-}
   rule102 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule103 #-}
   rule103 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule104 #-}
   rule104 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule105 #-}
   rule105 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule106 #-}
   rule106 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule107 #-}
   rule107 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_Alternatives_Nil #-}
sem_Alternatives_Nil ::  T_Alternatives 
sem_Alternatives_Nil  = T_Alternatives (return st5) where
   {-# NOINLINE st5 #-}
   st5 = let
      v4 :: T_Alternatives_v4 
      v4 = \ (T_Alternatives_vIn4 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule108  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule109  ()
         _self = rule110  ()
         _lhsOself :: Alternatives
         _lhsOself = rule111 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule112 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule113 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule114 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule115 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule116 _lhsIwarnings
         __result_ = T_Alternatives_vOut4 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Alternatives_s5 v4
   {-# INLINE rule108 #-}
   rule108 = \  (_ :: ()) ->
     []
   {-# INLINE rule109 #-}
   rule109 = \  (_ :: ()) ->
     []
   {-# INLINE rule110 #-}
   rule110 = \  (_ :: ()) ->
     []
   {-# INLINE rule111 #-}
   rule111 = \ _self ->
     _self
   {-# INLINE rule112 #-}
   rule112 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule113 #-}
   rule113 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule114 #-}
   rule114 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule115 #-}
   rule115 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule116 #-}
   rule116 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- AnnotatedType -----------------------------------------------
-- wrapper
data Inh_AnnotatedType  = Inh_AnnotatedType { allTypeConstructors_Inh_AnnotatedType :: (Names), allValueConstructors_Inh_AnnotatedType :: (Names), counter_Inh_AnnotatedType :: (Int), kindErrors_Inh_AnnotatedType :: ([Error]), miscerrors_Inh_AnnotatedType :: ([Error]), namesInScope_Inh_AnnotatedType :: (Names), options_Inh_AnnotatedType :: ([Option]), typeConstructors_Inh_AnnotatedType :: (M.Map Name Int), valueConstructors_Inh_AnnotatedType :: (M.Map Name TpScheme), warnings_Inh_AnnotatedType :: ([Warning]) }
data Syn_AnnotatedType  = Syn_AnnotatedType { counter_Syn_AnnotatedType :: (Int), kindErrors_Syn_AnnotatedType :: ([Error]), miscerrors_Syn_AnnotatedType :: ([Error]), self_Syn_AnnotatedType :: (AnnotatedType), type_Syn_AnnotatedType :: (Type), typevariables_Syn_AnnotatedType :: (Names), unboundNames_Syn_AnnotatedType :: (Names), warnings_Syn_AnnotatedType :: ([Warning]) }
{-# INLINABLE wrap_AnnotatedType #-}
wrap_AnnotatedType :: T_AnnotatedType  -> Inh_AnnotatedType  -> (Syn_AnnotatedType )
wrap_AnnotatedType (T_AnnotatedType act) (Inh_AnnotatedType _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_AnnotatedType_vIn7 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_AnnotatedType_vOut7 _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOtype _lhsOtypevariables _lhsOunboundNames _lhsOwarnings) <- return (inv_AnnotatedType_s8 sem arg)
        return (Syn_AnnotatedType _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOtype _lhsOtypevariables _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# INLINE sem_AnnotatedType #-}
sem_AnnotatedType :: AnnotatedType  -> T_AnnotatedType 
sem_AnnotatedType ( AnnotatedType_AnnotatedType range_ strict_ type_ ) = sem_AnnotatedType_AnnotatedType ( sem_Range range_ ) strict_ ( sem_Type type_ )

-- semantic domain
newtype T_AnnotatedType  = T_AnnotatedType {
                                           attach_T_AnnotatedType :: Identity (T_AnnotatedType_s8 )
                                           }
newtype T_AnnotatedType_s8  = C_AnnotatedType_s8 {
                                                 inv_AnnotatedType_s8 :: (T_AnnotatedType_v7 )
                                                 }
data T_AnnotatedType_s9  = C_AnnotatedType_s9
type T_AnnotatedType_v7  = (T_AnnotatedType_vIn7 ) -> (T_AnnotatedType_vOut7 )
data T_AnnotatedType_vIn7  = T_AnnotatedType_vIn7 (Names) (Names) (Int) ([Error]) ([Error]) (Names) ([Option]) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_AnnotatedType_vOut7  = T_AnnotatedType_vOut7 (Int) ([Error]) ([Error]) (AnnotatedType) (Type) (Names) (Names) ([Warning])
{-# NOINLINE sem_AnnotatedType_AnnotatedType #-}
sem_AnnotatedType_AnnotatedType :: T_Range  -> (Bool) -> T_Type  -> T_AnnotatedType 
sem_AnnotatedType_AnnotatedType arg_range_ arg_strict_ arg_type_ = T_AnnotatedType (return st8) where
   {-# NOINLINE st8 #-}
   st8 = let
      v7 :: T_AnnotatedType_v7 
      v7 = \ (T_AnnotatedType_vIn7 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Type_vOut163 _typeIcontextRange _typeImiscerrors _typeIself _typeItypevariables _typeIwarnings) = inv_Type_s164 _typeX164 (T_Type_vIn163 _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings)
         _lhsOtype :: Type
         _lhsOtype = rule117 _typeIself
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule118 _lhsIkindErrors _newErrors
         _newErrors = rule119 _lhsIallValueConstructors _lhsInamesInScope _lhsItypeConstructors _typeIself
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule120 _typeItypevariables
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule121  ()
         _self = rule122 _rangeIself _typeIself arg_strict_
         _lhsOself :: AnnotatedType
         _lhsOself = rule123 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule124 _lhsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule125 _typeImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule126 _typeIwarnings
         _typeOallTypeConstructors = rule127 _lhsIallTypeConstructors
         _typeOmiscerrors = rule128 _lhsImiscerrors
         _typeOoptions = rule129 _lhsIoptions
         _typeOtypeConstructors = rule130 _lhsItypeConstructors
         _typeOwarnings = rule131 _lhsIwarnings
         __result_ = T_AnnotatedType_vOut7 _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOtype _lhsOtypevariables _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_AnnotatedType_s8 v7
   {-# INLINE rule117 #-}
   rule117 = \ ((_typeIself) :: Type) ->
                                  _typeIself
   {-# INLINE rule118 #-}
   rule118 = \ ((_lhsIkindErrors) :: [Error]) _newErrors ->
                                         _newErrors ++ _lhsIkindErrors
   {-# INLINE rule119 #-}
   rule119 = \ ((_lhsIallValueConstructors) :: Names) ((_lhsInamesInScope) :: Names) ((_lhsItypeConstructors) :: M.Map Name Int) ((_typeIself) :: Type) ->
                                         checkType _lhsItypeConstructors (_lhsInamesInScope ++ _lhsIallValueConstructors) _typeIself
   {-# INLINE rule120 #-}
   rule120 = \ ((_typeItypevariables) :: Names) ->
     _typeItypevariables
   {-# INLINE rule121 #-}
   rule121 = \  (_ :: ()) ->
     []
   {-# INLINE rule122 #-}
   rule122 = \ ((_rangeIself) :: Range) ((_typeIself) :: Type) strict_ ->
     AnnotatedType_AnnotatedType _rangeIself strict_ _typeIself
   {-# INLINE rule123 #-}
   rule123 = \ _self ->
     _self
   {-# INLINE rule124 #-}
   rule124 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule125 #-}
   rule125 = \ ((_typeImiscerrors) :: [Error]) ->
     _typeImiscerrors
   {-# INLINE rule126 #-}
   rule126 = \ ((_typeIwarnings) :: [Warning]) ->
     _typeIwarnings
   {-# INLINE rule127 #-}
   rule127 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule128 #-}
   rule128 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule129 #-}
   rule129 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule130 #-}
   rule130 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule131 #-}
   rule131 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- AnnotatedTypes ----------------------------------------------
-- wrapper
data Inh_AnnotatedTypes  = Inh_AnnotatedTypes { allTypeConstructors_Inh_AnnotatedTypes :: (Names), allValueConstructors_Inh_AnnotatedTypes :: (Names), counter_Inh_AnnotatedTypes :: (Int), kindErrors_Inh_AnnotatedTypes :: ([Error]), miscerrors_Inh_AnnotatedTypes :: ([Error]), namesInScope_Inh_AnnotatedTypes :: (Names), options_Inh_AnnotatedTypes :: ([Option]), typeConstructors_Inh_AnnotatedTypes :: (M.Map Name Int), valueConstructors_Inh_AnnotatedTypes :: (M.Map Name TpScheme), warnings_Inh_AnnotatedTypes :: ([Warning]) }
data Syn_AnnotatedTypes  = Syn_AnnotatedTypes { counter_Syn_AnnotatedTypes :: (Int), kindErrors_Syn_AnnotatedTypes :: ([Error]), miscerrors_Syn_AnnotatedTypes :: ([Error]), self_Syn_AnnotatedTypes :: (AnnotatedTypes), types_Syn_AnnotatedTypes :: (Types), typevariables_Syn_AnnotatedTypes :: (Names), unboundNames_Syn_AnnotatedTypes :: (Names), warnings_Syn_AnnotatedTypes :: ([Warning]) }
{-# INLINABLE wrap_AnnotatedTypes #-}
wrap_AnnotatedTypes :: T_AnnotatedTypes  -> Inh_AnnotatedTypes  -> (Syn_AnnotatedTypes )
wrap_AnnotatedTypes (T_AnnotatedTypes act) (Inh_AnnotatedTypes _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_AnnotatedTypes_vIn10 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_AnnotatedTypes_vOut10 _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOtypes _lhsOtypevariables _lhsOunboundNames _lhsOwarnings) <- return (inv_AnnotatedTypes_s11 sem arg)
        return (Syn_AnnotatedTypes _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOtypes _lhsOtypevariables _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_AnnotatedTypes #-}
sem_AnnotatedTypes :: AnnotatedTypes  -> T_AnnotatedTypes 
sem_AnnotatedTypes list = Prelude.foldr sem_AnnotatedTypes_Cons sem_AnnotatedTypes_Nil (Prelude.map sem_AnnotatedType list)

-- semantic domain
newtype T_AnnotatedTypes  = T_AnnotatedTypes {
                                             attach_T_AnnotatedTypes :: Identity (T_AnnotatedTypes_s11 )
                                             }
newtype T_AnnotatedTypes_s11  = C_AnnotatedTypes_s11 {
                                                     inv_AnnotatedTypes_s11 :: (T_AnnotatedTypes_v10 )
                                                     }
data T_AnnotatedTypes_s12  = C_AnnotatedTypes_s12
type T_AnnotatedTypes_v10  = (T_AnnotatedTypes_vIn10 ) -> (T_AnnotatedTypes_vOut10 )
data T_AnnotatedTypes_vIn10  = T_AnnotatedTypes_vIn10 (Names) (Names) (Int) ([Error]) ([Error]) (Names) ([Option]) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_AnnotatedTypes_vOut10  = T_AnnotatedTypes_vOut10 (Int) ([Error]) ([Error]) (AnnotatedTypes) (Types) (Names) (Names) ([Warning])
{-# NOINLINE sem_AnnotatedTypes_Cons #-}
sem_AnnotatedTypes_Cons :: T_AnnotatedType  -> T_AnnotatedTypes  -> T_AnnotatedTypes 
sem_AnnotatedTypes_Cons arg_hd_ arg_tl_ = T_AnnotatedTypes (return st11) where
   {-# NOINLINE st11 #-}
   st11 = let
      v10 :: T_AnnotatedTypes_v10 
      v10 = \ (T_AnnotatedTypes_vIn10 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _hdX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_hd_))
         _tlX11 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedTypes (arg_tl_))
         (T_AnnotatedType_vOut7 _hdIcounter _hdIkindErrors _hdImiscerrors _hdIself _hdItype _hdItypevariables _hdIunboundNames _hdIwarnings) = inv_AnnotatedType_s8 _hdX8 (T_AnnotatedType_vIn7 _hdOallTypeConstructors _hdOallValueConstructors _hdOcounter _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings)
         (T_AnnotatedTypes_vOut10 _tlIcounter _tlIkindErrors _tlImiscerrors _tlIself _tlItypes _tlItypevariables _tlIunboundNames _tlIwarnings) = inv_AnnotatedTypes_s11 _tlX11 (T_AnnotatedTypes_vIn10 _tlOallTypeConstructors _tlOallValueConstructors _tlOcounter _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings)
         _lhsOtypes :: Types
         _lhsOtypes = rule132 _hdItype _tlItypes
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule133 _hdItypevariables _tlItypevariables
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule134 _hdIunboundNames _tlIunboundNames
         _self = rule135 _hdIself _tlIself
         _lhsOself :: AnnotatedTypes
         _lhsOself = rule136 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule137 _tlIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule138 _tlIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule139 _tlImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule140 _tlIwarnings
         _hdOallTypeConstructors = rule141 _lhsIallTypeConstructors
         _hdOallValueConstructors = rule142 _lhsIallValueConstructors
         _hdOcounter = rule143 _lhsIcounter
         _hdOkindErrors = rule144 _lhsIkindErrors
         _hdOmiscerrors = rule145 _lhsImiscerrors
         _hdOnamesInScope = rule146 _lhsInamesInScope
         _hdOoptions = rule147 _lhsIoptions
         _hdOtypeConstructors = rule148 _lhsItypeConstructors
         _hdOvalueConstructors = rule149 _lhsIvalueConstructors
         _hdOwarnings = rule150 _lhsIwarnings
         _tlOallTypeConstructors = rule151 _lhsIallTypeConstructors
         _tlOallValueConstructors = rule152 _lhsIallValueConstructors
         _tlOcounter = rule153 _hdIcounter
         _tlOkindErrors = rule154 _hdIkindErrors
         _tlOmiscerrors = rule155 _hdImiscerrors
         _tlOnamesInScope = rule156 _lhsInamesInScope
         _tlOoptions = rule157 _lhsIoptions
         _tlOtypeConstructors = rule158 _lhsItypeConstructors
         _tlOvalueConstructors = rule159 _lhsIvalueConstructors
         _tlOwarnings = rule160 _hdIwarnings
         __result_ = T_AnnotatedTypes_vOut10 _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOtypes _lhsOtypevariables _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_AnnotatedTypes_s11 v10
   {-# INLINE rule132 #-}
   rule132 = \ ((_hdItype) :: Type) ((_tlItypes) :: Types) ->
                           _hdItype : _tlItypes
   {-# INLINE rule133 #-}
   rule133 = \ ((_hdItypevariables) :: Names) ((_tlItypevariables) :: Names) ->
     _hdItypevariables  ++  _tlItypevariables
   {-# INLINE rule134 #-}
   rule134 = \ ((_hdIunboundNames) :: Names) ((_tlIunboundNames) :: Names) ->
     _hdIunboundNames ++ _tlIunboundNames
   {-# INLINE rule135 #-}
   rule135 = \ ((_hdIself) :: AnnotatedType) ((_tlIself) :: AnnotatedTypes) ->
     (:) _hdIself _tlIself
   {-# INLINE rule136 #-}
   rule136 = \ _self ->
     _self
   {-# INLINE rule137 #-}
   rule137 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule138 #-}
   rule138 = \ ((_tlIkindErrors) :: [Error]) ->
     _tlIkindErrors
   {-# INLINE rule139 #-}
   rule139 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule140 #-}
   rule140 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule141 #-}
   rule141 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule142 #-}
   rule142 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule143 #-}
   rule143 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule144 #-}
   rule144 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule145 #-}
   rule145 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule146 #-}
   rule146 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule147 #-}
   rule147 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule148 #-}
   rule148 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule149 #-}
   rule149 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule150 #-}
   rule150 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule151 #-}
   rule151 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule152 #-}
   rule152 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule153 #-}
   rule153 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule154 #-}
   rule154 = \ ((_hdIkindErrors) :: [Error]) ->
     _hdIkindErrors
   {-# INLINE rule155 #-}
   rule155 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule156 #-}
   rule156 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule157 #-}
   rule157 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule158 #-}
   rule158 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule159 #-}
   rule159 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule160 #-}
   rule160 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_AnnotatedTypes_Nil #-}
sem_AnnotatedTypes_Nil ::  T_AnnotatedTypes 
sem_AnnotatedTypes_Nil  = T_AnnotatedTypes (return st11) where
   {-# NOINLINE st11 #-}
   st11 = let
      v10 :: T_AnnotatedTypes_v10 
      v10 = \ (T_AnnotatedTypes_vIn10 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOtypes :: Types
         _lhsOtypes = rule161  ()
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule162  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule163  ()
         _self = rule164  ()
         _lhsOself :: AnnotatedTypes
         _lhsOself = rule165 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule166 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule167 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule168 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule169 _lhsIwarnings
         __result_ = T_AnnotatedTypes_vOut10 _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOtypes _lhsOtypevariables _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_AnnotatedTypes_s11 v10
   {-# INLINE rule161 #-}
   rule161 = \  (_ :: ()) ->
                           []
   {-# INLINE rule162 #-}
   rule162 = \  (_ :: ()) ->
     []
   {-# INLINE rule163 #-}
   rule163 = \  (_ :: ()) ->
     []
   {-# INLINE rule164 #-}
   rule164 = \  (_ :: ()) ->
     []
   {-# INLINE rule165 #-}
   rule165 = \ _self ->
     _self
   {-# INLINE rule166 #-}
   rule166 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule167 #-}
   rule167 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule168 #-}
   rule168 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule169 #-}
   rule169 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Body --------------------------------------------------------
-- wrapper
data Inh_Body  = Inh_Body { allTypeConstructors_Inh_Body :: (Names), allValueConstructors_Inh_Body :: (Names), classEnvironment_Inh_Body :: (ClassEnvironment), collectScopeInfos_Inh_Body :: ([(ScopeInfo, Entity)]), collectTypeConstructors_Inh_Body :: ([(Name,Int)]), collectTypeSynonyms_Inh_Body :: ([(Name,(Int,Tps -> Tp))]), collectValueConstructors_Inh_Body :: ([(Name,TpScheme)]), counter_Inh_Body :: (Int), kindErrors_Inh_Body :: ([Error]), miscerrors_Inh_Body :: ([Error]), namesInScope_Inh_Body :: (Names), operatorFixities_Inh_Body :: ([(Name,(Int,Assoc))]), options_Inh_Body :: ([Option]), orderedTypeSynonyms_Inh_Body :: (OrderedTypeSynonyms), typeConstructors_Inh_Body :: (M.Map Name Int), valueConstructors_Inh_Body :: (M.Map Name TpScheme), warnings_Inh_Body :: ([Warning]) }
data Syn_Body  = Syn_Body { collectInstances_Syn_Body :: ([(Name, Instance)]), collectScopeInfos_Syn_Body :: ([(ScopeInfo, Entity)]), collectTypeConstructors_Syn_Body :: ([(Name,Int)]), collectTypeSynonyms_Syn_Body :: ([(Name,(Int,Tps -> Tp))]), collectValueConstructors_Syn_Body :: ([(Name,TpScheme)]), counter_Syn_Body :: (Int), declVarNames_Syn_Body :: (Names), importedModules_Syn_Body :: (Names), kindErrors_Syn_Body :: ([Error]), miscerrors_Syn_Body :: ([Error]), operatorFixities_Syn_Body :: ([(Name,(Int,Assoc))]), self_Syn_Body :: (Body), typeSignatures_Syn_Body :: ([(Name,TpScheme)]), unboundNames_Syn_Body :: (Names), warnings_Syn_Body :: ([Warning]) }
{-# INLINABLE wrap_Body #-}
wrap_Body :: T_Body  -> Inh_Body  -> (Syn_Body )
wrap_Body (T_Body act) (Inh_Body _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Body_vIn13 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_Body_vOut13 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOimportedModules _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOself _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings) <- return (inv_Body_s14 sem arg)
        return (Syn_Body _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOimportedModules _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOself _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Body #-}
sem_Body :: Body  -> T_Body 
sem_Body ( Body_Hole range_ id_ ) = sem_Body_Hole ( sem_Range range_ ) id_
sem_Body ( Body_Body range_ importdeclarations_ declarations_ ) = sem_Body_Body ( sem_Range range_ ) ( sem_ImportDeclarations importdeclarations_ ) ( sem_Declarations declarations_ )

-- semantic domain
newtype T_Body  = T_Body {
                         attach_T_Body :: Identity (T_Body_s14 )
                         }
newtype T_Body_s14  = C_Body_s14 {
                                 inv_Body_s14 :: (T_Body_v13 )
                                 }
data T_Body_s15  = C_Body_s15
type T_Body_v13  = (T_Body_vIn13 ) -> (T_Body_vOut13 )
data T_Body_vIn13  = T_Body_vIn13 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) ([(Name,Int)]) ([(Name,(Int,Tps -> Tp))]) ([(Name,TpScheme)]) (Int) ([Error]) ([Error]) (Names) ([(Name,(Int,Assoc))]) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_Body_vOut13  = T_Body_vOut13 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) ([(Name,Int)]) ([(Name,(Int,Tps -> Tp))]) ([(Name,TpScheme)]) (Int) (Names) (Names) ([Error]) ([Error]) ([(Name,(Int,Assoc))]) (Body) ([(Name,TpScheme)]) (Names) ([Warning])
{-# NOINLINE sem_Body_Hole #-}
sem_Body_Hole :: T_Range  -> (Integer) -> T_Body 
sem_Body_Hole arg_range_ arg_id_ = T_Body (return st14) where
   {-# NOINLINE st14 #-}
   st14 = let
      v13 :: T_Body_v13 
      v13 = \ (T_Body_vIn13 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule170  ()
         _lhsOimportedModules :: Names
         _lhsOimportedModules = rule171  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule172  ()
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule173  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule174  ()
         _self = rule175 _rangeIself arg_id_
         _lhsOself :: Body
         _lhsOself = rule176 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule177 _lhsIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule178 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule179 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule180 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule181 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule182 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule183 _lhsImiscerrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule184 _lhsIoperatorFixities
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule185 _lhsIwarnings
         __result_ = T_Body_vOut13 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOimportedModules _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOself _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Body_s14 v13
   {-# INLINE rule170 #-}
   rule170 = \  (_ :: ()) ->
                                  []
   {-# INLINE rule171 #-}
   rule171 = \  (_ :: ()) ->
                                      []
   {-# INLINE rule172 #-}
   rule172 = \  (_ :: ()) ->
     []
   {-# INLINE rule173 #-}
   rule173 = \  (_ :: ()) ->
     []
   {-# INLINE rule174 #-}
   rule174 = \  (_ :: ()) ->
     []
   {-# INLINE rule175 #-}
   rule175 = \ ((_rangeIself) :: Range) id_ ->
     Body_Hole _rangeIself id_
   {-# INLINE rule176 #-}
   rule176 = \ _self ->
     _self
   {-# INLINE rule177 #-}
   rule177 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule178 #-}
   rule178 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule179 #-}
   rule179 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule180 #-}
   rule180 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule181 #-}
   rule181 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule182 #-}
   rule182 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule183 #-}
   rule183 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule184 #-}
   rule184 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule185 #-}
   rule185 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Body_Body #-}
sem_Body_Body :: T_Range  -> T_ImportDeclarations  -> T_Declarations  -> T_Body 
sem_Body_Body arg_range_ arg_importdeclarations_ arg_declarations_ = T_Body (return st14) where
   {-# NOINLINE st14 #-}
   st14 = let
      v13 :: T_Body_v13 
      v13 = \ (T_Body_vIn13 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _importdeclarationsX74 = Control.Monad.Identity.runIdentity (attach_T_ImportDeclarations (arg_importdeclarations_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ImportDeclarations_vOut73 _importdeclarationsIimportedModules _importdeclarationsIself) = inv_ImportDeclarations_s74 _importdeclarationsX74 (T_ImportDeclarations_vIn73 _importdeclarationsOimportedModules)
         (T_Declarations_vOut31 _declarationsIcollectInstances _declarationsIcollectScopeInfos _declarationsIcollectTypeConstructors _declarationsIcollectTypeSynonyms _declarationsIcollectValueConstructors _declarationsIcounter _declarationsIdeclVarNames _declarationsIkindErrors _declarationsImiscerrors _declarationsIoperatorFixities _declarationsIpreviousWasAlsoFB _declarationsIrestrictedNames _declarationsIself _declarationsIsuspiciousFBs _declarationsItypeSignatures _declarationsIunboundNames _declarationsIwarnings) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 _declarationsOallTypeConstructors _declarationsOallValueConstructors _declarationsOclassEnvironment _declarationsOcollectScopeInfos _declarationsOcollectTypeConstructors _declarationsOcollectTypeSynonyms _declarationsOcollectValueConstructors _declarationsOcounter _declarationsOkindErrors _declarationsOmiscerrors _declarationsOnamesInScope _declarationsOoperatorFixities _declarationsOoptions _declarationsOorderedTypeSynonyms _declarationsOpreviousWasAlsoFB _declarationsOsuspiciousFBs _declarationsOtypeConstructors _declarationsOtypeSignatures _declarationsOvalueConstructors _declarationsOwarnings)
         _declarationsOtypeSignatures = rule186  ()
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule187 _declarationsIwarnings _suspiciousErrors
         _declarationsOpreviousWasAlsoFB = rule188  ()
         _declarationsOsuspiciousFBs = rule189  ()
         _suspiciousErrors = rule190 _declarationsIsuspiciousFBs _declarationsItypeSignatures
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule191 _declarationsImiscerrors _typeSignatureErrors
         _typeSignatureErrors = rule192 _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
         _importdeclarationsOimportedModules = rule193  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule194 _declarationsIcollectInstances
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule195 _declarationsIdeclVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule196 _declarationsIunboundNames
         _self = rule197 _declarationsIself _importdeclarationsIself _rangeIself
         _lhsOself :: Body
         _lhsOself = rule198 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule199 _declarationsIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule200 _declarationsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule201 _declarationsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule202 _declarationsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule203 _declarationsIcounter
         _lhsOimportedModules :: Names
         _lhsOimportedModules = rule204 _importdeclarationsIimportedModules
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule205 _declarationsIkindErrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule206 _declarationsIoperatorFixities
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule207 _declarationsItypeSignatures
         _declarationsOallTypeConstructors = rule208 _lhsIallTypeConstructors
         _declarationsOallValueConstructors = rule209 _lhsIallValueConstructors
         _declarationsOclassEnvironment = rule210 _lhsIclassEnvironment
         _declarationsOcollectScopeInfos = rule211 _lhsIcollectScopeInfos
         _declarationsOcollectTypeConstructors = rule212 _lhsIcollectTypeConstructors
         _declarationsOcollectTypeSynonyms = rule213 _lhsIcollectTypeSynonyms
         _declarationsOcollectValueConstructors = rule214 _lhsIcollectValueConstructors
         _declarationsOcounter = rule215 _lhsIcounter
         _declarationsOkindErrors = rule216 _lhsIkindErrors
         _declarationsOmiscerrors = rule217 _lhsImiscerrors
         _declarationsOnamesInScope = rule218 _lhsInamesInScope
         _declarationsOoperatorFixities = rule219 _lhsIoperatorFixities
         _declarationsOoptions = rule220 _lhsIoptions
         _declarationsOorderedTypeSynonyms = rule221 _lhsIorderedTypeSynonyms
         _declarationsOtypeConstructors = rule222 _lhsItypeConstructors
         _declarationsOvalueConstructors = rule223 _lhsIvalueConstructors
         _declarationsOwarnings = rule224 _lhsIwarnings
         __result_ = T_Body_vOut13 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOimportedModules _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOself _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Body_s14 v13
   {-# INLINE rule186 #-}
   rule186 = \  (_ :: ()) ->
                                              []
   {-# INLINE rule187 #-}
   rule187 = \ ((_declarationsIwarnings) :: [Warning]) _suspiciousErrors ->
                            _declarationsIwarnings ++
                            _suspiciousErrors
   {-# INLINE rule188 #-}
   rule188 = \  (_ :: ()) ->
                                                Nothing
   {-# INLINE rule189 #-}
   rule189 = \  (_ :: ()) ->
                                                []
   {-# INLINE rule190 #-}
   rule190 = \ ((_declarationsIsuspiciousFBs) :: [(Name,Name)]) ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                                findSimilarFunctionBindings _declarationsItypeSignatures _declarationsIsuspiciousFBs
   {-# INLINE rule191 #-}
   rule191 = \ ((_declarationsImiscerrors) :: [Error]) _typeSignatureErrors ->
                                _typeSignatureErrors ++ _declarationsImiscerrors
   {-# INLINE rule192 #-}
   rule192 = \ ((_declarationsIdeclVarNames) :: Names) ((_declarationsIrestrictedNames) :: Names) ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                         checkTypeSignatures _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
   {-# INLINE rule193 #-}
   rule193 = \  (_ :: ()) ->
                                                     []
   {-# INLINE rule194 #-}
   rule194 = \ ((_declarationsIcollectInstances) :: [(Name, Instance)]) ->
     _declarationsIcollectInstances
   {-# INLINE rule195 #-}
   rule195 = \ ((_declarationsIdeclVarNames) :: Names) ->
     _declarationsIdeclVarNames
   {-# INLINE rule196 #-}
   rule196 = \ ((_declarationsIunboundNames) :: Names) ->
     _declarationsIunboundNames
   {-# INLINE rule197 #-}
   rule197 = \ ((_declarationsIself) :: Declarations) ((_importdeclarationsIself) :: ImportDeclarations) ((_rangeIself) :: Range) ->
     Body_Body _rangeIself _importdeclarationsIself _declarationsIself
   {-# INLINE rule198 #-}
   rule198 = \ _self ->
     _self
   {-# INLINE rule199 #-}
   rule199 = \ ((_declarationsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _declarationsIcollectScopeInfos
   {-# INLINE rule200 #-}
   rule200 = \ ((_declarationsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _declarationsIcollectTypeConstructors
   {-# INLINE rule201 #-}
   rule201 = \ ((_declarationsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _declarationsIcollectTypeSynonyms
   {-# INLINE rule202 #-}
   rule202 = \ ((_declarationsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _declarationsIcollectValueConstructors
   {-# INLINE rule203 #-}
   rule203 = \ ((_declarationsIcounter) :: Int) ->
     _declarationsIcounter
   {-# INLINE rule204 #-}
   rule204 = \ ((_importdeclarationsIimportedModules) :: Names) ->
     _importdeclarationsIimportedModules
   {-# INLINE rule205 #-}
   rule205 = \ ((_declarationsIkindErrors) :: [Error]) ->
     _declarationsIkindErrors
   {-# INLINE rule206 #-}
   rule206 = \ ((_declarationsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _declarationsIoperatorFixities
   {-# INLINE rule207 #-}
   rule207 = \ ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
     _declarationsItypeSignatures
   {-# INLINE rule208 #-}
   rule208 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule209 #-}
   rule209 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule210 #-}
   rule210 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule211 #-}
   rule211 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule212 #-}
   rule212 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule213 #-}
   rule213 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule214 #-}
   rule214 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule215 #-}
   rule215 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule216 #-}
   rule216 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule217 #-}
   rule217 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule218 #-}
   rule218 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule219 #-}
   rule219 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule220 #-}
   rule220 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule221 #-}
   rule221 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule222 #-}
   rule222 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule223 #-}
   rule223 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule224 #-}
   rule224 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Constructor -------------------------------------------------
-- wrapper
data Inh_Constructor  = Inh_Constructor { allTypeConstructors_Inh_Constructor :: (Names), allValueConstructors_Inh_Constructor :: (Names), collectValueConstructors_Inh_Constructor :: ([(Name,TpScheme)]), counter_Inh_Constructor :: (Int), kindErrors_Inh_Constructor :: ([Error]), miscerrors_Inh_Constructor :: ([Error]), namesInScope_Inh_Constructor :: (Names), options_Inh_Constructor :: ([Option]), simpletype_Inh_Constructor :: (SimpleType), typeConstructors_Inh_Constructor :: (M.Map Name Int), valueConstructors_Inh_Constructor :: (M.Map Name TpScheme), warnings_Inh_Constructor :: ([Warning]) }
data Syn_Constructor  = Syn_Constructor { collectValueConstructors_Syn_Constructor :: ([(Name,TpScheme)]), counter_Syn_Constructor :: (Int), kindErrors_Syn_Constructor :: ([Error]), miscerrors_Syn_Constructor :: ([Error]), parameterTypes_Syn_Constructor :: (Tps), self_Syn_Constructor :: (Constructor), typevariables_Syn_Constructor :: (Names), unboundNames_Syn_Constructor :: (Names), warnings_Syn_Constructor :: ([Warning]) }
{-# INLINABLE wrap_Constructor #-}
wrap_Constructor :: T_Constructor  -> Inh_Constructor  -> (Syn_Constructor )
wrap_Constructor (T_Constructor act) (Inh_Constructor _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIsimpletype _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Constructor_vIn16 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIsimpletype _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_Constructor_vOut16 _lhsOcollectValueConstructors _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOparameterTypes _lhsOself _lhsOtypevariables _lhsOunboundNames _lhsOwarnings) <- return (inv_Constructor_s17 sem arg)
        return (Syn_Constructor _lhsOcollectValueConstructors _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOparameterTypes _lhsOself _lhsOtypevariables _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Constructor #-}
sem_Constructor :: Constructor  -> T_Constructor 
sem_Constructor ( Constructor_Constructor range_ constructor_ types_ ) = sem_Constructor_Constructor ( sem_Range range_ ) ( sem_Name constructor_ ) ( sem_AnnotatedTypes types_ )
sem_Constructor ( Constructor_Infix range_ leftType_ constructorOperator_ rightType_ ) = sem_Constructor_Infix ( sem_Range range_ ) ( sem_AnnotatedType leftType_ ) ( sem_Name constructorOperator_ ) ( sem_AnnotatedType rightType_ )
sem_Constructor ( Constructor_Record range_ constructor_ fieldDeclarations_ ) = sem_Constructor_Record ( sem_Range range_ ) ( sem_Name constructor_ ) ( sem_FieldDeclarations fieldDeclarations_ )

-- semantic domain
newtype T_Constructor  = T_Constructor {
                                       attach_T_Constructor :: Identity (T_Constructor_s17 )
                                       }
newtype T_Constructor_s17  = C_Constructor_s17 {
                                               inv_Constructor_s17 :: (T_Constructor_v16 )
                                               }
data T_Constructor_s18  = C_Constructor_s18
type T_Constructor_v16  = (T_Constructor_vIn16 ) -> (T_Constructor_vOut16 )
data T_Constructor_vIn16  = T_Constructor_vIn16 (Names) (Names) ([(Name,TpScheme)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (SimpleType) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_Constructor_vOut16  = T_Constructor_vOut16 ([(Name,TpScheme)]) (Int) ([Error]) ([Error]) (Tps) (Constructor) (Names) (Names) ([Warning])
{-# NOINLINE sem_Constructor_Constructor #-}
sem_Constructor_Constructor :: T_Range  -> T_Name  -> T_AnnotatedTypes  -> T_Constructor 
sem_Constructor_Constructor arg_range_ arg_constructor_ arg_types_ = T_Constructor (return st17) where
   {-# NOINLINE st17 #-}
   st17 = let
      v16 :: T_Constructor_v16 
      v16 = \ (T_Constructor_vIn16 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIsimpletype _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _constructorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructor_))
         _typesX11 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedTypes (arg_types_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _constructorIself) = inv_Name_s113 _constructorX113 (T_Name_vIn112 )
         (T_AnnotatedTypes_vOut10 _typesIcounter _typesIkindErrors _typesImiscerrors _typesIself _typesItypes _typesItypevariables _typesIunboundNames _typesIwarnings) = inv_AnnotatedTypes_s11 _typesX11 (T_AnnotatedTypes_vIn10 _typesOallTypeConstructors _typesOallValueConstructors _typesOcounter _typesOkindErrors _typesOmiscerrors _typesOnamesInScope _typesOoptions _typesOtypeConstructors _typesOvalueConstructors _typesOwarnings)
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule225 _constructorIself _lhsIcollectValueConstructors _typeScheme
         _lhsOparameterTypes :: Tps
         _lhsOparameterTypes = rule226 _tps
         _typeScheme = rule227 _tp _tps
         (_tp,_tps) = rule228 _lhsIsimpletype _typesItypes
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule229 _typesItypevariables
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule230 _typesIunboundNames
         _self = rule231 _constructorIself _rangeIself _typesIself
         _lhsOself :: Constructor
         _lhsOself = rule232 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule233 _typesIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule234 _typesIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule235 _typesImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule236 _typesIwarnings
         _typesOallTypeConstructors = rule237 _lhsIallTypeConstructors
         _typesOallValueConstructors = rule238 _lhsIallValueConstructors
         _typesOcounter = rule239 _lhsIcounter
         _typesOkindErrors = rule240 _lhsIkindErrors
         _typesOmiscerrors = rule241 _lhsImiscerrors
         _typesOnamesInScope = rule242 _lhsInamesInScope
         _typesOoptions = rule243 _lhsIoptions
         _typesOtypeConstructors = rule244 _lhsItypeConstructors
         _typesOvalueConstructors = rule245 _lhsIvalueConstructors
         _typesOwarnings = rule246 _lhsIwarnings
         __result_ = T_Constructor_vOut16 _lhsOcollectValueConstructors _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOparameterTypes _lhsOself _lhsOtypevariables _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Constructor_s17 v16
   {-# INLINE rule225 #-}
   rule225 = \ ((_constructorIself) :: Name) ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) _typeScheme ->
                                          (_constructorIself, _typeScheme) : _lhsIcollectValueConstructors
   {-# INLINE rule226 #-}
   rule226 = \ _tps ->
                                _tps
   {-# INLINE rule227 #-}
   rule227 = \ _tp _tps ->
                            generalizeAll ([] .=>. foldr (.->.) _tp _tps)
   {-# INLINE rule228 #-}
   rule228 = \ ((_lhsIsimpletype) :: SimpleType) ((_typesItypes) :: Types) ->
                            convertFromSimpleTypeAndTypes _lhsIsimpletype _typesItypes
   {-# INLINE rule229 #-}
   rule229 = \ ((_typesItypevariables) :: Names) ->
     _typesItypevariables
   {-# INLINE rule230 #-}
   rule230 = \ ((_typesIunboundNames) :: Names) ->
     _typesIunboundNames
   {-# INLINE rule231 #-}
   rule231 = \ ((_constructorIself) :: Name) ((_rangeIself) :: Range) ((_typesIself) :: AnnotatedTypes) ->
     Constructor_Constructor _rangeIself _constructorIself _typesIself
   {-# INLINE rule232 #-}
   rule232 = \ _self ->
     _self
   {-# INLINE rule233 #-}
   rule233 = \ ((_typesIcounter) :: Int) ->
     _typesIcounter
   {-# INLINE rule234 #-}
   rule234 = \ ((_typesIkindErrors) :: [Error]) ->
     _typesIkindErrors
   {-# INLINE rule235 #-}
   rule235 = \ ((_typesImiscerrors) :: [Error]) ->
     _typesImiscerrors
   {-# INLINE rule236 #-}
   rule236 = \ ((_typesIwarnings) :: [Warning]) ->
     _typesIwarnings
   {-# INLINE rule237 #-}
   rule237 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule238 #-}
   rule238 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule239 #-}
   rule239 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule240 #-}
   rule240 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule241 #-}
   rule241 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule242 #-}
   rule242 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule243 #-}
   rule243 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule244 #-}
   rule244 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule245 #-}
   rule245 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule246 #-}
   rule246 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Constructor_Infix #-}
sem_Constructor_Infix :: T_Range  -> T_AnnotatedType  -> T_Name  -> T_AnnotatedType  -> T_Constructor 
sem_Constructor_Infix arg_range_ arg_leftType_ arg_constructorOperator_ arg_rightType_ = T_Constructor (return st17) where
   {-# NOINLINE st17 #-}
   st17 = let
      v16 :: T_Constructor_v16 
      v16 = \ (T_Constructor_vIn16 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIsimpletype _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftTypeX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_leftType_))
         _constructorOperatorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructorOperator_))
         _rightTypeX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_rightType_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_AnnotatedType_vOut7 _leftTypeIcounter _leftTypeIkindErrors _leftTypeImiscerrors _leftTypeIself _leftTypeItype _leftTypeItypevariables _leftTypeIunboundNames _leftTypeIwarnings) = inv_AnnotatedType_s8 _leftTypeX8 (T_AnnotatedType_vIn7 _leftTypeOallTypeConstructors _leftTypeOallValueConstructors _leftTypeOcounter _leftTypeOkindErrors _leftTypeOmiscerrors _leftTypeOnamesInScope _leftTypeOoptions _leftTypeOtypeConstructors _leftTypeOvalueConstructors _leftTypeOwarnings)
         (T_Name_vOut112 _constructorOperatorIself) = inv_Name_s113 _constructorOperatorX113 (T_Name_vIn112 )
         (T_AnnotatedType_vOut7 _rightTypeIcounter _rightTypeIkindErrors _rightTypeImiscerrors _rightTypeIself _rightTypeItype _rightTypeItypevariables _rightTypeIunboundNames _rightTypeIwarnings) = inv_AnnotatedType_s8 _rightTypeX8 (T_AnnotatedType_vIn7 _rightTypeOallTypeConstructors _rightTypeOallValueConstructors _rightTypeOcounter _rightTypeOkindErrors _rightTypeOmiscerrors _rightTypeOnamesInScope _rightTypeOoptions _rightTypeOtypeConstructors _rightTypeOvalueConstructors _rightTypeOwarnings)
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule247 _constructorOperatorIself _lhsIcollectValueConstructors _typeScheme
         _lhsOparameterTypes :: Tps
         _lhsOparameterTypes = rule248 _tps
         _typeScheme = rule249 _tp _tps
         (_tp,_tps) = rule250 _leftTypeItype _lhsIsimpletype _rightTypeItype
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule251 _leftTypeItypevariables _rightTypeItypevariables
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule252 _leftTypeIunboundNames _rightTypeIunboundNames
         _self = rule253 _constructorOperatorIself _leftTypeIself _rangeIself _rightTypeIself
         _lhsOself :: Constructor
         _lhsOself = rule254 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule255 _rightTypeIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule256 _rightTypeIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule257 _rightTypeImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule258 _rightTypeIwarnings
         _leftTypeOallTypeConstructors = rule259 _lhsIallTypeConstructors
         _leftTypeOallValueConstructors = rule260 _lhsIallValueConstructors
         _leftTypeOcounter = rule261 _lhsIcounter
         _leftTypeOkindErrors = rule262 _lhsIkindErrors
         _leftTypeOmiscerrors = rule263 _lhsImiscerrors
         _leftTypeOnamesInScope = rule264 _lhsInamesInScope
         _leftTypeOoptions = rule265 _lhsIoptions
         _leftTypeOtypeConstructors = rule266 _lhsItypeConstructors
         _leftTypeOvalueConstructors = rule267 _lhsIvalueConstructors
         _leftTypeOwarnings = rule268 _lhsIwarnings
         _rightTypeOallTypeConstructors = rule269 _lhsIallTypeConstructors
         _rightTypeOallValueConstructors = rule270 _lhsIallValueConstructors
         _rightTypeOcounter = rule271 _leftTypeIcounter
         _rightTypeOkindErrors = rule272 _leftTypeIkindErrors
         _rightTypeOmiscerrors = rule273 _leftTypeImiscerrors
         _rightTypeOnamesInScope = rule274 _lhsInamesInScope
         _rightTypeOoptions = rule275 _lhsIoptions
         _rightTypeOtypeConstructors = rule276 _lhsItypeConstructors
         _rightTypeOvalueConstructors = rule277 _lhsIvalueConstructors
         _rightTypeOwarnings = rule278 _leftTypeIwarnings
         __result_ = T_Constructor_vOut16 _lhsOcollectValueConstructors _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOparameterTypes _lhsOself _lhsOtypevariables _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Constructor_s17 v16
   {-# INLINE rule247 #-}
   rule247 = \ ((_constructorOperatorIself) :: Name) ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) _typeScheme ->
                                          (_constructorOperatorIself, _typeScheme) : _lhsIcollectValueConstructors
   {-# INLINE rule248 #-}
   rule248 = \ _tps ->
                                _tps
   {-# INLINE rule249 #-}
   rule249 = \ _tp _tps ->
                            generalizeAll ([] .=>. foldr (.->.) _tp _tps)
   {-# INLINE rule250 #-}
   rule250 = \ ((_leftTypeItype) :: Type) ((_lhsIsimpletype) :: SimpleType) ((_rightTypeItype) :: Type) ->
                            convertFromSimpleTypeAndTypes _lhsIsimpletype [_leftTypeItype,_rightTypeItype]
   {-# INLINE rule251 #-}
   rule251 = \ ((_leftTypeItypevariables) :: Names) ((_rightTypeItypevariables) :: Names) ->
     _leftTypeItypevariables  ++  _rightTypeItypevariables
   {-# INLINE rule252 #-}
   rule252 = \ ((_leftTypeIunboundNames) :: Names) ((_rightTypeIunboundNames) :: Names) ->
     _leftTypeIunboundNames ++ _rightTypeIunboundNames
   {-# INLINE rule253 #-}
   rule253 = \ ((_constructorOperatorIself) :: Name) ((_leftTypeIself) :: AnnotatedType) ((_rangeIself) :: Range) ((_rightTypeIself) :: AnnotatedType) ->
     Constructor_Infix _rangeIself _leftTypeIself _constructorOperatorIself _rightTypeIself
   {-# INLINE rule254 #-}
   rule254 = \ _self ->
     _self
   {-# INLINE rule255 #-}
   rule255 = \ ((_rightTypeIcounter) :: Int) ->
     _rightTypeIcounter
   {-# INLINE rule256 #-}
   rule256 = \ ((_rightTypeIkindErrors) :: [Error]) ->
     _rightTypeIkindErrors
   {-# INLINE rule257 #-}
   rule257 = \ ((_rightTypeImiscerrors) :: [Error]) ->
     _rightTypeImiscerrors
   {-# INLINE rule258 #-}
   rule258 = \ ((_rightTypeIwarnings) :: [Warning]) ->
     _rightTypeIwarnings
   {-# INLINE rule259 #-}
   rule259 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule260 #-}
   rule260 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule261 #-}
   rule261 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule262 #-}
   rule262 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule263 #-}
   rule263 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule264 #-}
   rule264 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule265 #-}
   rule265 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule266 #-}
   rule266 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule267 #-}
   rule267 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule268 #-}
   rule268 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule269 #-}
   rule269 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule270 #-}
   rule270 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule271 #-}
   rule271 = \ ((_leftTypeIcounter) :: Int) ->
     _leftTypeIcounter
   {-# INLINE rule272 #-}
   rule272 = \ ((_leftTypeIkindErrors) :: [Error]) ->
     _leftTypeIkindErrors
   {-# INLINE rule273 #-}
   rule273 = \ ((_leftTypeImiscerrors) :: [Error]) ->
     _leftTypeImiscerrors
   {-# INLINE rule274 #-}
   rule274 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule275 #-}
   rule275 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule276 #-}
   rule276 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule277 #-}
   rule277 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule278 #-}
   rule278 = \ ((_leftTypeIwarnings) :: [Warning]) ->
     _leftTypeIwarnings
{-# NOINLINE sem_Constructor_Record #-}
sem_Constructor_Record :: T_Range  -> T_Name  -> T_FieldDeclarations  -> T_Constructor 
sem_Constructor_Record arg_range_ arg_constructor_ arg_fieldDeclarations_ = T_Constructor (return st17) where
   {-# NOINLINE st17 #-}
   st17 = let
      v16 :: T_Constructor_v16 
      v16 = \ (T_Constructor_vIn16 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIsimpletype _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _constructorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructor_))
         _fieldDeclarationsX50 = Control.Monad.Identity.runIdentity (attach_T_FieldDeclarations (arg_fieldDeclarations_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _constructorIself) = inv_Name_s113 _constructorX113 (T_Name_vIn112 )
         (T_FieldDeclarations_vOut49 _fieldDeclarationsIcounter _fieldDeclarationsImiscerrors _fieldDeclarationsIself _fieldDeclarationsIunboundNames) = inv_FieldDeclarations_s50 _fieldDeclarationsX50 (T_FieldDeclarations_vIn49 _fieldDeclarationsOcounter _fieldDeclarationsOmiscerrors _fieldDeclarationsOnamesInScope _fieldDeclarationsOoptions)
         _lhsOparameterTypes :: Tps
         _lhsOparameterTypes = rule279  ()
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule280  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule281 _fieldDeclarationsIunboundNames
         _self = rule282 _constructorIself _fieldDeclarationsIself _rangeIself
         _lhsOself :: Constructor
         _lhsOself = rule283 _self
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule284 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule285 _fieldDeclarationsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule286 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule287 _fieldDeclarationsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule288 _lhsIwarnings
         _fieldDeclarationsOcounter = rule289 _lhsIcounter
         _fieldDeclarationsOmiscerrors = rule290 _lhsImiscerrors
         _fieldDeclarationsOnamesInScope = rule291 _lhsInamesInScope
         _fieldDeclarationsOoptions = rule292 _lhsIoptions
         __result_ = T_Constructor_vOut16 _lhsOcollectValueConstructors _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOparameterTypes _lhsOself _lhsOtypevariables _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Constructor_s17 v16
   {-# INLINE rule279 #-}
   rule279 = \  (_ :: ()) ->
     []
   {-# INLINE rule280 #-}
   rule280 = \  (_ :: ()) ->
     []
   {-# INLINE rule281 #-}
   rule281 = \ ((_fieldDeclarationsIunboundNames) :: Names) ->
     _fieldDeclarationsIunboundNames
   {-# INLINE rule282 #-}
   rule282 = \ ((_constructorIself) :: Name) ((_fieldDeclarationsIself) :: FieldDeclarations) ((_rangeIself) :: Range) ->
     Constructor_Record _rangeIself _constructorIself _fieldDeclarationsIself
   {-# INLINE rule283 #-}
   rule283 = \ _self ->
     _self
   {-# INLINE rule284 #-}
   rule284 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule285 #-}
   rule285 = \ ((_fieldDeclarationsIcounter) :: Int) ->
     _fieldDeclarationsIcounter
   {-# INLINE rule286 #-}
   rule286 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule287 #-}
   rule287 = \ ((_fieldDeclarationsImiscerrors) :: [Error]) ->
     _fieldDeclarationsImiscerrors
   {-# INLINE rule288 #-}
   rule288 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule289 #-}
   rule289 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule290 #-}
   rule290 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule291 #-}
   rule291 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule292 #-}
   rule292 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions

-- Constructors ------------------------------------------------
-- wrapper
data Inh_Constructors  = Inh_Constructors { allTypeConstructors_Inh_Constructors :: (Names), allValueConstructors_Inh_Constructors :: (Names), collectValueConstructors_Inh_Constructors :: ([(Name,TpScheme)]), counter_Inh_Constructors :: (Int), kindErrors_Inh_Constructors :: ([Error]), miscerrors_Inh_Constructors :: ([Error]), namesInScope_Inh_Constructors :: (Names), options_Inh_Constructors :: ([Option]), simpletype_Inh_Constructors :: (SimpleType), typeConstructors_Inh_Constructors :: (M.Map Name Int), valueConstructors_Inh_Constructors :: (M.Map Name TpScheme), warnings_Inh_Constructors :: ([Warning]) }
data Syn_Constructors  = Syn_Constructors { collectValueConstructors_Syn_Constructors :: ([(Name,TpScheme)]), counter_Syn_Constructors :: (Int), kindErrors_Syn_Constructors :: ([Error]), miscerrors_Syn_Constructors :: ([Error]), parameterTypes_Syn_Constructors :: (Tps), self_Syn_Constructors :: (Constructors), typevariables_Syn_Constructors :: (Names), unboundNames_Syn_Constructors :: (Names), warnings_Syn_Constructors :: ([Warning]) }
{-# INLINABLE wrap_Constructors #-}
wrap_Constructors :: T_Constructors  -> Inh_Constructors  -> (Syn_Constructors )
wrap_Constructors (T_Constructors act) (Inh_Constructors _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIsimpletype _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Constructors_vIn19 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIsimpletype _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_Constructors_vOut19 _lhsOcollectValueConstructors _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOparameterTypes _lhsOself _lhsOtypevariables _lhsOunboundNames _lhsOwarnings) <- return (inv_Constructors_s20 sem arg)
        return (Syn_Constructors _lhsOcollectValueConstructors _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOparameterTypes _lhsOself _lhsOtypevariables _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Constructors #-}
sem_Constructors :: Constructors  -> T_Constructors 
sem_Constructors list = Prelude.foldr sem_Constructors_Cons sem_Constructors_Nil (Prelude.map sem_Constructor list)

-- semantic domain
newtype T_Constructors  = T_Constructors {
                                         attach_T_Constructors :: Identity (T_Constructors_s20 )
                                         }
newtype T_Constructors_s20  = C_Constructors_s20 {
                                                 inv_Constructors_s20 :: (T_Constructors_v19 )
                                                 }
data T_Constructors_s21  = C_Constructors_s21
type T_Constructors_v19  = (T_Constructors_vIn19 ) -> (T_Constructors_vOut19 )
data T_Constructors_vIn19  = T_Constructors_vIn19 (Names) (Names) ([(Name,TpScheme)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (SimpleType) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_Constructors_vOut19  = T_Constructors_vOut19 ([(Name,TpScheme)]) (Int) ([Error]) ([Error]) (Tps) (Constructors) (Names) (Names) ([Warning])
{-# NOINLINE sem_Constructors_Cons #-}
sem_Constructors_Cons :: T_Constructor  -> T_Constructors  -> T_Constructors 
sem_Constructors_Cons arg_hd_ arg_tl_ = T_Constructors (return st20) where
   {-# NOINLINE st20 #-}
   st20 = let
      v19 :: T_Constructors_v19 
      v19 = \ (T_Constructors_vIn19 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIsimpletype _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _hdX17 = Control.Monad.Identity.runIdentity (attach_T_Constructor (arg_hd_))
         _tlX20 = Control.Monad.Identity.runIdentity (attach_T_Constructors (arg_tl_))
         (T_Constructor_vOut16 _hdIcollectValueConstructors _hdIcounter _hdIkindErrors _hdImiscerrors _hdIparameterTypes _hdIself _hdItypevariables _hdIunboundNames _hdIwarnings) = inv_Constructor_s17 _hdX17 (T_Constructor_vIn16 _hdOallTypeConstructors _hdOallValueConstructors _hdOcollectValueConstructors _hdOcounter _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOsimpletype _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings)
         (T_Constructors_vOut19 _tlIcollectValueConstructors _tlIcounter _tlIkindErrors _tlImiscerrors _tlIparameterTypes _tlIself _tlItypevariables _tlIunboundNames _tlIwarnings) = inv_Constructors_s20 _tlX20 (T_Constructors_vIn19 _tlOallTypeConstructors _tlOallValueConstructors _tlOcollectValueConstructors _tlOcounter _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOsimpletype _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings)
         _lhsOparameterTypes :: Tps
         _lhsOparameterTypes = rule293 _hdIparameterTypes _tlIparameterTypes
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule294 _hdItypevariables _tlItypevariables
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule295 _hdIunboundNames _tlIunboundNames
         _self = rule296 _hdIself _tlIself
         _lhsOself :: Constructors
         _lhsOself = rule297 _self
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule298 _tlIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule299 _tlIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule300 _tlIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule301 _tlImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule302 _tlIwarnings
         _hdOallTypeConstructors = rule303 _lhsIallTypeConstructors
         _hdOallValueConstructors = rule304 _lhsIallValueConstructors
         _hdOcollectValueConstructors = rule305 _lhsIcollectValueConstructors
         _hdOcounter = rule306 _lhsIcounter
         _hdOkindErrors = rule307 _lhsIkindErrors
         _hdOmiscerrors = rule308 _lhsImiscerrors
         _hdOnamesInScope = rule309 _lhsInamesInScope
         _hdOoptions = rule310 _lhsIoptions
         _hdOsimpletype = rule311 _lhsIsimpletype
         _hdOtypeConstructors = rule312 _lhsItypeConstructors
         _hdOvalueConstructors = rule313 _lhsIvalueConstructors
         _hdOwarnings = rule314 _lhsIwarnings
         _tlOallTypeConstructors = rule315 _lhsIallTypeConstructors
         _tlOallValueConstructors = rule316 _lhsIallValueConstructors
         _tlOcollectValueConstructors = rule317 _hdIcollectValueConstructors
         _tlOcounter = rule318 _hdIcounter
         _tlOkindErrors = rule319 _hdIkindErrors
         _tlOmiscerrors = rule320 _hdImiscerrors
         _tlOnamesInScope = rule321 _lhsInamesInScope
         _tlOoptions = rule322 _lhsIoptions
         _tlOsimpletype = rule323 _lhsIsimpletype
         _tlOtypeConstructors = rule324 _lhsItypeConstructors
         _tlOvalueConstructors = rule325 _lhsIvalueConstructors
         _tlOwarnings = rule326 _hdIwarnings
         __result_ = T_Constructors_vOut19 _lhsOcollectValueConstructors _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOparameterTypes _lhsOself _lhsOtypevariables _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Constructors_s20 v19
   {-# INLINE rule293 #-}
   rule293 = \ ((_hdIparameterTypes) :: Tps) ((_tlIparameterTypes) :: Tps) ->
     _hdIparameterTypes  ++  _tlIparameterTypes
   {-# INLINE rule294 #-}
   rule294 = \ ((_hdItypevariables) :: Names) ((_tlItypevariables) :: Names) ->
     _hdItypevariables  ++  _tlItypevariables
   {-# INLINE rule295 #-}
   rule295 = \ ((_hdIunboundNames) :: Names) ((_tlIunboundNames) :: Names) ->
     _hdIunboundNames ++ _tlIunboundNames
   {-# INLINE rule296 #-}
   rule296 = \ ((_hdIself) :: Constructor) ((_tlIself) :: Constructors) ->
     (:) _hdIself _tlIself
   {-# INLINE rule297 #-}
   rule297 = \ _self ->
     _self
   {-# INLINE rule298 #-}
   rule298 = \ ((_tlIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _tlIcollectValueConstructors
   {-# INLINE rule299 #-}
   rule299 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule300 #-}
   rule300 = \ ((_tlIkindErrors) :: [Error]) ->
     _tlIkindErrors
   {-# INLINE rule301 #-}
   rule301 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule302 #-}
   rule302 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule303 #-}
   rule303 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule304 #-}
   rule304 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule305 #-}
   rule305 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule306 #-}
   rule306 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule307 #-}
   rule307 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule308 #-}
   rule308 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule309 #-}
   rule309 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule310 #-}
   rule310 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule311 #-}
   rule311 = \ ((_lhsIsimpletype) :: SimpleType) ->
     _lhsIsimpletype
   {-# INLINE rule312 #-}
   rule312 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule313 #-}
   rule313 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule314 #-}
   rule314 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule315 #-}
   rule315 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule316 #-}
   rule316 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule317 #-}
   rule317 = \ ((_hdIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _hdIcollectValueConstructors
   {-# INLINE rule318 #-}
   rule318 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule319 #-}
   rule319 = \ ((_hdIkindErrors) :: [Error]) ->
     _hdIkindErrors
   {-# INLINE rule320 #-}
   rule320 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule321 #-}
   rule321 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule322 #-}
   rule322 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule323 #-}
   rule323 = \ ((_lhsIsimpletype) :: SimpleType) ->
     _lhsIsimpletype
   {-# INLINE rule324 #-}
   rule324 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule325 #-}
   rule325 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule326 #-}
   rule326 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_Constructors_Nil #-}
sem_Constructors_Nil ::  T_Constructors 
sem_Constructors_Nil  = T_Constructors (return st20) where
   {-# NOINLINE st20 #-}
   st20 = let
      v19 :: T_Constructors_v19 
      v19 = \ (T_Constructors_vIn19 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIsimpletype _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOparameterTypes :: Tps
         _lhsOparameterTypes = rule327  ()
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule328  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule329  ()
         _self = rule330  ()
         _lhsOself :: Constructors
         _lhsOself = rule331 _self
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule332 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule333 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule334 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule335 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule336 _lhsIwarnings
         __result_ = T_Constructors_vOut19 _lhsOcollectValueConstructors _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOparameterTypes _lhsOself _lhsOtypevariables _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Constructors_s20 v19
   {-# INLINE rule327 #-}
   rule327 = \  (_ :: ()) ->
     []
   {-# INLINE rule328 #-}
   rule328 = \  (_ :: ()) ->
     []
   {-# INLINE rule329 #-}
   rule329 = \  (_ :: ()) ->
     []
   {-# INLINE rule330 #-}
   rule330 = \  (_ :: ()) ->
     []
   {-# INLINE rule331 #-}
   rule331 = \ _self ->
     _self
   {-# INLINE rule332 #-}
   rule332 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule333 #-}
   rule333 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule334 #-}
   rule334 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule335 #-}
   rule335 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule336 #-}
   rule336 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- ContextItem -------------------------------------------------
-- wrapper
data Inh_ContextItem  = Inh_ContextItem { allTypeConstructors_Inh_ContextItem :: (Names), miscerrors_Inh_ContextItem :: ([Error]), options_Inh_ContextItem :: ([Option]), typeConstructors_Inh_ContextItem :: (M.Map Name Int), warnings_Inh_ContextItem :: ([Warning]) }
data Syn_ContextItem  = Syn_ContextItem { contextRanges_Syn_ContextItem :: ([Range]), contextVars_Syn_ContextItem :: ([Name]), miscerrors_Syn_ContextItem :: ([Error]), self_Syn_ContextItem :: (ContextItem), warnings_Syn_ContextItem :: ([Warning]) }
{-# INLINABLE wrap_ContextItem #-}
wrap_ContextItem :: T_ContextItem  -> Inh_ContextItem  -> (Syn_ContextItem )
wrap_ContextItem (T_ContextItem act) (Inh_ContextItem _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_ContextItem_vIn22 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings
        (T_ContextItem_vOut22 _lhsOcontextRanges _lhsOcontextVars _lhsOmiscerrors _lhsOself _lhsOwarnings) <- return (inv_ContextItem_s23 sem arg)
        return (Syn_ContextItem _lhsOcontextRanges _lhsOcontextVars _lhsOmiscerrors _lhsOself _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_ContextItem #-}
sem_ContextItem :: ContextItem  -> T_ContextItem 
sem_ContextItem ( ContextItem_ContextItem range_ name_ types_ ) = sem_ContextItem_ContextItem ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Types types_ )

-- semantic domain
newtype T_ContextItem  = T_ContextItem {
                                       attach_T_ContextItem :: Identity (T_ContextItem_s23 )
                                       }
newtype T_ContextItem_s23  = C_ContextItem_s23 {
                                               inv_ContextItem_s23 :: (T_ContextItem_v22 )
                                               }
data T_ContextItem_s24  = C_ContextItem_s24
type T_ContextItem_v22  = (T_ContextItem_vIn22 ) -> (T_ContextItem_vOut22 )
data T_ContextItem_vIn22  = T_ContextItem_vIn22 (Names) ([Error]) ([Option]) (M.Map Name Int) ([Warning])
data T_ContextItem_vOut22  = T_ContextItem_vOut22 ([Range]) ([Name]) ([Error]) (ContextItem) ([Warning])
{-# NOINLINE sem_ContextItem_ContextItem #-}
sem_ContextItem_ContextItem :: T_Range  -> T_Name  -> T_Types  -> T_ContextItem 
sem_ContextItem_ContextItem arg_range_ arg_name_ arg_types_ = T_ContextItem (return st23) where
   {-# NOINLINE st23 #-}
   st23 = let
      v22 :: T_ContextItem_v22 
      v22 = \ (T_ContextItem_vIn22 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _typesX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_types_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Types_vOut166 _typesImiscerrors _typesIself _typesItypevariables _typesIwarnings) = inv_Types_s167 _typesX167 (T_Types_vIn166 _typesOallTypeConstructors _typesOmiscerrors _typesOoptions _typesOtypeConstructors _typesOwarnings)
         _lhsOcontextRanges :: [Range]
         _lhsOcontextRanges = rule337 _rangeIself
         _lhsOcontextVars :: [Name]
         _lhsOcontextVars = rule338 _typesItypevariables
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule339 _nameIself _typesImiscerrors
         _tyconEnv = rule340  ()
         _self = rule341 _nameIself _rangeIself _typesIself
         _lhsOself :: ContextItem
         _lhsOself = rule342 _self
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule343 _typesIwarnings
         _typesOallTypeConstructors = rule344 _lhsIallTypeConstructors
         _typesOmiscerrors = rule345 _lhsImiscerrors
         _typesOoptions = rule346 _lhsIoptions
         _typesOtypeConstructors = rule347 _lhsItypeConstructors
         _typesOwarnings = rule348 _lhsIwarnings
         __result_ = T_ContextItem_vOut22 _lhsOcontextRanges _lhsOcontextVars _lhsOmiscerrors _lhsOself _lhsOwarnings
         in __result_ )
     in C_ContextItem_s23 v22
   {-# INLINE rule337 #-}
   rule337 = \ ((_rangeIself) :: Range) ->
                                      [_rangeIself]
   {-# INLINE rule338 #-}
   rule338 = \ ((_typesItypevariables) :: Names) ->
                                    _typesItypevariables
   {-# INLINE rule339 #-}
   rule339 = \ ((_nameIself) :: Name) ((_typesImiscerrors) :: [Error]) ->
                                   if elem (getNameName _nameIself) (M.keys standardClasses)
                                      then _typesImiscerrors
                                      else UnknownClass _nameIself : _typesImiscerrors
   {-# INLINE rule340 #-}
   rule340 = \  (_ :: ()) ->
                                        internalError "PartialSyntax.ag" "n/a" "ContextItem.ContextItem"
   {-# INLINE rule341 #-}
   rule341 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ((_typesIself) :: Types) ->
     ContextItem_ContextItem _rangeIself _nameIself _typesIself
   {-# INLINE rule342 #-}
   rule342 = \ _self ->
     _self
   {-# INLINE rule343 #-}
   rule343 = \ ((_typesIwarnings) :: [Warning]) ->
     _typesIwarnings
   {-# INLINE rule344 #-}
   rule344 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule345 #-}
   rule345 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule346 #-}
   rule346 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule347 #-}
   rule347 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule348 #-}
   rule348 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- ContextItems ------------------------------------------------
-- wrapper
data Inh_ContextItems  = Inh_ContextItems { allTypeConstructors_Inh_ContextItems :: (Names), miscerrors_Inh_ContextItems :: ([Error]), options_Inh_ContextItems :: ([Option]), typeConstructors_Inh_ContextItems :: (M.Map Name Int), warnings_Inh_ContextItems :: ([Warning]) }
data Syn_ContextItems  = Syn_ContextItems { contextRanges_Syn_ContextItems :: ([Range]), contextVars_Syn_ContextItems :: ([Name]), miscerrors_Syn_ContextItems :: ([Error]), self_Syn_ContextItems :: (ContextItems), warnings_Syn_ContextItems :: ([Warning]) }
{-# INLINABLE wrap_ContextItems #-}
wrap_ContextItems :: T_ContextItems  -> Inh_ContextItems  -> (Syn_ContextItems )
wrap_ContextItems (T_ContextItems act) (Inh_ContextItems _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_ContextItems_vIn25 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings
        (T_ContextItems_vOut25 _lhsOcontextRanges _lhsOcontextVars _lhsOmiscerrors _lhsOself _lhsOwarnings) <- return (inv_ContextItems_s26 sem arg)
        return (Syn_ContextItems _lhsOcontextRanges _lhsOcontextVars _lhsOmiscerrors _lhsOself _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_ContextItems #-}
sem_ContextItems :: ContextItems  -> T_ContextItems 
sem_ContextItems list = Prelude.foldr sem_ContextItems_Cons sem_ContextItems_Nil (Prelude.map sem_ContextItem list)

-- semantic domain
newtype T_ContextItems  = T_ContextItems {
                                         attach_T_ContextItems :: Identity (T_ContextItems_s26 )
                                         }
newtype T_ContextItems_s26  = C_ContextItems_s26 {
                                                 inv_ContextItems_s26 :: (T_ContextItems_v25 )
                                                 }
data T_ContextItems_s27  = C_ContextItems_s27
type T_ContextItems_v25  = (T_ContextItems_vIn25 ) -> (T_ContextItems_vOut25 )
data T_ContextItems_vIn25  = T_ContextItems_vIn25 (Names) ([Error]) ([Option]) (M.Map Name Int) ([Warning])
data T_ContextItems_vOut25  = T_ContextItems_vOut25 ([Range]) ([Name]) ([Error]) (ContextItems) ([Warning])
{-# NOINLINE sem_ContextItems_Cons #-}
sem_ContextItems_Cons :: T_ContextItem  -> T_ContextItems  -> T_ContextItems 
sem_ContextItems_Cons arg_hd_ arg_tl_ = T_ContextItems (return st26) where
   {-# NOINLINE st26 #-}
   st26 = let
      v25 :: T_ContextItems_v25 
      v25 = \ (T_ContextItems_vIn25 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _hdX23 = Control.Monad.Identity.runIdentity (attach_T_ContextItem (arg_hd_))
         _tlX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_tl_))
         (T_ContextItem_vOut22 _hdIcontextRanges _hdIcontextVars _hdImiscerrors _hdIself _hdIwarnings) = inv_ContextItem_s23 _hdX23 (T_ContextItem_vIn22 _hdOallTypeConstructors _hdOmiscerrors _hdOoptions _hdOtypeConstructors _hdOwarnings)
         (T_ContextItems_vOut25 _tlIcontextRanges _tlIcontextVars _tlImiscerrors _tlIself _tlIwarnings) = inv_ContextItems_s26 _tlX26 (T_ContextItems_vIn25 _tlOallTypeConstructors _tlOmiscerrors _tlOoptions _tlOtypeConstructors _tlOwarnings)
         _lhsOcontextRanges :: [Range]
         _lhsOcontextRanges = rule349 _hdIcontextRanges _tlIcontextRanges
         _lhsOcontextVars :: [Name]
         _lhsOcontextVars = rule350 _hdIcontextVars _tlIcontextVars
         _self = rule351 _hdIself _tlIself
         _lhsOself :: ContextItems
         _lhsOself = rule352 _self
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule353 _tlImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule354 _tlIwarnings
         _hdOallTypeConstructors = rule355 _lhsIallTypeConstructors
         _hdOmiscerrors = rule356 _lhsImiscerrors
         _hdOoptions = rule357 _lhsIoptions
         _hdOtypeConstructors = rule358 _lhsItypeConstructors
         _hdOwarnings = rule359 _lhsIwarnings
         _tlOallTypeConstructors = rule360 _lhsIallTypeConstructors
         _tlOmiscerrors = rule361 _hdImiscerrors
         _tlOoptions = rule362 _lhsIoptions
         _tlOtypeConstructors = rule363 _lhsItypeConstructors
         _tlOwarnings = rule364 _hdIwarnings
         __result_ = T_ContextItems_vOut25 _lhsOcontextRanges _lhsOcontextVars _lhsOmiscerrors _lhsOself _lhsOwarnings
         in __result_ )
     in C_ContextItems_s26 v25
   {-# INLINE rule349 #-}
   rule349 = \ ((_hdIcontextRanges) :: [Range]) ((_tlIcontextRanges) :: [Range]) ->
                                _hdIcontextRanges ++ _tlIcontextRanges
   {-# INLINE rule350 #-}
   rule350 = \ ((_hdIcontextVars) :: [Name]) ((_tlIcontextVars) :: [Name]) ->
     _hdIcontextVars  ++  _tlIcontextVars
   {-# INLINE rule351 #-}
   rule351 = \ ((_hdIself) :: ContextItem) ((_tlIself) :: ContextItems) ->
     (:) _hdIself _tlIself
   {-# INLINE rule352 #-}
   rule352 = \ _self ->
     _self
   {-# INLINE rule353 #-}
   rule353 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule354 #-}
   rule354 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule355 #-}
   rule355 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule356 #-}
   rule356 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule357 #-}
   rule357 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule358 #-}
   rule358 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule359 #-}
   rule359 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule360 #-}
   rule360 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule361 #-}
   rule361 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule362 #-}
   rule362 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule363 #-}
   rule363 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule364 #-}
   rule364 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_ContextItems_Nil #-}
sem_ContextItems_Nil ::  T_ContextItems 
sem_ContextItems_Nil  = T_ContextItems (return st26) where
   {-# NOINLINE st26 #-}
   st26 = let
      v25 :: T_ContextItems_v25 
      v25 = \ (T_ContextItems_vIn25 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _lhsOcontextRanges :: [Range]
         _lhsOcontextRanges = rule365  ()
         _lhsOcontextVars :: [Name]
         _lhsOcontextVars = rule366  ()
         _self = rule367  ()
         _lhsOself :: ContextItems
         _lhsOself = rule368 _self
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule369 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule370 _lhsIwarnings
         __result_ = T_ContextItems_vOut25 _lhsOcontextRanges _lhsOcontextVars _lhsOmiscerrors _lhsOself _lhsOwarnings
         in __result_ )
     in C_ContextItems_s26 v25
   {-# INLINE rule365 #-}
   rule365 = \  (_ :: ()) ->
                                []
   {-# INLINE rule366 #-}
   rule366 = \  (_ :: ()) ->
     []
   {-# INLINE rule367 #-}
   rule367 = \  (_ :: ()) ->
     []
   {-# INLINE rule368 #-}
   rule368 = \ _self ->
     _self
   {-# INLINE rule369 #-}
   rule369 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule370 #-}
   rule370 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Declaration -------------------------------------------------
-- wrapper
data Inh_Declaration  = Inh_Declaration { allTypeConstructors_Inh_Declaration :: (Names), allValueConstructors_Inh_Declaration :: (Names), classEnvironment_Inh_Declaration :: (ClassEnvironment), collectScopeInfos_Inh_Declaration :: ([(ScopeInfo, Entity)]), collectTypeConstructors_Inh_Declaration :: ([(Name,Int)]), collectTypeSynonyms_Inh_Declaration :: ([(Name,(Int,Tps -> Tp))]), collectValueConstructors_Inh_Declaration :: ([(Name,TpScheme)]), counter_Inh_Declaration :: (Int), kindErrors_Inh_Declaration :: ([Error]), miscerrors_Inh_Declaration :: ([Error]), namesInScope_Inh_Declaration :: (Names), operatorFixities_Inh_Declaration :: ([(Name,(Int,Assoc))]), options_Inh_Declaration :: ([Option]), orderedTypeSynonyms_Inh_Declaration :: (OrderedTypeSynonyms), previousWasAlsoFB_Inh_Declaration :: (Maybe Name), suspiciousFBs_Inh_Declaration :: ([(Name,Name)]), typeConstructors_Inh_Declaration :: (M.Map Name Int), typeSignatures_Inh_Declaration :: ([(Name,TpScheme)]), valueConstructors_Inh_Declaration :: (M.Map Name TpScheme), warnings_Inh_Declaration :: ([Warning]) }
data Syn_Declaration  = Syn_Declaration { collectInstances_Syn_Declaration :: ([(Name, Instance)]), collectScopeInfos_Syn_Declaration :: ([(ScopeInfo, Entity)]), collectTypeConstructors_Syn_Declaration :: ([(Name,Int)]), collectTypeSynonyms_Syn_Declaration :: ([(Name,(Int,Tps -> Tp))]), collectValueConstructors_Syn_Declaration :: ([(Name,TpScheme)]), counter_Syn_Declaration :: (Int), declVarNames_Syn_Declaration :: (Names), kindErrors_Syn_Declaration :: ([Error]), miscerrors_Syn_Declaration :: ([Error]), operatorFixities_Syn_Declaration :: ([(Name,(Int,Assoc))]), previousWasAlsoFB_Syn_Declaration :: (Maybe Name), restrictedNames_Syn_Declaration :: (Names), self_Syn_Declaration :: (Declaration), suspiciousFBs_Syn_Declaration :: ([(Name,Name)]), typeSignatures_Syn_Declaration :: ([(Name,TpScheme)]), unboundNames_Syn_Declaration :: (Names), warnings_Syn_Declaration :: ([Warning]) }
{-# INLINABLE wrap_Declaration #-}
wrap_Declaration :: T_Declaration  -> Inh_Declaration  -> (Syn_Declaration )
wrap_Declaration (T_Declaration act) (Inh_Declaration _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings
        (T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings) <- return (inv_Declaration_s29 sem arg)
        return (Syn_Declaration _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Declaration #-}
sem_Declaration :: Declaration  -> T_Declaration 
sem_Declaration ( Declaration_Hole range_ id_ ) = sem_Declaration_Hole ( sem_Range range_ ) id_
sem_Declaration ( Declaration_Type range_ simpletype_ type_ ) = sem_Declaration_Type ( sem_Range range_ ) ( sem_SimpleType simpletype_ ) ( sem_Type type_ )
sem_Declaration ( Declaration_Data range_ context_ simpletype_ constructors_ derivings_ ) = sem_Declaration_Data ( sem_Range range_ ) ( sem_ContextItems context_ ) ( sem_SimpleType simpletype_ ) ( sem_Constructors constructors_ ) ( sem_Names derivings_ )
sem_Declaration ( Declaration_Newtype range_ context_ simpletype_ constructor_ derivings_ ) = sem_Declaration_Newtype ( sem_Range range_ ) ( sem_ContextItems context_ ) ( sem_SimpleType simpletype_ ) ( sem_Constructor constructor_ ) ( sem_Names derivings_ )
sem_Declaration ( Declaration_Class range_ context_ simpletype_ where_ ) = sem_Declaration_Class ( sem_Range range_ ) ( sem_ContextItems context_ ) ( sem_SimpleType simpletype_ ) ( sem_MaybeDeclarations where_ )
sem_Declaration ( Declaration_Instance range_ context_ name_ types_ where_ ) = sem_Declaration_Instance ( sem_Range range_ ) ( sem_ContextItems context_ ) ( sem_Name name_ ) ( sem_Types types_ ) ( sem_MaybeDeclarations where_ )
sem_Declaration ( Declaration_Default range_ types_ ) = sem_Declaration_Default ( sem_Range range_ ) ( sem_Types types_ )
sem_Declaration ( Declaration_FunctionBindings range_ bindings_ ) = sem_Declaration_FunctionBindings ( sem_Range range_ ) ( sem_FunctionBindings bindings_ )
sem_Declaration ( Declaration_PatternBinding range_ pattern_ righthandside_ ) = sem_Declaration_PatternBinding ( sem_Range range_ ) ( sem_Pattern pattern_ ) ( sem_RightHandSide righthandside_ )
sem_Declaration ( Declaration_TypeSignature range_ names_ type_ ) = sem_Declaration_TypeSignature ( sem_Range range_ ) ( sem_Names names_ ) ( sem_Type type_ )
sem_Declaration ( Declaration_Fixity range_ fixity_ priority_ operators_ ) = sem_Declaration_Fixity ( sem_Range range_ ) ( sem_Fixity fixity_ ) ( sem_MaybeInt priority_ ) ( sem_Names operators_ )
sem_Declaration ( Declaration_Empty range_ ) = sem_Declaration_Empty ( sem_Range range_ )

-- semantic domain
newtype T_Declaration  = T_Declaration {
                                       attach_T_Declaration :: Identity (T_Declaration_s29 )
                                       }
newtype T_Declaration_s29  = C_Declaration_s29 {
                                               inv_Declaration_s29 :: (T_Declaration_v28 )
                                               }
data T_Declaration_s30  = C_Declaration_s30
type T_Declaration_v28  = (T_Declaration_vIn28 ) -> (T_Declaration_vOut28 )
data T_Declaration_vIn28  = T_Declaration_vIn28 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) ([(Name,Int)]) ([(Name,(Int,Tps -> Tp))]) ([(Name,TpScheme)]) (Int) ([Error]) ([Error]) (Names) ([(Name,(Int,Assoc))]) ([Option]) (OrderedTypeSynonyms) (Maybe Name) ([(Name,Name)]) (M.Map Name Int) ([(Name,TpScheme)]) (M.Map Name TpScheme) ([Warning])
data T_Declaration_vOut28  = T_Declaration_vOut28 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) ([(Name,Int)]) ([(Name,(Int,Tps -> Tp))]) ([(Name,TpScheme)]) (Int) (Names) ([Error]) ([Error]) ([(Name,(Int,Assoc))]) (Maybe Name) (Names) (Declaration) ([(Name,Name)]) ([(Name,TpScheme)]) (Names) ([Warning])
{-# NOINLINE sem_Declaration_Hole #-}
sem_Declaration_Hole :: T_Range  -> (Integer) -> T_Declaration 
sem_Declaration_Hole arg_range_ arg_id_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule371  ()
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule372  ()
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule373  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule374  ()
         _self = rule375 _rangeIself arg_id_
         _lhsOself :: Declaration
         _lhsOself = rule376 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule377 _lhsIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule378 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule379 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule380 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule381 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule382 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule383 _lhsImiscerrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule384 _lhsIoperatorFixities
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule385 _lhsIpreviousWasAlsoFB
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule386 _lhsIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule387 _lhsItypeSignatures
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule388 _lhsIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule371 #-}
   rule371 = \  (_ :: ()) ->
     []
   {-# INLINE rule372 #-}
   rule372 = \  (_ :: ()) ->
     []
   {-# INLINE rule373 #-}
   rule373 = \  (_ :: ()) ->
     []
   {-# INLINE rule374 #-}
   rule374 = \  (_ :: ()) ->
     []
   {-# INLINE rule375 #-}
   rule375 = \ ((_rangeIself) :: Range) id_ ->
     Declaration_Hole _rangeIself id_
   {-# INLINE rule376 #-}
   rule376 = \ _self ->
     _self
   {-# INLINE rule377 #-}
   rule377 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule378 #-}
   rule378 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule379 #-}
   rule379 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule380 #-}
   rule380 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule381 #-}
   rule381 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule382 #-}
   rule382 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule383 #-}
   rule383 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule384 #-}
   rule384 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule385 #-}
   rule385 = \ ((_lhsIpreviousWasAlsoFB) :: Maybe Name) ->
     _lhsIpreviousWasAlsoFB
   {-# INLINE rule386 #-}
   rule386 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule387 #-}
   rule387 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule388 #-}
   rule388 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Declaration_Type #-}
sem_Declaration_Type :: T_Range  -> T_SimpleType  -> T_Type  -> T_Declaration 
sem_Declaration_Type arg_range_ arg_simpletype_ arg_type_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_SimpleType_vOut151 _simpletypeIname _simpletypeIself _simpletypeItypevariables) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_Type_vOut163 _typeIcontextRange _typeImiscerrors _typeIself _typeItypevariables _typeIwarnings) = inv_Type_s164 _typeX164 (T_Type_vIn163 _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings)
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule389 _lhsIcollectTypeSynonyms _simpletypeIname _typeSynonymInfo
         _typeSynonymInfo = rule390 _simpletypeItypevariables _typeIself
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule391 _lhsIkindErrors _newErrors
         _newErrors = rule392 _lhsIallValueConstructors _lhsInamesInScope _lhsItypeConstructors _typeIself
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule393 _lhsIwarnings _unused
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule394  ()
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule395 _doubles _lhsImiscerrors _simpletypeItypevariables _undef
         _unused = rule396 _simpletypeItypevariables _typeItypevariables
         _doubles = rule397 _simpletypeItypevariables
         _undef = rule398 _simpletypeItypevariables _typeItypevariables
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule399  ()
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule400  ()
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule401  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule402  ()
         _self = rule403 _rangeIself _simpletypeIself _typeIself
         _lhsOself :: Declaration
         _lhsOself = rule404 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule405 _lhsIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule406 _lhsIcollectTypeConstructors
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule407 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule408 _lhsIcounter
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule409 _lhsIoperatorFixities
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule410 _lhsIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule411 _lhsItypeSignatures
         _typeOallTypeConstructors = rule412 _lhsIallTypeConstructors
         _typeOmiscerrors = rule413 _lhsImiscerrors
         _typeOoptions = rule414 _lhsIoptions
         _typeOtypeConstructors = rule415 _lhsItypeConstructors
         _typeOwarnings = rule416 _lhsIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule389 #-}
   rule389 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ((_simpletypeIname) :: Name) _typeSynonymInfo ->
                                         (_simpletypeIname, _typeSynonymInfo) : _lhsIcollectTypeSynonyms
   {-# INLINE rule390 #-}
   rule390 = \ ((_simpletypeItypevariables) :: Names) ((_typeIself) :: Type) ->
                                     (length _simpletypeItypevariables,\tps -> makeTpFromType (zip _simpletypeItypevariables tps) _typeIself)
   {-# INLINE rule391 #-}
   rule391 = \ ((_lhsIkindErrors) :: [Error]) _newErrors ->
                                         _newErrors ++ _lhsIkindErrors
   {-# INLINE rule392 #-}
   rule392 = \ ((_lhsIallValueConstructors) :: Names) ((_lhsInamesInScope) :: Names) ((_lhsItypeConstructors) :: M.Map Name Int) ((_typeIself) :: Type) ->
                                         checkType _lhsItypeConstructors (_lhsInamesInScope ++ _lhsIallValueConstructors) _typeIself
   {-# INLINE rule393 #-}
   rule393 = \ ((_lhsIwarnings) :: [Warning]) _unused ->
                           map (Unused TypeVariable) _unused ++ _lhsIwarnings
   {-# INLINE rule394 #-}
   rule394 = \  (_ :: ()) ->
                                                   Nothing
   {-# INLINE rule395 #-}
   rule395 = \ _doubles ((_lhsImiscerrors) :: [Error]) ((_simpletypeItypevariables) :: Names) _undef ->
                                  concat [ makeDuplicated TypeVariable _doubles
                                         , makeUndefined TypeVariable _undef _simpletypeItypevariables
                                         , _lhsImiscerrors
                                         ]
   {-# INLINE rule396 #-}
   rule396 = \ ((_simpletypeItypevariables) :: Names) ((_typeItypevariables) :: Names) ->
                               filter (`notElem` _typeItypevariables)       _simpletypeItypevariables
   {-# INLINE rule397 #-}
   rule397 = \ ((_simpletypeItypevariables) :: Names) ->
                               filter ((>1) . length) . group . sort $      _simpletypeItypevariables
   {-# INLINE rule398 #-}
   rule398 = \ ((_simpletypeItypevariables) :: Names) ((_typeItypevariables) :: Names) ->
                               filter (`notElem` _simpletypeItypevariables) _typeItypevariables
   {-# INLINE rule399 #-}
   rule399 = \  (_ :: ()) ->
     []
   {-# INLINE rule400 #-}
   rule400 = \  (_ :: ()) ->
     []
   {-# INLINE rule401 #-}
   rule401 = \  (_ :: ()) ->
     []
   {-# INLINE rule402 #-}
   rule402 = \  (_ :: ()) ->
     []
   {-# INLINE rule403 #-}
   rule403 = \ ((_rangeIself) :: Range) ((_simpletypeIself) :: SimpleType) ((_typeIself) :: Type) ->
     Declaration_Type _rangeIself _simpletypeIself _typeIself
   {-# INLINE rule404 #-}
   rule404 = \ _self ->
     _self
   {-# INLINE rule405 #-}
   rule405 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule406 #-}
   rule406 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule407 #-}
   rule407 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule408 #-}
   rule408 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule409 #-}
   rule409 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule410 #-}
   rule410 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule411 #-}
   rule411 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule412 #-}
   rule412 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule413 #-}
   rule413 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule414 #-}
   rule414 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule415 #-}
   rule415 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule416 #-}
   rule416 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Declaration_Data #-}
sem_Declaration_Data :: T_Range  -> T_ContextItems  -> T_SimpleType  -> T_Constructors  -> T_Names  -> T_Declaration 
sem_Declaration_Data arg_range_ arg_context_ arg_simpletype_ arg_constructors_ arg_derivings_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _constructorsX20 = Control.Monad.Identity.runIdentity (attach_T_Constructors (arg_constructors_))
         _derivingsX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_derivings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextIcontextRanges _contextIcontextVars _contextImiscerrors _contextIself _contextIwarnings) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 _contextOallTypeConstructors _contextOmiscerrors _contextOoptions _contextOtypeConstructors _contextOwarnings)
         (T_SimpleType_vOut151 _simpletypeIname _simpletypeIself _simpletypeItypevariables) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_Constructors_vOut19 _constructorsIcollectValueConstructors _constructorsIcounter _constructorsIkindErrors _constructorsImiscerrors _constructorsIparameterTypes _constructorsIself _constructorsItypevariables _constructorsIunboundNames _constructorsIwarnings) = inv_Constructors_s20 _constructorsX20 (T_Constructors_vIn19 _constructorsOallTypeConstructors _constructorsOallValueConstructors _constructorsOcollectValueConstructors _constructorsOcounter _constructorsOkindErrors _constructorsOmiscerrors _constructorsOnamesInScope _constructorsOoptions _constructorsOsimpletype _constructorsOtypeConstructors _constructorsOvalueConstructors _constructorsOwarnings)
         (T_Names_vOut115 _derivingsIself) = inv_Names_s116 _derivingsX116 (T_Names_vIn115 )
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule417 _lhsIcollectTypeConstructors _simpletypeIname _simpletypeItypevariables
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule418 _derivingsIself _simpletypeIname _simpletypeItypevariables
         _constructorsOsimpletype = rule419 _simpletypeIself
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule420 _lhsIwarnings _unused
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule421  ()
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule422 _cantDer _doubles _lhsImiscerrors _simpletypeItypevariables _undef _unknCls
         _unused = rule423 _constructorsItypevariables _simpletypeItypevariables
         _doubles = rule424 _simpletypeItypevariables
         _undef = rule425 _constructorsItypevariables _simpletypeItypevariables
         _unknCls = rule426 _derivingsIself
         _cantDer = rule427 _constructorsIparameterTypes _derivingsIself _lhsIclassEnvironment _lhsIorderedTypeSynonyms
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule428  ()
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule429  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule430 _constructorsIunboundNames
         _self = rule431 _constructorsIself _contextIself _derivingsIself _rangeIself _simpletypeIself
         _lhsOself :: Declaration
         _lhsOself = rule432 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule433 _lhsIcollectScopeInfos
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule434 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule435 _constructorsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule436 _constructorsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule437 _constructorsIkindErrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule438 _lhsIoperatorFixities
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule439 _lhsIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule440 _lhsItypeSignatures
         _contextOallTypeConstructors = rule441 _lhsIallTypeConstructors
         _contextOmiscerrors = rule442 _lhsImiscerrors
         _contextOoptions = rule443 _lhsIoptions
         _contextOtypeConstructors = rule444 _lhsItypeConstructors
         _contextOwarnings = rule445 _lhsIwarnings
         _constructorsOallTypeConstructors = rule446 _lhsIallTypeConstructors
         _constructorsOallValueConstructors = rule447 _lhsIallValueConstructors
         _constructorsOcollectValueConstructors = rule448 _lhsIcollectValueConstructors
         _constructorsOcounter = rule449 _lhsIcounter
         _constructorsOkindErrors = rule450 _lhsIkindErrors
         _constructorsOmiscerrors = rule451 _contextImiscerrors
         _constructorsOnamesInScope = rule452 _lhsInamesInScope
         _constructorsOoptions = rule453 _lhsIoptions
         _constructorsOtypeConstructors = rule454 _lhsItypeConstructors
         _constructorsOvalueConstructors = rule455 _lhsIvalueConstructors
         _constructorsOwarnings = rule456 _contextIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule417 #-}
   rule417 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ((_simpletypeIname) :: Name) ((_simpletypeItypevariables) :: Names) ->
                                             (_simpletypeIname,length _simpletypeItypevariables) : _lhsIcollectTypeConstructors
   {-# INLINE rule418 #-}
   rule418 = \ ((_derivingsIself) :: Names) ((_simpletypeIname) :: Name) ((_simpletypeItypevariables) :: Names) ->
                                  [ (cl, makeInstance (show cl) (length _simpletypeItypevariables) (show _simpletypeIname) )
                                  | cl <- _derivingsIself
                                  ]
   {-# INLINE rule419 #-}
   rule419 = \ ((_simpletypeIself) :: SimpleType) ->
                                           _simpletypeIself
   {-# INLINE rule420 #-}
   rule420 = \ ((_lhsIwarnings) :: [Warning]) _unused ->
                           map (Unused TypeVariable) _unused ++ _lhsIwarnings
   {-# INLINE rule421 #-}
   rule421 = \  (_ :: ()) ->
                                                   Nothing
   {-# INLINE rule422 #-}
   rule422 = \ _cantDer _doubles ((_lhsImiscerrors) :: [Error]) ((_simpletypeItypevariables) :: Names) _undef _unknCls ->
                                  concat [ makeDuplicated TypeVariable _doubles
                                         , makeUndefined TypeVariable _undef _simpletypeItypevariables
                                         , _lhsImiscerrors
                                         , _unknCls
                                         , if null _unknCls then _cantDer else []
                                         ]
   {-# INLINE rule423 #-}
   rule423 = \ ((_constructorsItypevariables) :: Names) ((_simpletypeItypevariables) :: Names) ->
                               filter (`notElem` _constructorsItypevariables) _simpletypeItypevariables
   {-# INLINE rule424 #-}
   rule424 = \ ((_simpletypeItypevariables) :: Names) ->
                               filter ((>1) . length) . group . sort $        _simpletypeItypevariables
   {-# INLINE rule425 #-}
   rule425 = \ ((_constructorsItypevariables) :: Names) ((_simpletypeItypevariables) :: Names) ->
                               filter (`notElem` _simpletypeItypevariables)   _constructorsItypevariables
   {-# INLINE rule426 #-}
   rule426 = \ ((_derivingsIself) :: Names) ->
                               [ if className `elem` [ "Num", "Enum", "Ord" ]
                                  then NonDerivableClass c
                                  else UnknownClass c
                               | c <- _derivingsIself, let className = show c
                               , className `notElem` ["Show", "Eq"]
                               ]
   {-# INLINE rule427 #-}
   rule427 = \ ((_constructorsIparameterTypes) :: Tps) ((_derivingsIself) :: Names) ((_lhsIclassEnvironment) :: ClassEnvironment) ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
                               [ CannotDerive c [ tp | ReductionError (Predicate _ tp) <- errs ]
                               | c <- _derivingsIself
                               , let preds     = map (Predicate (show c)) _constructorsIparameterTypes
                                     (_, errs) = contextReduction _lhsIorderedTypeSynonyms _lhsIclassEnvironment preds
                               , not (null errs)
                               ]
   {-# INLINE rule428 #-}
   rule428 = \  (_ :: ()) ->
     []
   {-# INLINE rule429 #-}
   rule429 = \  (_ :: ()) ->
     []
   {-# INLINE rule430 #-}
   rule430 = \ ((_constructorsIunboundNames) :: Names) ->
     _constructorsIunboundNames
   {-# INLINE rule431 #-}
   rule431 = \ ((_constructorsIself) :: Constructors) ((_contextIself) :: ContextItems) ((_derivingsIself) :: Names) ((_rangeIself) :: Range) ((_simpletypeIself) :: SimpleType) ->
     Declaration_Data _rangeIself _contextIself _simpletypeIself _constructorsIself _derivingsIself
   {-# INLINE rule432 #-}
   rule432 = \ _self ->
     _self
   {-# INLINE rule433 #-}
   rule433 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule434 #-}
   rule434 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule435 #-}
   rule435 = \ ((_constructorsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _constructorsIcollectValueConstructors
   {-# INLINE rule436 #-}
   rule436 = \ ((_constructorsIcounter) :: Int) ->
     _constructorsIcounter
   {-# INLINE rule437 #-}
   rule437 = \ ((_constructorsIkindErrors) :: [Error]) ->
     _constructorsIkindErrors
   {-# INLINE rule438 #-}
   rule438 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule439 #-}
   rule439 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule440 #-}
   rule440 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule441 #-}
   rule441 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule442 #-}
   rule442 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule443 #-}
   rule443 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule444 #-}
   rule444 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule445 #-}
   rule445 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule446 #-}
   rule446 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule447 #-}
   rule447 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule448 #-}
   rule448 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule449 #-}
   rule449 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule450 #-}
   rule450 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule451 #-}
   rule451 = \ ((_contextImiscerrors) :: [Error]) ->
     _contextImiscerrors
   {-# INLINE rule452 #-}
   rule452 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule453 #-}
   rule453 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule454 #-}
   rule454 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule455 #-}
   rule455 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule456 #-}
   rule456 = \ ((_contextIwarnings) :: [Warning]) ->
     _contextIwarnings
{-# NOINLINE sem_Declaration_Newtype #-}
sem_Declaration_Newtype :: T_Range  -> T_ContextItems  -> T_SimpleType  -> T_Constructor  -> T_Names  -> T_Declaration 
sem_Declaration_Newtype arg_range_ arg_context_ arg_simpletype_ arg_constructor_ arg_derivings_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _constructorX17 = Control.Monad.Identity.runIdentity (attach_T_Constructor (arg_constructor_))
         _derivingsX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_derivings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextIcontextRanges _contextIcontextVars _contextImiscerrors _contextIself _contextIwarnings) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 _contextOallTypeConstructors _contextOmiscerrors _contextOoptions _contextOtypeConstructors _contextOwarnings)
         (T_SimpleType_vOut151 _simpletypeIname _simpletypeIself _simpletypeItypevariables) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_Constructor_vOut16 _constructorIcollectValueConstructors _constructorIcounter _constructorIkindErrors _constructorImiscerrors _constructorIparameterTypes _constructorIself _constructorItypevariables _constructorIunboundNames _constructorIwarnings) = inv_Constructor_s17 _constructorX17 (T_Constructor_vIn16 _constructorOallTypeConstructors _constructorOallValueConstructors _constructorOcollectValueConstructors _constructorOcounter _constructorOkindErrors _constructorOmiscerrors _constructorOnamesInScope _constructorOoptions _constructorOsimpletype _constructorOtypeConstructors _constructorOvalueConstructors _constructorOwarnings)
         (T_Names_vOut115 _derivingsIself) = inv_Names_s116 _derivingsX116 (T_Names_vIn115 )
         _constructorOsimpletype = rule457 _simpletypeIself
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule458  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule459  ()
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule460  ()
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule461  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule462 _constructorIunboundNames
         _self = rule463 _constructorIself _contextIself _derivingsIself _rangeIself _simpletypeIself
         _lhsOself :: Declaration
         _lhsOself = rule464 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule465 _lhsIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule466 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule467 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule468 _constructorIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule469 _constructorIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule470 _constructorIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule471 _constructorImiscerrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule472 _lhsIoperatorFixities
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule473 _lhsIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule474 _lhsItypeSignatures
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule475 _constructorIwarnings
         _contextOallTypeConstructors = rule476 _lhsIallTypeConstructors
         _contextOmiscerrors = rule477 _lhsImiscerrors
         _contextOoptions = rule478 _lhsIoptions
         _contextOtypeConstructors = rule479 _lhsItypeConstructors
         _contextOwarnings = rule480 _lhsIwarnings
         _constructorOallTypeConstructors = rule481 _lhsIallTypeConstructors
         _constructorOallValueConstructors = rule482 _lhsIallValueConstructors
         _constructorOcollectValueConstructors = rule483 _lhsIcollectValueConstructors
         _constructorOcounter = rule484 _lhsIcounter
         _constructorOkindErrors = rule485 _lhsIkindErrors
         _constructorOmiscerrors = rule486 _contextImiscerrors
         _constructorOnamesInScope = rule487 _lhsInamesInScope
         _constructorOoptions = rule488 _lhsIoptions
         _constructorOtypeConstructors = rule489 _lhsItypeConstructors
         _constructorOvalueConstructors = rule490 _lhsIvalueConstructors
         _constructorOwarnings = rule491 _contextIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule457 #-}
   rule457 = \ ((_simpletypeIself) :: SimpleType) ->
                                           _simpletypeIself
   {-# INLINE rule458 #-}
   rule458 = \  (_ :: ()) ->
                                                   Nothing
   {-# INLINE rule459 #-}
   rule459 = \  (_ :: ()) ->
     []
   {-# INLINE rule460 #-}
   rule460 = \  (_ :: ()) ->
     []
   {-# INLINE rule461 #-}
   rule461 = \  (_ :: ()) ->
     []
   {-# INLINE rule462 #-}
   rule462 = \ ((_constructorIunboundNames) :: Names) ->
     _constructorIunboundNames
   {-# INLINE rule463 #-}
   rule463 = \ ((_constructorIself) :: Constructor) ((_contextIself) :: ContextItems) ((_derivingsIself) :: Names) ((_rangeIself) :: Range) ((_simpletypeIself) :: SimpleType) ->
     Declaration_Newtype _rangeIself _contextIself _simpletypeIself _constructorIself _derivingsIself
   {-# INLINE rule464 #-}
   rule464 = \ _self ->
     _self
   {-# INLINE rule465 #-}
   rule465 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule466 #-}
   rule466 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule467 #-}
   rule467 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule468 #-}
   rule468 = \ ((_constructorIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _constructorIcollectValueConstructors
   {-# INLINE rule469 #-}
   rule469 = \ ((_constructorIcounter) :: Int) ->
     _constructorIcounter
   {-# INLINE rule470 #-}
   rule470 = \ ((_constructorIkindErrors) :: [Error]) ->
     _constructorIkindErrors
   {-# INLINE rule471 #-}
   rule471 = \ ((_constructorImiscerrors) :: [Error]) ->
     _constructorImiscerrors
   {-# INLINE rule472 #-}
   rule472 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule473 #-}
   rule473 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule474 #-}
   rule474 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule475 #-}
   rule475 = \ ((_constructorIwarnings) :: [Warning]) ->
     _constructorIwarnings
   {-# INLINE rule476 #-}
   rule476 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule477 #-}
   rule477 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule478 #-}
   rule478 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule479 #-}
   rule479 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule480 #-}
   rule480 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule481 #-}
   rule481 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule482 #-}
   rule482 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule483 #-}
   rule483 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule484 #-}
   rule484 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule485 #-}
   rule485 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule486 #-}
   rule486 = \ ((_contextImiscerrors) :: [Error]) ->
     _contextImiscerrors
   {-# INLINE rule487 #-}
   rule487 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule488 #-}
   rule488 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule489 #-}
   rule489 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule490 #-}
   rule490 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule491 #-}
   rule491 = \ ((_contextIwarnings) :: [Warning]) ->
     _contextIwarnings
{-# NOINLINE sem_Declaration_Class #-}
sem_Declaration_Class :: T_Range  -> T_ContextItems  -> T_SimpleType  -> T_MaybeDeclarations  -> T_Declaration 
sem_Declaration_Class arg_range_ arg_context_ arg_simpletype_ arg_where_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextIcontextRanges _contextIcontextVars _contextImiscerrors _contextIself _contextIwarnings) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 _contextOallTypeConstructors _contextOmiscerrors _contextOoptions _contextOtypeConstructors _contextOwarnings)
         (T_SimpleType_vOut151 _simpletypeIname _simpletypeIself _simpletypeItypevariables) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_MaybeDeclarations_vOut88 _whereIcollectInstances _whereIcollectScopeInfos _whereIcounter _whereIkindErrors _whereImiscerrors _whereInamesInScope _whereIself _whereIunboundNames _whereIwarnings) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 _whereOallTypeConstructors _whereOallValueConstructors _whereOclassEnvironment _whereOcollectScopeInfos _whereOcounter _whereOkindErrors _whereOmiscerrors _whereOnamesInScope _whereOoptions _whereOorderedTypeSynonyms _whereOtypeConstructors _whereOunboundNames _whereOvalueConstructors _whereOwarnings)
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule492  ()
         (_assumptions,_constraints,_unboundNames) = rule493  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule494 _whereIcollectInstances
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule495  ()
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule496  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule497 _unboundNames
         _self = rule498 _contextIself _rangeIself _simpletypeIself _whereIself
         _lhsOself :: Declaration
         _lhsOself = rule499 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule500 _whereIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule501 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule502 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule503 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule504 _whereIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule505 _whereIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule506 _whereImiscerrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule507 _lhsIoperatorFixities
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule508 _lhsIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule509 _lhsItypeSignatures
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule510 _whereIwarnings
         _contextOallTypeConstructors = rule511 _lhsIallTypeConstructors
         _contextOmiscerrors = rule512 _lhsImiscerrors
         _contextOoptions = rule513 _lhsIoptions
         _contextOtypeConstructors = rule514 _lhsItypeConstructors
         _contextOwarnings = rule515 _lhsIwarnings
         _whereOallTypeConstructors = rule516 _lhsIallTypeConstructors
         _whereOallValueConstructors = rule517 _lhsIallValueConstructors
         _whereOclassEnvironment = rule518 _lhsIclassEnvironment
         _whereOcollectScopeInfos = rule519 _lhsIcollectScopeInfos
         _whereOcounter = rule520 _lhsIcounter
         _whereOkindErrors = rule521 _lhsIkindErrors
         _whereOmiscerrors = rule522 _contextImiscerrors
         _whereOnamesInScope = rule523 _lhsInamesInScope
         _whereOoptions = rule524 _lhsIoptions
         _whereOorderedTypeSynonyms = rule525 _lhsIorderedTypeSynonyms
         _whereOtypeConstructors = rule526 _lhsItypeConstructors
         _whereOunboundNames = rule527 _unboundNames
         _whereOvalueConstructors = rule528 _lhsIvalueConstructors
         _whereOwarnings = rule529 _contextIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule492 #-}
   rule492 = \  (_ :: ()) ->
                                                   Nothing
   {-# INLINE rule493 #-}
   rule493 = \  (_ :: ()) ->
                                                               internalError "PartialSyntax.ag" "n/a" "Declaration.Class"
   {-# INLINE rule494 #-}
   rule494 = \ ((_whereIcollectInstances) :: [(Name, Instance)]) ->
     _whereIcollectInstances
   {-# INLINE rule495 #-}
   rule495 = \  (_ :: ()) ->
     []
   {-# INLINE rule496 #-}
   rule496 = \  (_ :: ()) ->
     []
   {-# INLINE rule497 #-}
   rule497 = \ _unboundNames ->
     _unboundNames
   {-# INLINE rule498 #-}
   rule498 = \ ((_contextIself) :: ContextItems) ((_rangeIself) :: Range) ((_simpletypeIself) :: SimpleType) ((_whereIself) :: MaybeDeclarations) ->
     Declaration_Class _rangeIself _contextIself _simpletypeIself _whereIself
   {-# INLINE rule499 #-}
   rule499 = \ _self ->
     _self
   {-# INLINE rule500 #-}
   rule500 = \ ((_whereIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _whereIcollectScopeInfos
   {-# INLINE rule501 #-}
   rule501 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule502 #-}
   rule502 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule503 #-}
   rule503 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule504 #-}
   rule504 = \ ((_whereIcounter) :: Int) ->
     _whereIcounter
   {-# INLINE rule505 #-}
   rule505 = \ ((_whereIkindErrors) :: [Error]) ->
     _whereIkindErrors
   {-# INLINE rule506 #-}
   rule506 = \ ((_whereImiscerrors) :: [Error]) ->
     _whereImiscerrors
   {-# INLINE rule507 #-}
   rule507 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule508 #-}
   rule508 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule509 #-}
   rule509 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule510 #-}
   rule510 = \ ((_whereIwarnings) :: [Warning]) ->
     _whereIwarnings
   {-# INLINE rule511 #-}
   rule511 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule512 #-}
   rule512 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule513 #-}
   rule513 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule514 #-}
   rule514 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule515 #-}
   rule515 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule516 #-}
   rule516 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule517 #-}
   rule517 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule518 #-}
   rule518 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule519 #-}
   rule519 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule520 #-}
   rule520 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule521 #-}
   rule521 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule522 #-}
   rule522 = \ ((_contextImiscerrors) :: [Error]) ->
     _contextImiscerrors
   {-# INLINE rule523 #-}
   rule523 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule524 #-}
   rule524 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule525 #-}
   rule525 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule526 #-}
   rule526 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule527 #-}
   rule527 = \ _unboundNames ->
     _unboundNames
   {-# INLINE rule528 #-}
   rule528 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule529 #-}
   rule529 = \ ((_contextIwarnings) :: [Warning]) ->
     _contextIwarnings
{-# NOINLINE sem_Declaration_Instance #-}
sem_Declaration_Instance :: T_Range  -> T_ContextItems  -> T_Name  -> T_Types  -> T_MaybeDeclarations  -> T_Declaration 
sem_Declaration_Instance arg_range_ arg_context_ arg_name_ arg_types_ arg_where_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _typesX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_types_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextIcontextRanges _contextIcontextVars _contextImiscerrors _contextIself _contextIwarnings) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 _contextOallTypeConstructors _contextOmiscerrors _contextOoptions _contextOtypeConstructors _contextOwarnings)
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Types_vOut166 _typesImiscerrors _typesIself _typesItypevariables _typesIwarnings) = inv_Types_s167 _typesX167 (T_Types_vIn166 _typesOallTypeConstructors _typesOmiscerrors _typesOoptions _typesOtypeConstructors _typesOwarnings)
         (T_MaybeDeclarations_vOut88 _whereIcollectInstances _whereIcollectScopeInfos _whereIcounter _whereIkindErrors _whereImiscerrors _whereInamesInScope _whereIself _whereIunboundNames _whereIwarnings) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 _whereOallTypeConstructors _whereOallValueConstructors _whereOclassEnvironment _whereOcollectScopeInfos _whereOcounter _whereOkindErrors _whereOmiscerrors _whereOnamesInScope _whereOoptions _whereOorderedTypeSynonyms _whereOtypeConstructors _whereOunboundNames _whereOvalueConstructors _whereOwarnings)
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule530  ()
         (_assumptions,_constraints,_unboundNames) = rule531  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule532 _whereIcollectInstances
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule533  ()
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule534  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule535 _unboundNames
         _self = rule536 _contextIself _nameIself _rangeIself _typesIself _whereIself
         _lhsOself :: Declaration
         _lhsOself = rule537 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule538 _whereIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule539 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule540 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule541 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule542 _whereIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule543 _whereIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule544 _whereImiscerrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule545 _lhsIoperatorFixities
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule546 _lhsIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule547 _lhsItypeSignatures
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule548 _whereIwarnings
         _contextOallTypeConstructors = rule549 _lhsIallTypeConstructors
         _contextOmiscerrors = rule550 _lhsImiscerrors
         _contextOoptions = rule551 _lhsIoptions
         _contextOtypeConstructors = rule552 _lhsItypeConstructors
         _contextOwarnings = rule553 _lhsIwarnings
         _typesOallTypeConstructors = rule554 _lhsIallTypeConstructors
         _typesOmiscerrors = rule555 _contextImiscerrors
         _typesOoptions = rule556 _lhsIoptions
         _typesOtypeConstructors = rule557 _lhsItypeConstructors
         _typesOwarnings = rule558 _contextIwarnings
         _whereOallTypeConstructors = rule559 _lhsIallTypeConstructors
         _whereOallValueConstructors = rule560 _lhsIallValueConstructors
         _whereOclassEnvironment = rule561 _lhsIclassEnvironment
         _whereOcollectScopeInfos = rule562 _lhsIcollectScopeInfos
         _whereOcounter = rule563 _lhsIcounter
         _whereOkindErrors = rule564 _lhsIkindErrors
         _whereOmiscerrors = rule565 _typesImiscerrors
         _whereOnamesInScope = rule566 _lhsInamesInScope
         _whereOoptions = rule567 _lhsIoptions
         _whereOorderedTypeSynonyms = rule568 _lhsIorderedTypeSynonyms
         _whereOtypeConstructors = rule569 _lhsItypeConstructors
         _whereOunboundNames = rule570 _unboundNames
         _whereOvalueConstructors = rule571 _lhsIvalueConstructors
         _whereOwarnings = rule572 _typesIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule530 #-}
   rule530 = \  (_ :: ()) ->
                                                   Nothing
   {-# INLINE rule531 #-}
   rule531 = \  (_ :: ()) ->
                                                               internalError "PartialSyntax.ag" "n/a" "Declaration.Instance"
   {-# INLINE rule532 #-}
   rule532 = \ ((_whereIcollectInstances) :: [(Name, Instance)]) ->
     _whereIcollectInstances
   {-# INLINE rule533 #-}
   rule533 = \  (_ :: ()) ->
     []
   {-# INLINE rule534 #-}
   rule534 = \  (_ :: ()) ->
     []
   {-# INLINE rule535 #-}
   rule535 = \ _unboundNames ->
     _unboundNames
   {-# INLINE rule536 #-}
   rule536 = \ ((_contextIself) :: ContextItems) ((_nameIself) :: Name) ((_rangeIself) :: Range) ((_typesIself) :: Types) ((_whereIself) :: MaybeDeclarations) ->
     Declaration_Instance _rangeIself _contextIself _nameIself _typesIself _whereIself
   {-# INLINE rule537 #-}
   rule537 = \ _self ->
     _self
   {-# INLINE rule538 #-}
   rule538 = \ ((_whereIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _whereIcollectScopeInfos
   {-# INLINE rule539 #-}
   rule539 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule540 #-}
   rule540 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule541 #-}
   rule541 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule542 #-}
   rule542 = \ ((_whereIcounter) :: Int) ->
     _whereIcounter
   {-# INLINE rule543 #-}
   rule543 = \ ((_whereIkindErrors) :: [Error]) ->
     _whereIkindErrors
   {-# INLINE rule544 #-}
   rule544 = \ ((_whereImiscerrors) :: [Error]) ->
     _whereImiscerrors
   {-# INLINE rule545 #-}
   rule545 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule546 #-}
   rule546 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule547 #-}
   rule547 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule548 #-}
   rule548 = \ ((_whereIwarnings) :: [Warning]) ->
     _whereIwarnings
   {-# INLINE rule549 #-}
   rule549 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule550 #-}
   rule550 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule551 #-}
   rule551 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule552 #-}
   rule552 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule553 #-}
   rule553 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule554 #-}
   rule554 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule555 #-}
   rule555 = \ ((_contextImiscerrors) :: [Error]) ->
     _contextImiscerrors
   {-# INLINE rule556 #-}
   rule556 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule557 #-}
   rule557 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule558 #-}
   rule558 = \ ((_contextIwarnings) :: [Warning]) ->
     _contextIwarnings
   {-# INLINE rule559 #-}
   rule559 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule560 #-}
   rule560 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule561 #-}
   rule561 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule562 #-}
   rule562 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule563 #-}
   rule563 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule564 #-}
   rule564 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule565 #-}
   rule565 = \ ((_typesImiscerrors) :: [Error]) ->
     _typesImiscerrors
   {-# INLINE rule566 #-}
   rule566 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule567 #-}
   rule567 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule568 #-}
   rule568 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule569 #-}
   rule569 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule570 #-}
   rule570 = \ _unboundNames ->
     _unboundNames
   {-# INLINE rule571 #-}
   rule571 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule572 #-}
   rule572 = \ ((_typesIwarnings) :: [Warning]) ->
     _typesIwarnings
{-# NOINLINE sem_Declaration_Default #-}
sem_Declaration_Default :: T_Range  -> T_Types  -> T_Declaration 
sem_Declaration_Default arg_range_ arg_types_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typesX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_types_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Types_vOut166 _typesImiscerrors _typesIself _typesItypevariables _typesIwarnings) = inv_Types_s167 _typesX167 (T_Types_vIn166 _typesOallTypeConstructors _typesOmiscerrors _typesOoptions _typesOtypeConstructors _typesOwarnings)
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule573  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule574  ()
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule575  ()
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule576  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule577  ()
         _self = rule578 _rangeIself _typesIself
         _lhsOself :: Declaration
         _lhsOself = rule579 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule580 _lhsIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule581 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule582 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule583 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule584 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule585 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule586 _typesImiscerrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule587 _lhsIoperatorFixities
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule588 _lhsIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule589 _lhsItypeSignatures
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule590 _typesIwarnings
         _typesOallTypeConstructors = rule591 _lhsIallTypeConstructors
         _typesOmiscerrors = rule592 _lhsImiscerrors
         _typesOoptions = rule593 _lhsIoptions
         _typesOtypeConstructors = rule594 _lhsItypeConstructors
         _typesOwarnings = rule595 _lhsIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule573 #-}
   rule573 = \  (_ :: ()) ->
                                                   Nothing
   {-# INLINE rule574 #-}
   rule574 = \  (_ :: ()) ->
     []
   {-# INLINE rule575 #-}
   rule575 = \  (_ :: ()) ->
     []
   {-# INLINE rule576 #-}
   rule576 = \  (_ :: ()) ->
     []
   {-# INLINE rule577 #-}
   rule577 = \  (_ :: ()) ->
     []
   {-# INLINE rule578 #-}
   rule578 = \ ((_rangeIself) :: Range) ((_typesIself) :: Types) ->
     Declaration_Default _rangeIself _typesIself
   {-# INLINE rule579 #-}
   rule579 = \ _self ->
     _self
   {-# INLINE rule580 #-}
   rule580 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule581 #-}
   rule581 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule582 #-}
   rule582 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule583 #-}
   rule583 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule584 #-}
   rule584 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule585 #-}
   rule585 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule586 #-}
   rule586 = \ ((_typesImiscerrors) :: [Error]) ->
     _typesImiscerrors
   {-# INLINE rule587 #-}
   rule587 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule588 #-}
   rule588 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule589 #-}
   rule589 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule590 #-}
   rule590 = \ ((_typesIwarnings) :: [Warning]) ->
     _typesIwarnings
   {-# INLINE rule591 #-}
   rule591 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule592 #-}
   rule592 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule593 #-}
   rule593 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule594 #-}
   rule594 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule595 #-}
   rule595 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Declaration_FunctionBindings #-}
sem_Declaration_FunctionBindings :: T_Range  -> T_FunctionBindings  -> T_Declaration 
sem_Declaration_FunctionBindings arg_range_ arg_bindings_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _bindingsX59 = Control.Monad.Identity.runIdentity (attach_T_FunctionBindings (arg_bindings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_FunctionBindings_vOut58 _bindingsIarities _bindingsIcollectInstances _bindingsIcollectScopeInfos _bindingsIcounter _bindingsIkindErrors _bindingsImiscerrors _bindingsIname _bindingsIself _bindingsIunboundNames _bindingsIwarnings) = inv_FunctionBindings_s59 _bindingsX59 (T_FunctionBindings_vIn58 _bindingsOallTypeConstructors _bindingsOallValueConstructors _bindingsOclassEnvironment _bindingsOcollectScopeInfos _bindingsOcounter _bindingsOkindErrors _bindingsOmiscerrors _bindingsOnamesInScope _bindingsOoptions _bindingsOorderedTypeSynonyms _bindingsOtypeConstructors _bindingsOvalueConstructors _bindingsOwarnings)
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule596 _bindingsIname
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule597 _bindingsIname
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule598 _bindingsIname _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule599 _arityErrors _bindingsImiscerrors
         _arityErrors = rule600 _bindingsIarities _bindingsIname _rangeIself
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule601 _bindingsIcollectInstances
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule602  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule603 _bindingsIunboundNames
         _self = rule604 _bindingsIself _rangeIself
         _lhsOself :: Declaration
         _lhsOself = rule605 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule606 _bindingsIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule607 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule608 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule609 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule610 _bindingsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule611 _bindingsIkindErrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule612 _lhsIoperatorFixities
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule613 _lhsItypeSignatures
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule614 _bindingsIwarnings
         _bindingsOallTypeConstructors = rule615 _lhsIallTypeConstructors
         _bindingsOallValueConstructors = rule616 _lhsIallValueConstructors
         _bindingsOclassEnvironment = rule617 _lhsIclassEnvironment
         _bindingsOcollectScopeInfos = rule618 _lhsIcollectScopeInfos
         _bindingsOcounter = rule619 _lhsIcounter
         _bindingsOkindErrors = rule620 _lhsIkindErrors
         _bindingsOmiscerrors = rule621 _lhsImiscerrors
         _bindingsOnamesInScope = rule622 _lhsInamesInScope
         _bindingsOoptions = rule623 _lhsIoptions
         _bindingsOorderedTypeSynonyms = rule624 _lhsIorderedTypeSynonyms
         _bindingsOtypeConstructors = rule625 _lhsItypeConstructors
         _bindingsOvalueConstructors = rule626 _lhsIvalueConstructors
         _bindingsOwarnings = rule627 _lhsIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule596 #-}
   rule596 = \ ((_bindingsIname) :: Name) ->
                                             [_bindingsIname]
   {-# INLINE rule597 #-}
   rule597 = \ ((_bindingsIname) :: Name) ->
                                                   Just _bindingsIname
   {-# INLINE rule598 #-}
   rule598 = \ ((_bindingsIname) :: Name) ((_lhsIpreviousWasAlsoFB) :: Maybe Name) ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
                                                   case _lhsIpreviousWasAlsoFB of
                                                      Just name | show name `similar` show _bindingsIname
                                                         -> (name,_bindingsIname) : _lhsIsuspiciousFBs
                                                      _  -> _lhsIsuspiciousFBs
   {-# INLINE rule599 #-}
   rule599 = \ _arityErrors ((_bindingsImiscerrors) :: [Error]) ->
                                               _arityErrors ++ _bindingsImiscerrors
   {-# INLINE rule600 #-}
   rule600 = \ ((_bindingsIarities) ::  [Int] ) ((_bindingsIname) :: Name) ((_rangeIself) :: Range) ->
                                               if all (== head _bindingsIarities) _bindingsIarities
                                                 then []
                                                 else [ DefArityMismatch _bindingsIname (mode _bindingsIarities) _rangeIself ]
   {-# INLINE rule601 #-}
   rule601 = \ ((_bindingsIcollectInstances) :: [(Name, Instance)]) ->
     _bindingsIcollectInstances
   {-# INLINE rule602 #-}
   rule602 = \  (_ :: ()) ->
     []
   {-# INLINE rule603 #-}
   rule603 = \ ((_bindingsIunboundNames) :: Names) ->
     _bindingsIunboundNames
   {-# INLINE rule604 #-}
   rule604 = \ ((_bindingsIself) :: FunctionBindings) ((_rangeIself) :: Range) ->
     Declaration_FunctionBindings _rangeIself _bindingsIself
   {-# INLINE rule605 #-}
   rule605 = \ _self ->
     _self
   {-# INLINE rule606 #-}
   rule606 = \ ((_bindingsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _bindingsIcollectScopeInfos
   {-# INLINE rule607 #-}
   rule607 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule608 #-}
   rule608 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule609 #-}
   rule609 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule610 #-}
   rule610 = \ ((_bindingsIcounter) :: Int) ->
     _bindingsIcounter
   {-# INLINE rule611 #-}
   rule611 = \ ((_bindingsIkindErrors) :: [Error]) ->
     _bindingsIkindErrors
   {-# INLINE rule612 #-}
   rule612 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule613 #-}
   rule613 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule614 #-}
   rule614 = \ ((_bindingsIwarnings) :: [Warning]) ->
     _bindingsIwarnings
   {-# INLINE rule615 #-}
   rule615 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule616 #-}
   rule616 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule617 #-}
   rule617 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule618 #-}
   rule618 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule619 #-}
   rule619 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule620 #-}
   rule620 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule621 #-}
   rule621 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule622 #-}
   rule622 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule623 #-}
   rule623 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule624 #-}
   rule624 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule625 #-}
   rule625 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule626 #-}
   rule626 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule627 #-}
   rule627 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Declaration_PatternBinding #-}
sem_Declaration_PatternBinding :: T_Range  -> T_Pattern  -> T_RightHandSide  -> T_Declaration 
sem_Declaration_PatternBinding arg_range_ arg_pattern_ arg_righthandside_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _righthandsideX149 = Control.Monad.Identity.runIdentity (attach_T_RightHandSide (arg_righthandside_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIcollectScopeInfos _patternIcounter _patternImiscerrors _patternIpatVarNames _patternIself _patternIunboundNames _patternIwarnings) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOcounter _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings)
         (T_RightHandSide_vOut148 _righthandsideIcollectInstances _righthandsideIcollectScopeInfos _righthandsideIcounter _righthandsideIkindErrors _righthandsideImiscerrors _righthandsideIself _righthandsideIunboundNames _righthandsideIwarnings) = inv_RightHandSide_s149 _righthandsideX149 (T_RightHandSide_vIn148 _righthandsideOallTypeConstructors _righthandsideOallValueConstructors _righthandsideOclassEnvironment _righthandsideOcollectScopeInfos _righthandsideOcounter _righthandsideOkindErrors _righthandsideOmiscerrors _righthandsideOnamesInScope _righthandsideOoptions _righthandsideOorderedTypeSynonyms _righthandsideOtypeConstructors _righthandsideOvalueConstructors _righthandsideOwarnings)
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule628 _patternIpatVarNames
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule629  ()
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule630 _patternDefinesNoVarsErrors _righthandsideImiscerrors
         _patternDefinesNoVarsErrors = rule631 _patternIpatVarNames _patternIself
         _patternOlhsPattern = rule632 _patternIself
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule633 _patternIpatVarNames _patternIself
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule634 _righthandsideIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule635 _patternIunboundNames _righthandsideIunboundNames
         _self = rule636 _patternIself _rangeIself _righthandsideIself
         _lhsOself :: Declaration
         _lhsOself = rule637 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule638 _righthandsideIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule639 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule640 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule641 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule642 _righthandsideIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule643 _righthandsideIkindErrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule644 _lhsIoperatorFixities
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule645 _lhsIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule646 _lhsItypeSignatures
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule647 _righthandsideIwarnings
         _patternOallTypeConstructors = rule648 _lhsIallTypeConstructors
         _patternOallValueConstructors = rule649 _lhsIallValueConstructors
         _patternOcollectScopeInfos = rule650 _lhsIcollectScopeInfos
         _patternOcounter = rule651 _lhsIcounter
         _patternOmiscerrors = rule652 _lhsImiscerrors
         _patternOnamesInScope = rule653 _lhsInamesInScope
         _patternOtypeConstructors = rule654 _lhsItypeConstructors
         _patternOvalueConstructors = rule655 _lhsIvalueConstructors
         _patternOwarnings = rule656 _lhsIwarnings
         _righthandsideOallTypeConstructors = rule657 _lhsIallTypeConstructors
         _righthandsideOallValueConstructors = rule658 _lhsIallValueConstructors
         _righthandsideOclassEnvironment = rule659 _lhsIclassEnvironment
         _righthandsideOcollectScopeInfos = rule660 _patternIcollectScopeInfos
         _righthandsideOcounter = rule661 _patternIcounter
         _righthandsideOkindErrors = rule662 _lhsIkindErrors
         _righthandsideOmiscerrors = rule663 _patternImiscerrors
         _righthandsideOnamesInScope = rule664 _lhsInamesInScope
         _righthandsideOoptions = rule665 _lhsIoptions
         _righthandsideOorderedTypeSynonyms = rule666 _lhsIorderedTypeSynonyms
         _righthandsideOtypeConstructors = rule667 _lhsItypeConstructors
         _righthandsideOvalueConstructors = rule668 _lhsIvalueConstructors
         _righthandsideOwarnings = rule669 _patternIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule628 #-}
   rule628 = \ ((_patternIpatVarNames) :: Names) ->
                                             _patternIpatVarNames
   {-# INLINE rule629 #-}
   rule629 = \  (_ :: ()) ->
                                                   Nothing
   {-# INLINE rule630 #-}
   rule630 = \ _patternDefinesNoVarsErrors ((_righthandsideImiscerrors) :: [Error]) ->
                                             _patternDefinesNoVarsErrors ++ _righthandsideImiscerrors
   {-# INLINE rule631 #-}
   rule631 = \ ((_patternIpatVarNames) :: Names) ((_patternIself) :: Pattern) ->
                                                            if null _patternIpatVarNames
                                                              then [ PatternDefinesNoVars (getPatRange _patternIself) ]
                                                              else []
   {-# INLINE rule632 #-}
   rule632 = \ ((_patternIself) :: Pattern) ->
                                                                simplePattern _patternIself
   {-# INLINE rule633 #-}
   rule633 = \ ((_patternIpatVarNames) :: Names) ((_patternIself) :: Pattern) ->
                                 if isSimplePattern _patternIself
                                   then []
                                   else _patternIpatVarNames
   {-# INLINE rule634 #-}
   rule634 = \ ((_righthandsideIcollectInstances) :: [(Name, Instance)]) ->
     _righthandsideIcollectInstances
   {-# INLINE rule635 #-}
   rule635 = \ ((_patternIunboundNames) :: Names) ((_righthandsideIunboundNames) :: Names) ->
     _patternIunboundNames ++ _righthandsideIunboundNames
   {-# INLINE rule636 #-}
   rule636 = \ ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ((_righthandsideIself) :: RightHandSide) ->
     Declaration_PatternBinding _rangeIself _patternIself _righthandsideIself
   {-# INLINE rule637 #-}
   rule637 = \ _self ->
     _self
   {-# INLINE rule638 #-}
   rule638 = \ ((_righthandsideIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _righthandsideIcollectScopeInfos
   {-# INLINE rule639 #-}
   rule639 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule640 #-}
   rule640 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule641 #-}
   rule641 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule642 #-}
   rule642 = \ ((_righthandsideIcounter) :: Int) ->
     _righthandsideIcounter
   {-# INLINE rule643 #-}
   rule643 = \ ((_righthandsideIkindErrors) :: [Error]) ->
     _righthandsideIkindErrors
   {-# INLINE rule644 #-}
   rule644 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule645 #-}
   rule645 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule646 #-}
   rule646 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule647 #-}
   rule647 = \ ((_righthandsideIwarnings) :: [Warning]) ->
     _righthandsideIwarnings
   {-# INLINE rule648 #-}
   rule648 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule649 #-}
   rule649 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule650 #-}
   rule650 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule651 #-}
   rule651 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule652 #-}
   rule652 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule653 #-}
   rule653 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule654 #-}
   rule654 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule655 #-}
   rule655 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule656 #-}
   rule656 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule657 #-}
   rule657 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule658 #-}
   rule658 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule659 #-}
   rule659 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule660 #-}
   rule660 = \ ((_patternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternIcollectScopeInfos
   {-# INLINE rule661 #-}
   rule661 = \ ((_patternIcounter) :: Int) ->
     _patternIcounter
   {-# INLINE rule662 #-}
   rule662 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule663 #-}
   rule663 = \ ((_patternImiscerrors) :: [Error]) ->
     _patternImiscerrors
   {-# INLINE rule664 #-}
   rule664 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule665 #-}
   rule665 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule666 #-}
   rule666 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule667 #-}
   rule667 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule668 #-}
   rule668 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule669 #-}
   rule669 = \ ((_patternIwarnings) :: [Warning]) ->
     _patternIwarnings
{-# NOINLINE sem_Declaration_TypeSignature #-}
sem_Declaration_TypeSignature :: T_Range  -> T_Names  -> T_Type  -> T_Declaration 
sem_Declaration_TypeSignature arg_range_ arg_names_ arg_type_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _namesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_names_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _namesIself) = inv_Names_s116 _namesX116 (T_Names_vIn115 )
         (T_Type_vOut163 _typeIcontextRange _typeImiscerrors _typeIself _typeItypevariables _typeIwarnings) = inv_Type_s164 _typeX164 (T_Type_vIn163 _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings)
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule670 _lhsItypeSignatures _namesIself _typeScheme
         (_typeScheme,_intMap) = rule671 _typeIself
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule672 _lhsIkindErrors _newErrors
         _newErrors = rule673 _lhsIallValueConstructors _lhsInamesInScope _lhsItypeConstructors _typeIself
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule674  ()
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule675 _intMap _lhsIorderedTypeSynonyms _typeIcontextRange _typeIwarnings _typeScheme
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule676  ()
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule677  ()
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule678  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule679  ()
         _self = rule680 _namesIself _rangeIself _typeIself
         _lhsOself :: Declaration
         _lhsOself = rule681 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule682 _lhsIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule683 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule684 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule685 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule686 _lhsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule687 _typeImiscerrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule688 _lhsIoperatorFixities
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule689 _lhsIsuspiciousFBs
         _typeOallTypeConstructors = rule690 _lhsIallTypeConstructors
         _typeOmiscerrors = rule691 _lhsImiscerrors
         _typeOoptions = rule692 _lhsIoptions
         _typeOtypeConstructors = rule693 _lhsItypeConstructors
         _typeOwarnings = rule694 _lhsIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule670 #-}
   rule670 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ((_namesIself) :: Names) _typeScheme ->
                               [ (name, _typeScheme) | name <- _namesIself ] ++ _lhsItypeSignatures
   {-# INLINE rule671 #-}
   rule671 = \ ((_typeIself) :: Type) ->
                                     makeTpSchemeFromType' _typeIself
   {-# INLINE rule672 #-}
   rule672 = \ ((_lhsIkindErrors) :: [Error]) _newErrors ->
                                         _newErrors ++ _lhsIkindErrors
   {-# INLINE rule673 #-}
   rule673 = \ ((_lhsIallValueConstructors) :: Names) ((_lhsInamesInScope) :: Names) ((_lhsItypeConstructors) :: M.Map Name Int) ((_typeIself) :: Type) ->
                                         checkType _lhsItypeConstructors (_lhsInamesInScope ++ _lhsIallValueConstructors) _typeIself
   {-# INLINE rule674 #-}
   rule674 = \  (_ :: ()) ->
                                                   Nothing
   {-# INLINE rule675 #-}
   rule675 = \ _intMap ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ((_typeIcontextRange) :: Range) ((_typeIwarnings) :: [Warning]) _typeScheme ->
                          simplifyContext _lhsIorderedTypeSynonyms _typeIcontextRange _intMap _typeScheme ++ _typeIwarnings
   {-# INLINE rule676 #-}
   rule676 = \  (_ :: ()) ->
     []
   {-# INLINE rule677 #-}
   rule677 = \  (_ :: ()) ->
     []
   {-# INLINE rule678 #-}
   rule678 = \  (_ :: ()) ->
     []
   {-# INLINE rule679 #-}
   rule679 = \  (_ :: ()) ->
     []
   {-# INLINE rule680 #-}
   rule680 = \ ((_namesIself) :: Names) ((_rangeIself) :: Range) ((_typeIself) :: Type) ->
     Declaration_TypeSignature _rangeIself _namesIself _typeIself
   {-# INLINE rule681 #-}
   rule681 = \ _self ->
     _self
   {-# INLINE rule682 #-}
   rule682 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule683 #-}
   rule683 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule684 #-}
   rule684 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule685 #-}
   rule685 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule686 #-}
   rule686 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule687 #-}
   rule687 = \ ((_typeImiscerrors) :: [Error]) ->
     _typeImiscerrors
   {-# INLINE rule688 #-}
   rule688 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule689 #-}
   rule689 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule690 #-}
   rule690 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule691 #-}
   rule691 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule692 #-}
   rule692 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule693 #-}
   rule693 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule694 #-}
   rule694 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Declaration_Fixity #-}
sem_Declaration_Fixity :: T_Range  -> T_Fixity  -> T_MaybeInt  -> T_Names  -> T_Declaration 
sem_Declaration_Fixity arg_range_ arg_fixity_ arg_priority_ arg_operators_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _fixityX53 = Control.Monad.Identity.runIdentity (attach_T_Fixity (arg_fixity_))
         _priorityX101 = Control.Monad.Identity.runIdentity (attach_T_MaybeInt (arg_priority_))
         _operatorsX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_operators_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Fixity_vOut52 _fixityIself) = inv_Fixity_s53 _fixityX53 (T_Fixity_vIn52 )
         (T_MaybeInt_vOut100 _priorityIself) = inv_MaybeInt_s101 _priorityX101 (T_MaybeInt_vIn100 )
         (T_Names_vOut115 _operatorsIself) = inv_Names_s116 _operatorsX116 (T_Names_vIn115 )
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule695 _fixityIself _lhsIoperatorFixities _operatorsIself _priorityIself
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule696  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule697  ()
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule698  ()
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule699  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule700  ()
         _self = rule701 _fixityIself _operatorsIself _priorityIself _rangeIself
         _lhsOself :: Declaration
         _lhsOself = rule702 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule703 _lhsIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule704 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule705 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule706 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule707 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule708 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule709 _lhsImiscerrors
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule710 _lhsIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule711 _lhsItypeSignatures
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule712 _lhsIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule695 #-}
   rule695 = \ ((_fixityIself) :: Fixity) ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ((_operatorsIself) :: Names) ((_priorityIself) :: MaybeInt) ->
                                        let associativity = case _fixityIself of
                                                               Fixity_Infix _  -> AssocNone
                                                               Fixity_Infixl _ -> AssocLeft
                                                               Fixity_Infixr _ -> AssocRight
                                            priority      = case _priorityIself of
                                                               MaybeInt_Just i  -> i
                                                               MaybeInt_Nothing -> 9
                                        in [ (name, (priority, associativity)) | name <- _operatorsIself ] ++ _lhsIoperatorFixities
   {-# INLINE rule696 #-}
   rule696 = \  (_ :: ()) ->
                                                   Nothing
   {-# INLINE rule697 #-}
   rule697 = \  (_ :: ()) ->
     []
   {-# INLINE rule698 #-}
   rule698 = \  (_ :: ()) ->
     []
   {-# INLINE rule699 #-}
   rule699 = \  (_ :: ()) ->
     []
   {-# INLINE rule700 #-}
   rule700 = \  (_ :: ()) ->
     []
   {-# INLINE rule701 #-}
   rule701 = \ ((_fixityIself) :: Fixity) ((_operatorsIself) :: Names) ((_priorityIself) :: MaybeInt) ((_rangeIself) :: Range) ->
     Declaration_Fixity _rangeIself _fixityIself _priorityIself _operatorsIself
   {-# INLINE rule702 #-}
   rule702 = \ _self ->
     _self
   {-# INLINE rule703 #-}
   rule703 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule704 #-}
   rule704 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule705 #-}
   rule705 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule706 #-}
   rule706 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule707 #-}
   rule707 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule708 #-}
   rule708 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule709 #-}
   rule709 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule710 #-}
   rule710 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule711 #-}
   rule711 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule712 #-}
   rule712 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Declaration_Empty #-}
sem_Declaration_Empty :: T_Range  -> T_Declaration 
sem_Declaration_Empty arg_range_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule713  ()
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule714  ()
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule715  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule716  ()
         _self = rule717 _rangeIself
         _lhsOself :: Declaration
         _lhsOself = rule718 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule719 _lhsIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule720 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule721 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule722 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule723 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule724 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule725 _lhsImiscerrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule726 _lhsIoperatorFixities
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule727 _lhsIpreviousWasAlsoFB
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule728 _lhsIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule729 _lhsItypeSignatures
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule730 _lhsIwarnings
         __result_ = T_Declaration_vOut28 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule713 #-}
   rule713 = \  (_ :: ()) ->
     []
   {-# INLINE rule714 #-}
   rule714 = \  (_ :: ()) ->
     []
   {-# INLINE rule715 #-}
   rule715 = \  (_ :: ()) ->
     []
   {-# INLINE rule716 #-}
   rule716 = \  (_ :: ()) ->
     []
   {-# INLINE rule717 #-}
   rule717 = \ ((_rangeIself) :: Range) ->
     Declaration_Empty _rangeIself
   {-# INLINE rule718 #-}
   rule718 = \ _self ->
     _self
   {-# INLINE rule719 #-}
   rule719 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule720 #-}
   rule720 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule721 #-}
   rule721 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule722 #-}
   rule722 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule723 #-}
   rule723 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule724 #-}
   rule724 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule725 #-}
   rule725 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule726 #-}
   rule726 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule727 #-}
   rule727 = \ ((_lhsIpreviousWasAlsoFB) :: Maybe Name) ->
     _lhsIpreviousWasAlsoFB
   {-# INLINE rule728 #-}
   rule728 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule729 #-}
   rule729 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule730 #-}
   rule730 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Declarations ------------------------------------------------
-- wrapper
data Inh_Declarations  = Inh_Declarations { allTypeConstructors_Inh_Declarations :: (Names), allValueConstructors_Inh_Declarations :: (Names), classEnvironment_Inh_Declarations :: (ClassEnvironment), collectScopeInfos_Inh_Declarations :: ([(ScopeInfo, Entity)]), collectTypeConstructors_Inh_Declarations :: ([(Name,Int)]), collectTypeSynonyms_Inh_Declarations :: ([(Name,(Int,Tps -> Tp))]), collectValueConstructors_Inh_Declarations :: ([(Name,TpScheme)]), counter_Inh_Declarations :: (Int), kindErrors_Inh_Declarations :: ([Error]), miscerrors_Inh_Declarations :: ([Error]), namesInScope_Inh_Declarations :: (Names), operatorFixities_Inh_Declarations :: ([(Name,(Int,Assoc))]), options_Inh_Declarations :: ([Option]), orderedTypeSynonyms_Inh_Declarations :: (OrderedTypeSynonyms), previousWasAlsoFB_Inh_Declarations :: (Maybe Name), suspiciousFBs_Inh_Declarations :: ([(Name,Name)]), typeConstructors_Inh_Declarations :: (M.Map Name Int), typeSignatures_Inh_Declarations :: ([(Name,TpScheme)]), valueConstructors_Inh_Declarations :: (M.Map Name TpScheme), warnings_Inh_Declarations :: ([Warning]) }
data Syn_Declarations  = Syn_Declarations { collectInstances_Syn_Declarations :: ([(Name, Instance)]), collectScopeInfos_Syn_Declarations :: ([(ScopeInfo, Entity)]), collectTypeConstructors_Syn_Declarations :: ([(Name,Int)]), collectTypeSynonyms_Syn_Declarations :: ([(Name,(Int,Tps -> Tp))]), collectValueConstructors_Syn_Declarations :: ([(Name,TpScheme)]), counter_Syn_Declarations :: (Int), declVarNames_Syn_Declarations :: (Names), kindErrors_Syn_Declarations :: ([Error]), miscerrors_Syn_Declarations :: ([Error]), operatorFixities_Syn_Declarations :: ([(Name,(Int,Assoc))]), previousWasAlsoFB_Syn_Declarations :: (Maybe Name), restrictedNames_Syn_Declarations :: (Names), self_Syn_Declarations :: (Declarations), suspiciousFBs_Syn_Declarations :: ([(Name,Name)]), typeSignatures_Syn_Declarations :: ([(Name,TpScheme)]), unboundNames_Syn_Declarations :: (Names), warnings_Syn_Declarations :: ([Warning]) }
{-# INLINABLE wrap_Declarations #-}
wrap_Declarations :: T_Declarations  -> Inh_Declarations  -> (Syn_Declarations )
wrap_Declarations (T_Declarations act) (Inh_Declarations _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Declarations_vIn31 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings
        (T_Declarations_vOut31 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings) <- return (inv_Declarations_s32 sem arg)
        return (Syn_Declarations _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Declarations #-}
sem_Declarations :: Declarations  -> T_Declarations 
sem_Declarations list = Prelude.foldr sem_Declarations_Cons sem_Declarations_Nil (Prelude.map sem_Declaration list)

-- semantic domain
newtype T_Declarations  = T_Declarations {
                                         attach_T_Declarations :: Identity (T_Declarations_s32 )
                                         }
newtype T_Declarations_s32  = C_Declarations_s32 {
                                                 inv_Declarations_s32 :: (T_Declarations_v31 )
                                                 }
data T_Declarations_s33  = C_Declarations_s33
type T_Declarations_v31  = (T_Declarations_vIn31 ) -> (T_Declarations_vOut31 )
data T_Declarations_vIn31  = T_Declarations_vIn31 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) ([(Name,Int)]) ([(Name,(Int,Tps -> Tp))]) ([(Name,TpScheme)]) (Int) ([Error]) ([Error]) (Names) ([(Name,(Int,Assoc))]) ([Option]) (OrderedTypeSynonyms) (Maybe Name) ([(Name,Name)]) (M.Map Name Int) ([(Name,TpScheme)]) (M.Map Name TpScheme) ([Warning])
data T_Declarations_vOut31  = T_Declarations_vOut31 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) ([(Name,Int)]) ([(Name,(Int,Tps -> Tp))]) ([(Name,TpScheme)]) (Int) (Names) ([Error]) ([Error]) ([(Name,(Int,Assoc))]) (Maybe Name) (Names) (Declarations) ([(Name,Name)]) ([(Name,TpScheme)]) (Names) ([Warning])
{-# NOINLINE sem_Declarations_Cons #-}
sem_Declarations_Cons :: T_Declaration  -> T_Declarations  -> T_Declarations 
sem_Declarations_Cons arg_hd_ arg_tl_ = T_Declarations (return st32) where
   {-# NOINLINE st32 #-}
   st32 = let
      v31 :: T_Declarations_v31 
      v31 = \ (T_Declarations_vIn31 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _hdX29 = Control.Monad.Identity.runIdentity (attach_T_Declaration (arg_hd_))
         _tlX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_tl_))
         (T_Declaration_vOut28 _hdIcollectInstances _hdIcollectScopeInfos _hdIcollectTypeConstructors _hdIcollectTypeSynonyms _hdIcollectValueConstructors _hdIcounter _hdIdeclVarNames _hdIkindErrors _hdImiscerrors _hdIoperatorFixities _hdIpreviousWasAlsoFB _hdIrestrictedNames _hdIself _hdIsuspiciousFBs _hdItypeSignatures _hdIunboundNames _hdIwarnings) = inv_Declaration_s29 _hdX29 (T_Declaration_vIn28 _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOcollectTypeConstructors _hdOcollectTypeSynonyms _hdOcollectValueConstructors _hdOcounter _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoperatorFixities _hdOoptions _hdOorderedTypeSynonyms _hdOpreviousWasAlsoFB _hdOsuspiciousFBs _hdOtypeConstructors _hdOtypeSignatures _hdOvalueConstructors _hdOwarnings)
         (T_Declarations_vOut31 _tlIcollectInstances _tlIcollectScopeInfos _tlIcollectTypeConstructors _tlIcollectTypeSynonyms _tlIcollectValueConstructors _tlIcounter _tlIdeclVarNames _tlIkindErrors _tlImiscerrors _tlIoperatorFixities _tlIpreviousWasAlsoFB _tlIrestrictedNames _tlIself _tlIsuspiciousFBs _tlItypeSignatures _tlIunboundNames _tlIwarnings) = inv_Declarations_s32 _tlX32 (T_Declarations_vIn31 _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOcollectTypeConstructors _tlOcollectTypeSynonyms _tlOcollectValueConstructors _tlOcounter _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoperatorFixities _tlOoptions _tlOorderedTypeSynonyms _tlOpreviousWasAlsoFB _tlOsuspiciousFBs _tlOtypeConstructors _tlOtypeSignatures _tlOvalueConstructors _tlOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule731 _hdIcollectInstances _tlIcollectInstances
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule732 _hdIdeclVarNames _tlIdeclVarNames
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule733 _hdIrestrictedNames _tlIrestrictedNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule734 _hdIunboundNames _tlIunboundNames
         _self = rule735 _hdIself _tlIself
         _lhsOself :: Declarations
         _lhsOself = rule736 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule737 _tlIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule738 _tlIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule739 _tlIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule740 _tlIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule741 _tlIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule742 _tlIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule743 _tlImiscerrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule744 _tlIoperatorFixities
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule745 _tlIpreviousWasAlsoFB
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule746 _tlIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule747 _tlItypeSignatures
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule748 _tlIwarnings
         _hdOallTypeConstructors = rule749 _lhsIallTypeConstructors
         _hdOallValueConstructors = rule750 _lhsIallValueConstructors
         _hdOclassEnvironment = rule751 _lhsIclassEnvironment
         _hdOcollectScopeInfos = rule752 _lhsIcollectScopeInfos
         _hdOcollectTypeConstructors = rule753 _lhsIcollectTypeConstructors
         _hdOcollectTypeSynonyms = rule754 _lhsIcollectTypeSynonyms
         _hdOcollectValueConstructors = rule755 _lhsIcollectValueConstructors
         _hdOcounter = rule756 _lhsIcounter
         _hdOkindErrors = rule757 _lhsIkindErrors
         _hdOmiscerrors = rule758 _lhsImiscerrors
         _hdOnamesInScope = rule759 _lhsInamesInScope
         _hdOoperatorFixities = rule760 _lhsIoperatorFixities
         _hdOoptions = rule761 _lhsIoptions
         _hdOorderedTypeSynonyms = rule762 _lhsIorderedTypeSynonyms
         _hdOpreviousWasAlsoFB = rule763 _lhsIpreviousWasAlsoFB
         _hdOsuspiciousFBs = rule764 _lhsIsuspiciousFBs
         _hdOtypeConstructors = rule765 _lhsItypeConstructors
         _hdOtypeSignatures = rule766 _lhsItypeSignatures
         _hdOvalueConstructors = rule767 _lhsIvalueConstructors
         _hdOwarnings = rule768 _lhsIwarnings
         _tlOallTypeConstructors = rule769 _lhsIallTypeConstructors
         _tlOallValueConstructors = rule770 _lhsIallValueConstructors
         _tlOclassEnvironment = rule771 _lhsIclassEnvironment
         _tlOcollectScopeInfos = rule772 _hdIcollectScopeInfos
         _tlOcollectTypeConstructors = rule773 _hdIcollectTypeConstructors
         _tlOcollectTypeSynonyms = rule774 _hdIcollectTypeSynonyms
         _tlOcollectValueConstructors = rule775 _hdIcollectValueConstructors
         _tlOcounter = rule776 _hdIcounter
         _tlOkindErrors = rule777 _hdIkindErrors
         _tlOmiscerrors = rule778 _hdImiscerrors
         _tlOnamesInScope = rule779 _lhsInamesInScope
         _tlOoperatorFixities = rule780 _hdIoperatorFixities
         _tlOoptions = rule781 _lhsIoptions
         _tlOorderedTypeSynonyms = rule782 _lhsIorderedTypeSynonyms
         _tlOpreviousWasAlsoFB = rule783 _hdIpreviousWasAlsoFB
         _tlOsuspiciousFBs = rule784 _hdIsuspiciousFBs
         _tlOtypeConstructors = rule785 _lhsItypeConstructors
         _tlOtypeSignatures = rule786 _hdItypeSignatures
         _tlOvalueConstructors = rule787 _lhsIvalueConstructors
         _tlOwarnings = rule788 _hdIwarnings
         __result_ = T_Declarations_vOut31 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declarations_s32 v31
   {-# INLINE rule731 #-}
   rule731 = \ ((_hdIcollectInstances) :: [(Name, Instance)]) ((_tlIcollectInstances) :: [(Name, Instance)]) ->
     _hdIcollectInstances  ++  _tlIcollectInstances
   {-# INLINE rule732 #-}
   rule732 = \ ((_hdIdeclVarNames) :: Names) ((_tlIdeclVarNames) :: Names) ->
     _hdIdeclVarNames ++ _tlIdeclVarNames
   {-# INLINE rule733 #-}
   rule733 = \ ((_hdIrestrictedNames) :: Names) ((_tlIrestrictedNames) :: Names) ->
     _hdIrestrictedNames  ++  _tlIrestrictedNames
   {-# INLINE rule734 #-}
   rule734 = \ ((_hdIunboundNames) :: Names) ((_tlIunboundNames) :: Names) ->
     _hdIunboundNames ++ _tlIunboundNames
   {-# INLINE rule735 #-}
   rule735 = \ ((_hdIself) :: Declaration) ((_tlIself) :: Declarations) ->
     (:) _hdIself _tlIself
   {-# INLINE rule736 #-}
   rule736 = \ _self ->
     _self
   {-# INLINE rule737 #-}
   rule737 = \ ((_tlIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _tlIcollectScopeInfos
   {-# INLINE rule738 #-}
   rule738 = \ ((_tlIcollectTypeConstructors) :: [(Name,Int)]) ->
     _tlIcollectTypeConstructors
   {-# INLINE rule739 #-}
   rule739 = \ ((_tlIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _tlIcollectTypeSynonyms
   {-# INLINE rule740 #-}
   rule740 = \ ((_tlIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _tlIcollectValueConstructors
   {-# INLINE rule741 #-}
   rule741 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule742 #-}
   rule742 = \ ((_tlIkindErrors) :: [Error]) ->
     _tlIkindErrors
   {-# INLINE rule743 #-}
   rule743 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule744 #-}
   rule744 = \ ((_tlIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _tlIoperatorFixities
   {-# INLINE rule745 #-}
   rule745 = \ ((_tlIpreviousWasAlsoFB) :: Maybe Name) ->
     _tlIpreviousWasAlsoFB
   {-# INLINE rule746 #-}
   rule746 = \ ((_tlIsuspiciousFBs) :: [(Name,Name)]) ->
     _tlIsuspiciousFBs
   {-# INLINE rule747 #-}
   rule747 = \ ((_tlItypeSignatures) :: [(Name,TpScheme)]) ->
     _tlItypeSignatures
   {-# INLINE rule748 #-}
   rule748 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule749 #-}
   rule749 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule750 #-}
   rule750 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule751 #-}
   rule751 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule752 #-}
   rule752 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule753 #-}
   rule753 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule754 #-}
   rule754 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule755 #-}
   rule755 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule756 #-}
   rule756 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule757 #-}
   rule757 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule758 #-}
   rule758 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule759 #-}
   rule759 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule760 #-}
   rule760 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule761 #-}
   rule761 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule762 #-}
   rule762 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule763 #-}
   rule763 = \ ((_lhsIpreviousWasAlsoFB) :: Maybe Name) ->
     _lhsIpreviousWasAlsoFB
   {-# INLINE rule764 #-}
   rule764 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule765 #-}
   rule765 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule766 #-}
   rule766 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule767 #-}
   rule767 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule768 #-}
   rule768 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule769 #-}
   rule769 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule770 #-}
   rule770 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule771 #-}
   rule771 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule772 #-}
   rule772 = \ ((_hdIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _hdIcollectScopeInfos
   {-# INLINE rule773 #-}
   rule773 = \ ((_hdIcollectTypeConstructors) :: [(Name,Int)]) ->
     _hdIcollectTypeConstructors
   {-# INLINE rule774 #-}
   rule774 = \ ((_hdIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _hdIcollectTypeSynonyms
   {-# INLINE rule775 #-}
   rule775 = \ ((_hdIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _hdIcollectValueConstructors
   {-# INLINE rule776 #-}
   rule776 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule777 #-}
   rule777 = \ ((_hdIkindErrors) :: [Error]) ->
     _hdIkindErrors
   {-# INLINE rule778 #-}
   rule778 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule779 #-}
   rule779 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule780 #-}
   rule780 = \ ((_hdIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _hdIoperatorFixities
   {-# INLINE rule781 #-}
   rule781 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule782 #-}
   rule782 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule783 #-}
   rule783 = \ ((_hdIpreviousWasAlsoFB) :: Maybe Name) ->
     _hdIpreviousWasAlsoFB
   {-# INLINE rule784 #-}
   rule784 = \ ((_hdIsuspiciousFBs) :: [(Name,Name)]) ->
     _hdIsuspiciousFBs
   {-# INLINE rule785 #-}
   rule785 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule786 #-}
   rule786 = \ ((_hdItypeSignatures) :: [(Name,TpScheme)]) ->
     _hdItypeSignatures
   {-# INLINE rule787 #-}
   rule787 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule788 #-}
   rule788 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_Declarations_Nil #-}
sem_Declarations_Nil ::  T_Declarations 
sem_Declarations_Nil  = T_Declarations (return st32) where
   {-# NOINLINE st32 #-}
   st32 = let
      v31 :: T_Declarations_v31 
      v31 = \ (T_Declarations_vIn31 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcollectTypeConstructors _lhsIcollectTypeSynonyms _lhsIcollectValueConstructors _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoperatorFixities _lhsIoptions _lhsIorderedTypeSynonyms _lhsIpreviousWasAlsoFB _lhsIsuspiciousFBs _lhsItypeConstructors _lhsItypeSignatures _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule789  ()
         _lhsOdeclVarNames :: Names
         _lhsOdeclVarNames = rule790  ()
         _lhsOrestrictedNames :: Names
         _lhsOrestrictedNames = rule791  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule792  ()
         _self = rule793  ()
         _lhsOself :: Declarations
         _lhsOself = rule794 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule795 _lhsIcollectScopeInfos
         _lhsOcollectTypeConstructors :: [(Name,Int)]
         _lhsOcollectTypeConstructors = rule796 _lhsIcollectTypeConstructors
         _lhsOcollectTypeSynonyms :: [(Name,(Int,Tps -> Tp))]
         _lhsOcollectTypeSynonyms = rule797 _lhsIcollectTypeSynonyms
         _lhsOcollectValueConstructors :: [(Name,TpScheme)]
         _lhsOcollectValueConstructors = rule798 _lhsIcollectValueConstructors
         _lhsOcounter :: Int
         _lhsOcounter = rule799 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule800 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule801 _lhsImiscerrors
         _lhsOoperatorFixities :: [(Name,(Int,Assoc))]
         _lhsOoperatorFixities = rule802 _lhsIoperatorFixities
         _lhsOpreviousWasAlsoFB :: Maybe Name
         _lhsOpreviousWasAlsoFB = rule803 _lhsIpreviousWasAlsoFB
         _lhsOsuspiciousFBs :: [(Name,Name)]
         _lhsOsuspiciousFBs = rule804 _lhsIsuspiciousFBs
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule805 _lhsItypeSignatures
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule806 _lhsIwarnings
         __result_ = T_Declarations_vOut31 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcollectTypeConstructors _lhsOcollectTypeSynonyms _lhsOcollectValueConstructors _lhsOcounter _lhsOdeclVarNames _lhsOkindErrors _lhsOmiscerrors _lhsOoperatorFixities _lhsOpreviousWasAlsoFB _lhsOrestrictedNames _lhsOself _lhsOsuspiciousFBs _lhsOtypeSignatures _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Declarations_s32 v31
   {-# INLINE rule789 #-}
   rule789 = \  (_ :: ()) ->
     []
   {-# INLINE rule790 #-}
   rule790 = \  (_ :: ()) ->
     []
   {-# INLINE rule791 #-}
   rule791 = \  (_ :: ()) ->
     []
   {-# INLINE rule792 #-}
   rule792 = \  (_ :: ()) ->
     []
   {-# INLINE rule793 #-}
   rule793 = \  (_ :: ()) ->
     []
   {-# INLINE rule794 #-}
   rule794 = \ _self ->
     _self
   {-# INLINE rule795 #-}
   rule795 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule796 #-}
   rule796 = \ ((_lhsIcollectTypeConstructors) :: [(Name,Int)]) ->
     _lhsIcollectTypeConstructors
   {-# INLINE rule797 #-}
   rule797 = \ ((_lhsIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
     _lhsIcollectTypeSynonyms
   {-# INLINE rule798 #-}
   rule798 = \ ((_lhsIcollectValueConstructors) :: [(Name,TpScheme)]) ->
     _lhsIcollectValueConstructors
   {-# INLINE rule799 #-}
   rule799 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule800 #-}
   rule800 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule801 #-}
   rule801 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule802 #-}
   rule802 = \ ((_lhsIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
     _lhsIoperatorFixities
   {-# INLINE rule803 #-}
   rule803 = \ ((_lhsIpreviousWasAlsoFB) :: Maybe Name) ->
     _lhsIpreviousWasAlsoFB
   {-# INLINE rule804 #-}
   rule804 = \ ((_lhsIsuspiciousFBs) :: [(Name,Name)]) ->
     _lhsIsuspiciousFBs
   {-# INLINE rule805 #-}
   rule805 = \ ((_lhsItypeSignatures) :: [(Name,TpScheme)]) ->
     _lhsItypeSignatures
   {-# INLINE rule806 #-}
   rule806 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Export ------------------------------------------------------
-- wrapper
data Inh_Export  = Inh_Export { consInScope_Inh_Export :: (Names), modulesInScope_Inh_Export :: (Names), namesInScop_Inh_Export :: (Names), tyconsInScope_Inh_Export :: (Names) }
data Syn_Export  = Syn_Export { exportErrors_Syn_Export :: ([Error]), self_Syn_Export :: (Export) }
{-# INLINABLE wrap_Export #-}
wrap_Export :: T_Export  -> Inh_Export  -> (Syn_Export )
wrap_Export (T_Export act) (Inh_Export _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Export_vIn34 _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope
        (T_Export_vOut34 _lhsOexportErrors _lhsOself) <- return (inv_Export_s35 sem arg)
        return (Syn_Export _lhsOexportErrors _lhsOself)
   )

-- cata
{-# NOINLINE sem_Export #-}
sem_Export :: Export  -> T_Export 
sem_Export ( Export_Variable range_ name_ ) = sem_Export_Variable ( sem_Range range_ ) ( sem_Name name_ )
sem_Export ( Export_TypeOrClass range_ name_ names_ ) = sem_Export_TypeOrClass ( sem_Range range_ ) ( sem_Name name_ ) ( sem_MaybeNames names_ )
sem_Export ( Export_TypeOrClassComplete range_ name_ ) = sem_Export_TypeOrClassComplete ( sem_Range range_ ) ( sem_Name name_ )
sem_Export ( Export_Module range_ name_ ) = sem_Export_Module ( sem_Range range_ ) ( sem_Name name_ )

-- semantic domain
newtype T_Export  = T_Export {
                             attach_T_Export :: Identity (T_Export_s35 )
                             }
newtype T_Export_s35  = C_Export_s35 {
                                     inv_Export_s35 :: (T_Export_v34 )
                                     }
data T_Export_s36  = C_Export_s36
type T_Export_v34  = (T_Export_vIn34 ) -> (T_Export_vOut34 )
data T_Export_vIn34  = T_Export_vIn34 (Names) (Names) (Names) (Names)
data T_Export_vOut34  = T_Export_vOut34 ([Error]) (Export)
{-# NOINLINE sem_Export_Variable #-}
sem_Export_Variable :: T_Range  -> T_Name  -> T_Export 
sem_Export_Variable arg_range_ arg_name_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOexportErrors :: [Error]
         _lhsOexportErrors = rule807 _lhsInamesInScop _nameIself
         _self = rule808 _nameIself _rangeIself
         _lhsOself :: Export
         _lhsOself = rule809 _self
         __result_ = T_Export_vOut34 _lhsOexportErrors _lhsOself
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule807 #-}
   rule807 = \ ((_lhsInamesInScop) :: Names) ((_nameIself) :: Name) ->
                                          checkExport ExportVariable _nameIself
                                             _lhsInamesInScop
   {-# INLINE rule808 #-}
   rule808 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Export_Variable _rangeIself _nameIself
   {-# INLINE rule809 #-}
   rule809 = \ _self ->
     _self
{-# NOINLINE sem_Export_TypeOrClass #-}
sem_Export_TypeOrClass :: T_Range  -> T_Name  -> T_MaybeNames  -> T_Export 
sem_Export_TypeOrClass arg_range_ arg_name_ arg_names_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _namesX107 = Control.Monad.Identity.runIdentity (attach_T_MaybeNames (arg_names_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_MaybeNames_vOut106 _namesIself) = inv_MaybeNames_s107 _namesX107 (T_MaybeNames_vIn106 )
         _lhsOexportErrors :: [Error]
         _lhsOexportErrors = rule810  ()
         _self = rule811 _nameIself _namesIself _rangeIself
         _lhsOself :: Export
         _lhsOself = rule812 _self
         __result_ = T_Export_vOut34 _lhsOexportErrors _lhsOself
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule810 #-}
   rule810 = \  (_ :: ()) ->
     []
   {-# INLINE rule811 #-}
   rule811 = \ ((_nameIself) :: Name) ((_namesIself) :: MaybeNames) ((_rangeIself) :: Range) ->
     Export_TypeOrClass _rangeIself _nameIself _namesIself
   {-# INLINE rule812 #-}
   rule812 = \ _self ->
     _self
{-# NOINLINE sem_Export_TypeOrClassComplete #-}
sem_Export_TypeOrClassComplete :: T_Range  -> T_Name  -> T_Export 
sem_Export_TypeOrClassComplete arg_range_ arg_name_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOexportErrors :: [Error]
         _lhsOexportErrors = rule813  ()
         _self = rule814 _nameIself _rangeIself
         _lhsOself :: Export
         _lhsOself = rule815 _self
         __result_ = T_Export_vOut34 _lhsOexportErrors _lhsOself
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule813 #-}
   rule813 = \  (_ :: ()) ->
     []
   {-# INLINE rule814 #-}
   rule814 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Export_TypeOrClassComplete _rangeIself _nameIself
   {-# INLINE rule815 #-}
   rule815 = \ _self ->
     _self
{-# NOINLINE sem_Export_Module #-}
sem_Export_Module :: T_Range  -> T_Name  -> T_Export 
sem_Export_Module arg_range_ arg_name_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOexportErrors :: [Error]
         _lhsOexportErrors = rule816 _lhsImodulesInScope _nameIself
         _self = rule817 _nameIself _rangeIself
         _lhsOself :: Export
         _lhsOself = rule818 _self
         __result_ = T_Export_vOut34 _lhsOexportErrors _lhsOself
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule816 #-}
   rule816 = \ ((_lhsImodulesInScope) :: Names) ((_nameIself) :: Name) ->
                                          checkExport ExportModule _nameIself
                                             _lhsImodulesInScope
   {-# INLINE rule817 #-}
   rule817 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Export_Module _rangeIself _nameIself
   {-# INLINE rule818 #-}
   rule818 = \ _self ->
     _self

-- Exports -----------------------------------------------------
-- wrapper
data Inh_Exports  = Inh_Exports { consInScope_Inh_Exports :: (Names), modulesInScope_Inh_Exports :: (Names), namesInScop_Inh_Exports :: (Names), tyconsInScope_Inh_Exports :: (Names) }
data Syn_Exports  = Syn_Exports { exportErrors_Syn_Exports :: ([Error]), self_Syn_Exports :: (Exports) }
{-# INLINABLE wrap_Exports #-}
wrap_Exports :: T_Exports  -> Inh_Exports  -> (Syn_Exports )
wrap_Exports (T_Exports act) (Inh_Exports _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Exports_vIn37 _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope
        (T_Exports_vOut37 _lhsOexportErrors _lhsOself) <- return (inv_Exports_s38 sem arg)
        return (Syn_Exports _lhsOexportErrors _lhsOself)
   )

-- cata
{-# NOINLINE sem_Exports #-}
sem_Exports :: Exports  -> T_Exports 
sem_Exports list = Prelude.foldr sem_Exports_Cons sem_Exports_Nil (Prelude.map sem_Export list)

-- semantic domain
newtype T_Exports  = T_Exports {
                               attach_T_Exports :: Identity (T_Exports_s38 )
                               }
newtype T_Exports_s38  = C_Exports_s38 {
                                       inv_Exports_s38 :: (T_Exports_v37 )
                                       }
data T_Exports_s39  = C_Exports_s39
type T_Exports_v37  = (T_Exports_vIn37 ) -> (T_Exports_vOut37 )
data T_Exports_vIn37  = T_Exports_vIn37 (Names) (Names) (Names) (Names)
data T_Exports_vOut37  = T_Exports_vOut37 ([Error]) (Exports)
{-# NOINLINE sem_Exports_Cons #-}
sem_Exports_Cons :: T_Export  -> T_Exports  -> T_Exports 
sem_Exports_Cons arg_hd_ arg_tl_ = T_Exports (return st38) where
   {-# NOINLINE st38 #-}
   st38 = let
      v37 :: T_Exports_v37 
      v37 = \ (T_Exports_vIn37 _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope) -> ( let
         _hdX35 = Control.Monad.Identity.runIdentity (attach_T_Export (arg_hd_))
         _tlX38 = Control.Monad.Identity.runIdentity (attach_T_Exports (arg_tl_))
         (T_Export_vOut34 _hdIexportErrors _hdIself) = inv_Export_s35 _hdX35 (T_Export_vIn34 _hdOconsInScope _hdOmodulesInScope _hdOnamesInScop _hdOtyconsInScope)
         (T_Exports_vOut37 _tlIexportErrors _tlIself) = inv_Exports_s38 _tlX38 (T_Exports_vIn37 _tlOconsInScope _tlOmodulesInScope _tlOnamesInScop _tlOtyconsInScope)
         _lhsOexportErrors :: [Error]
         _lhsOexportErrors = rule819 _hdIexportErrors _tlIexportErrors
         _self = rule820 _hdIself _tlIself
         _lhsOself :: Exports
         _lhsOself = rule821 _self
         _hdOconsInScope = rule822 _lhsIconsInScope
         _hdOmodulesInScope = rule823 _lhsImodulesInScope
         _hdOnamesInScop = rule824 _lhsInamesInScop
         _hdOtyconsInScope = rule825 _lhsItyconsInScope
         _tlOconsInScope = rule826 _lhsIconsInScope
         _tlOmodulesInScope = rule827 _lhsImodulesInScope
         _tlOnamesInScop = rule828 _lhsInamesInScop
         _tlOtyconsInScope = rule829 _lhsItyconsInScope
         __result_ = T_Exports_vOut37 _lhsOexportErrors _lhsOself
         in __result_ )
     in C_Exports_s38 v37
   {-# INLINE rule819 #-}
   rule819 = \ ((_hdIexportErrors) :: [Error]) ((_tlIexportErrors) :: [Error]) ->
     _hdIexportErrors  ++  _tlIexportErrors
   {-# INLINE rule820 #-}
   rule820 = \ ((_hdIself) :: Export) ((_tlIself) :: Exports) ->
     (:) _hdIself _tlIself
   {-# INLINE rule821 #-}
   rule821 = \ _self ->
     _self
   {-# INLINE rule822 #-}
   rule822 = \ ((_lhsIconsInScope) :: Names) ->
     _lhsIconsInScope
   {-# INLINE rule823 #-}
   rule823 = \ ((_lhsImodulesInScope) :: Names) ->
     _lhsImodulesInScope
   {-# INLINE rule824 #-}
   rule824 = \ ((_lhsInamesInScop) :: Names) ->
     _lhsInamesInScop
   {-# INLINE rule825 #-}
   rule825 = \ ((_lhsItyconsInScope) :: Names) ->
     _lhsItyconsInScope
   {-# INLINE rule826 #-}
   rule826 = \ ((_lhsIconsInScope) :: Names) ->
     _lhsIconsInScope
   {-# INLINE rule827 #-}
   rule827 = \ ((_lhsImodulesInScope) :: Names) ->
     _lhsImodulesInScope
   {-# INLINE rule828 #-}
   rule828 = \ ((_lhsInamesInScop) :: Names) ->
     _lhsInamesInScop
   {-# INLINE rule829 #-}
   rule829 = \ ((_lhsItyconsInScope) :: Names) ->
     _lhsItyconsInScope
{-# NOINLINE sem_Exports_Nil #-}
sem_Exports_Nil ::  T_Exports 
sem_Exports_Nil  = T_Exports (return st38) where
   {-# NOINLINE st38 #-}
   st38 = let
      v37 :: T_Exports_v37 
      v37 = \ (T_Exports_vIn37 _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope) -> ( let
         _lhsOexportErrors :: [Error]
         _lhsOexportErrors = rule830  ()
         _self = rule831  ()
         _lhsOself :: Exports
         _lhsOself = rule832 _self
         __result_ = T_Exports_vOut37 _lhsOexportErrors _lhsOself
         in __result_ )
     in C_Exports_s38 v37
   {-# INLINE rule830 #-}
   rule830 = \  (_ :: ()) ->
     []
   {-# INLINE rule831 #-}
   rule831 = \  (_ :: ()) ->
     []
   {-# INLINE rule832 #-}
   rule832 = \ _self ->
     _self

-- Expression --------------------------------------------------
-- wrapper
data Inh_Expression  = Inh_Expression { allTypeConstructors_Inh_Expression :: (Names), allValueConstructors_Inh_Expression :: (Names), classEnvironment_Inh_Expression :: (ClassEnvironment), collectScopeInfos_Inh_Expression :: ([(ScopeInfo, Entity)]), counter_Inh_Expression :: (Int), kindErrors_Inh_Expression :: ([Error]), miscerrors_Inh_Expression :: ([Error]), namesInScope_Inh_Expression :: (Names), options_Inh_Expression :: ([Option]), orderedTypeSynonyms_Inh_Expression :: (OrderedTypeSynonyms), typeConstructors_Inh_Expression :: (M.Map Name Int), valueConstructors_Inh_Expression :: (M.Map Name TpScheme), warnings_Inh_Expression :: ([Warning]) }
data Syn_Expression  = Syn_Expression { collectInstances_Syn_Expression :: ([(Name, Instance)]), collectScopeInfos_Syn_Expression :: ([(ScopeInfo, Entity)]), counter_Syn_Expression :: (Int), kindErrors_Syn_Expression :: ([Error]), miscerrors_Syn_Expression :: ([Error]), self_Syn_Expression :: (Expression), unboundNames_Syn_Expression :: (Names), warnings_Syn_Expression :: ([Warning]) }
{-# INLINABLE wrap_Expression #-}
wrap_Expression :: T_Expression  -> Inh_Expression  -> (Syn_Expression )
wrap_Expression (T_Expression act) (Inh_Expression _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_Expression_s41 sem arg)
        return (Syn_Expression _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Expression #-}
sem_Expression :: Expression  -> T_Expression 
sem_Expression ( Expression_Hole range_ id_ ) = sem_Expression_Hole ( sem_Range range_ ) id_
sem_Expression ( Expression_Feedback range_ feedback_ expression_ ) = sem_Expression_Feedback ( sem_Range range_ ) feedback_ ( sem_Expression expression_ )
sem_Expression ( Expression_MustUse range_ expression_ ) = sem_Expression_MustUse ( sem_Range range_ ) ( sem_Expression expression_ )
sem_Expression ( Expression_Literal range_ literal_ ) = sem_Expression_Literal ( sem_Range range_ ) ( sem_Literal literal_ )
sem_Expression ( Expression_Variable range_ name_ ) = sem_Expression_Variable ( sem_Range range_ ) ( sem_Name name_ )
sem_Expression ( Expression_Constructor range_ name_ ) = sem_Expression_Constructor ( sem_Range range_ ) ( sem_Name name_ )
sem_Expression ( Expression_Parenthesized range_ expression_ ) = sem_Expression_Parenthesized ( sem_Range range_ ) ( sem_Expression expression_ )
sem_Expression ( Expression_NormalApplication range_ function_ arguments_ ) = sem_Expression_NormalApplication ( sem_Range range_ ) ( sem_Expression function_ ) ( sem_Expressions arguments_ )
sem_Expression ( Expression_InfixApplication range_ leftExpression_ operator_ rightExpression_ ) = sem_Expression_InfixApplication ( sem_Range range_ ) ( sem_MaybeExpression leftExpression_ ) ( sem_Expression operator_ ) ( sem_MaybeExpression rightExpression_ )
sem_Expression ( Expression_If range_ guardExpression_ thenExpression_ elseExpression_ ) = sem_Expression_If ( sem_Range range_ ) ( sem_Expression guardExpression_ ) ( sem_Expression thenExpression_ ) ( sem_Expression elseExpression_ )
sem_Expression ( Expression_Lambda range_ patterns_ expression_ ) = sem_Expression_Lambda ( sem_Range range_ ) ( sem_Patterns patterns_ ) ( sem_Expression expression_ )
sem_Expression ( Expression_Case range_ expression_ alternatives_ ) = sem_Expression_Case ( sem_Range range_ ) ( sem_Expression expression_ ) ( sem_Alternatives alternatives_ )
sem_Expression ( Expression_Let range_ declarations_ expression_ ) = sem_Expression_Let ( sem_Range range_ ) ( sem_Declarations declarations_ ) ( sem_Expression expression_ )
sem_Expression ( Expression_Do range_ statements_ ) = sem_Expression_Do ( sem_Range range_ ) ( sem_Statements statements_ )
sem_Expression ( Expression_List range_ expressions_ ) = sem_Expression_List ( sem_Range range_ ) ( sem_Expressions expressions_ )
sem_Expression ( Expression_Tuple range_ expressions_ ) = sem_Expression_Tuple ( sem_Range range_ ) ( sem_Expressions expressions_ )
sem_Expression ( Expression_Comprehension range_ expression_ qualifiers_ ) = sem_Expression_Comprehension ( sem_Range range_ ) ( sem_Expression expression_ ) ( sem_Qualifiers qualifiers_ )
sem_Expression ( Expression_Typed range_ expression_ type_ ) = sem_Expression_Typed ( sem_Range range_ ) ( sem_Expression expression_ ) ( sem_Type type_ )
sem_Expression ( Expression_RecordConstruction range_ name_ recordExpressionBindings_ ) = sem_Expression_RecordConstruction ( sem_Range range_ ) ( sem_Name name_ ) ( sem_RecordExpressionBindings recordExpressionBindings_ )
sem_Expression ( Expression_RecordUpdate range_ expression_ recordExpressionBindings_ ) = sem_Expression_RecordUpdate ( sem_Range range_ ) ( sem_Expression expression_ ) ( sem_RecordExpressionBindings recordExpressionBindings_ )
sem_Expression ( Expression_Enum range_ from_ then_ to_ ) = sem_Expression_Enum ( sem_Range range_ ) ( sem_Expression from_ ) ( sem_MaybeExpression then_ ) ( sem_MaybeExpression to_ )
sem_Expression ( Expression_Negate range_ expression_ ) = sem_Expression_Negate ( sem_Range range_ ) ( sem_Expression expression_ )
sem_Expression ( Expression_NegateFloat range_ expression_ ) = sem_Expression_NegateFloat ( sem_Range range_ ) ( sem_Expression expression_ )

-- semantic domain
newtype T_Expression  = T_Expression {
                                     attach_T_Expression :: Identity (T_Expression_s41 )
                                     }
newtype T_Expression_s41  = C_Expression_s41 {
                                             inv_Expression_s41 :: (T_Expression_v40 )
                                             }
data T_Expression_s42  = C_Expression_s42
type T_Expression_v40  = (T_Expression_vIn40 ) -> (T_Expression_vOut40 )
data T_Expression_vIn40  = T_Expression_vIn40 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_Expression_vOut40  = T_Expression_vOut40 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Expression) (Names) ([Warning])
{-# NOINLINE sem_Expression_Hole #-}
sem_Expression_Hole :: T_Range  -> (Integer) -> T_Expression 
sem_Expression_Hole arg_range_ arg_id_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule833  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule834  ()
         _self = rule835 _rangeIself arg_id_
         _lhsOself :: Expression
         _lhsOself = rule836 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule837 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule838 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule839 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule840 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule841 _lhsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule833 #-}
   rule833 = \  (_ :: ()) ->
     []
   {-# INLINE rule834 #-}
   rule834 = \  (_ :: ()) ->
     []
   {-# INLINE rule835 #-}
   rule835 = \ ((_rangeIself) :: Range) id_ ->
     Expression_Hole _rangeIself id_
   {-# INLINE rule836 #-}
   rule836 = \ _self ->
     _self
   {-# INLINE rule837 #-}
   rule837 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule838 #-}
   rule838 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule839 #-}
   rule839 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule840 #-}
   rule840 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule841 #-}
   rule841 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Expression_Feedback #-}
sem_Expression_Feedback :: T_Range  -> (String) -> T_Expression  -> T_Expression 
sem_Expression_Feedback arg_range_ arg_feedback_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule842 _expressionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule843 _expressionIunboundNames
         _self = rule844 _expressionIself _rangeIself arg_feedback_
         _lhsOself :: Expression
         _lhsOself = rule845 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule846 _expressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule847 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule848 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule849 _expressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule850 _expressionIwarnings
         _expressionOallTypeConstructors = rule851 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule852 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule853 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule854 _lhsIcollectScopeInfos
         _expressionOcounter = rule855 _lhsIcounter
         _expressionOkindErrors = rule856 _lhsIkindErrors
         _expressionOmiscerrors = rule857 _lhsImiscerrors
         _expressionOnamesInScope = rule858 _lhsInamesInScope
         _expressionOoptions = rule859 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule860 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule861 _lhsItypeConstructors
         _expressionOvalueConstructors = rule862 _lhsIvalueConstructors
         _expressionOwarnings = rule863 _lhsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule842 #-}
   rule842 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule843 #-}
   rule843 = \ ((_expressionIunboundNames) :: Names) ->
     _expressionIunboundNames
   {-# INLINE rule844 #-}
   rule844 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) feedback_ ->
     Expression_Feedback _rangeIself feedback_ _expressionIself
   {-# INLINE rule845 #-}
   rule845 = \ _self ->
     _self
   {-# INLINE rule846 #-}
   rule846 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule847 #-}
   rule847 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule848 #-}
   rule848 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule849 #-}
   rule849 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule850 #-}
   rule850 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule851 #-}
   rule851 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule852 #-}
   rule852 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule853 #-}
   rule853 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule854 #-}
   rule854 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule855 #-}
   rule855 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule856 #-}
   rule856 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule857 #-}
   rule857 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule858 #-}
   rule858 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule859 #-}
   rule859 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule860 #-}
   rule860 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule861 #-}
   rule861 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule862 #-}
   rule862 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule863 #-}
   rule863 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Expression_MustUse #-}
sem_Expression_MustUse :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_MustUse arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule864 _expressionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule865 _expressionIunboundNames
         _self = rule866 _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule867 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule868 _expressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule869 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule870 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule871 _expressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule872 _expressionIwarnings
         _expressionOallTypeConstructors = rule873 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule874 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule875 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule876 _lhsIcollectScopeInfos
         _expressionOcounter = rule877 _lhsIcounter
         _expressionOkindErrors = rule878 _lhsIkindErrors
         _expressionOmiscerrors = rule879 _lhsImiscerrors
         _expressionOnamesInScope = rule880 _lhsInamesInScope
         _expressionOoptions = rule881 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule882 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule883 _lhsItypeConstructors
         _expressionOvalueConstructors = rule884 _lhsIvalueConstructors
         _expressionOwarnings = rule885 _lhsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule864 #-}
   rule864 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule865 #-}
   rule865 = \ ((_expressionIunboundNames) :: Names) ->
     _expressionIunboundNames
   {-# INLINE rule866 #-}
   rule866 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_MustUse _rangeIself _expressionIself
   {-# INLINE rule867 #-}
   rule867 = \ _self ->
     _self
   {-# INLINE rule868 #-}
   rule868 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule869 #-}
   rule869 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule870 #-}
   rule870 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule871 #-}
   rule871 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule872 #-}
   rule872 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule873 #-}
   rule873 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule874 #-}
   rule874 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule875 #-}
   rule875 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule876 #-}
   rule876 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule877 #-}
   rule877 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule878 #-}
   rule878 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule879 #-}
   rule879 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule880 #-}
   rule880 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule881 #-}
   rule881 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule882 #-}
   rule882 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule883 #-}
   rule883 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule884 #-}
   rule884 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule885 #-}
   rule885 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Expression_Literal #-}
sem_Expression_Literal :: T_Range  -> T_Literal  -> T_Expression 
sem_Expression_Literal arg_range_ arg_literal_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalIcollectScopeInfos _literalImiscerrors _literalIself) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 _literalOcollectScopeInfos _literalOmiscerrors)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule886  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule887  ()
         _self = rule888 _literalIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule889 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule890 _literalIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule891 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule892 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule893 _literalImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule894 _lhsIwarnings
         _literalOcollectScopeInfos = rule895 _lhsIcollectScopeInfos
         _literalOmiscerrors = rule896 _lhsImiscerrors
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule886 #-}
   rule886 = \  (_ :: ()) ->
     []
   {-# INLINE rule887 #-}
   rule887 = \  (_ :: ()) ->
     []
   {-# INLINE rule888 #-}
   rule888 = \ ((_literalIself) :: Literal) ((_rangeIself) :: Range) ->
     Expression_Literal _rangeIself _literalIself
   {-# INLINE rule889 #-}
   rule889 = \ _self ->
     _self
   {-# INLINE rule890 #-}
   rule890 = \ ((_literalIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _literalIcollectScopeInfos
   {-# INLINE rule891 #-}
   rule891 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule892 #-}
   rule892 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule893 #-}
   rule893 = \ ((_literalImiscerrors) :: [Error]) ->
     _literalImiscerrors
   {-# INLINE rule894 #-}
   rule894 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule895 #-}
   rule895 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule896 #-}
   rule896 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
{-# NOINLINE sem_Expression_Variable #-}
sem_Expression_Variable :: T_Range  -> T_Name  -> T_Expression 
sem_Expression_Variable arg_range_ arg_name_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule897 _nameIself
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule898 _lhsImiscerrors _undefinedErrors
         _undefinedErrors = rule899 _lhsInamesInScope _nameIself
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule900  ()
         _self = rule901 _nameIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule902 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule903 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule904 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule905 _lhsIkindErrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule906 _lhsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule897 #-}
   rule897 = \ ((_nameIself) :: Name) ->
                                      [ _nameIself ]
   {-# INLINE rule898 #-}
   rule898 = \ ((_lhsImiscerrors) :: [Error]) _undefinedErrors ->
                                          _undefinedErrors ++ _lhsImiscerrors
   {-# INLINE rule899 #-}
   rule899 = \ ((_lhsInamesInScope) :: Names) ((_nameIself) :: Name) ->
                                           if _nameIself `elem` _lhsInamesInScope
                                             then []
                                             else [ Undefined Variable _nameIself _lhsInamesInScope [] ]
   {-# INLINE rule900 #-}
   rule900 = \  (_ :: ()) ->
     []
   {-# INLINE rule901 #-}
   rule901 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Expression_Variable _rangeIself _nameIself
   {-# INLINE rule902 #-}
   rule902 = \ _self ->
     _self
   {-# INLINE rule903 #-}
   rule903 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule904 #-}
   rule904 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule905 #-}
   rule905 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule906 #-}
   rule906 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Expression_Constructor #-}
sem_Expression_Constructor :: T_Range  -> T_Name  -> T_Expression 
sem_Expression_Constructor arg_range_ arg_name_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule907 _lhsImiscerrors _undefinedConstructorErrors
         _undefinedConstructorErrors = rule908 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsInamesInScope _lhsIvalueConstructors _nameIself
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule909  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule910  ()
         _self = rule911 _nameIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule912 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule913 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule914 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule915 _lhsIkindErrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule916 _lhsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule907 #-}
   rule907 = \ ((_lhsImiscerrors) :: [Error]) _undefinedConstructorErrors ->
                                      _undefinedConstructorErrors ++ _lhsImiscerrors
   {-# INLINE rule908 #-}
   rule908 = \ ((_lhsIallTypeConstructors) :: Names) ((_lhsIallValueConstructors) :: Names) ((_lhsInamesInScope) :: Names) ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ((_nameIself) :: Name) ->
                                                      case M.lookup _nameIself _lhsIvalueConstructors of
                                                         Nothing -> [ undefinedConstructorInExpr _nameIself (_lhsInamesInScope ++ _lhsIallValueConstructors) _lhsIallTypeConstructors ]
                                                         Just _  -> []
   {-# INLINE rule909 #-}
   rule909 = \  (_ :: ()) ->
     []
   {-# INLINE rule910 #-}
   rule910 = \  (_ :: ()) ->
     []
   {-# INLINE rule911 #-}
   rule911 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Expression_Constructor _rangeIself _nameIself
   {-# INLINE rule912 #-}
   rule912 = \ _self ->
     _self
   {-# INLINE rule913 #-}
   rule913 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule914 #-}
   rule914 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule915 #-}
   rule915 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule916 #-}
   rule916 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Expression_Parenthesized #-}
sem_Expression_Parenthesized :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_Parenthesized arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule917 _expressionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule918 _expressionIunboundNames
         _self = rule919 _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule920 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule921 _expressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule922 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule923 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule924 _expressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule925 _expressionIwarnings
         _expressionOallTypeConstructors = rule926 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule927 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule928 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule929 _lhsIcollectScopeInfos
         _expressionOcounter = rule930 _lhsIcounter
         _expressionOkindErrors = rule931 _lhsIkindErrors
         _expressionOmiscerrors = rule932 _lhsImiscerrors
         _expressionOnamesInScope = rule933 _lhsInamesInScope
         _expressionOoptions = rule934 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule935 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule936 _lhsItypeConstructors
         _expressionOvalueConstructors = rule937 _lhsIvalueConstructors
         _expressionOwarnings = rule938 _lhsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule917 #-}
   rule917 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule918 #-}
   rule918 = \ ((_expressionIunboundNames) :: Names) ->
     _expressionIunboundNames
   {-# INLINE rule919 #-}
   rule919 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_Parenthesized _rangeIself _expressionIself
   {-# INLINE rule920 #-}
   rule920 = \ _self ->
     _self
   {-# INLINE rule921 #-}
   rule921 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule922 #-}
   rule922 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule923 #-}
   rule923 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule924 #-}
   rule924 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule925 #-}
   rule925 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule926 #-}
   rule926 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule927 #-}
   rule927 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule928 #-}
   rule928 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule929 #-}
   rule929 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule930 #-}
   rule930 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule931 #-}
   rule931 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule932 #-}
   rule932 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule933 #-}
   rule933 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule934 #-}
   rule934 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule935 #-}
   rule935 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule936 #-}
   rule936 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule937 #-}
   rule937 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule938 #-}
   rule938 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Expression_NormalApplication #-}
sem_Expression_NormalApplication :: T_Range  -> T_Expression  -> T_Expressions  -> T_Expression 
sem_Expression_NormalApplication arg_range_ arg_function_ arg_arguments_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _functionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_function_))
         _argumentsX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_arguments_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _functionIcollectInstances _functionIcollectScopeInfos _functionIcounter _functionIkindErrors _functionImiscerrors _functionIself _functionIunboundNames _functionIwarnings) = inv_Expression_s41 _functionX41 (T_Expression_vIn40 _functionOallTypeConstructors _functionOallValueConstructors _functionOclassEnvironment _functionOcollectScopeInfos _functionOcounter _functionOkindErrors _functionOmiscerrors _functionOnamesInScope _functionOoptions _functionOorderedTypeSynonyms _functionOtypeConstructors _functionOvalueConstructors _functionOwarnings)
         (T_Expressions_vOut43 _argumentsIcollectInstances _argumentsIcollectScopeInfos _argumentsIcounter _argumentsIkindErrors _argumentsImiscerrors _argumentsIself _argumentsIunboundNames _argumentsIwarnings) = inv_Expressions_s44 _argumentsX44 (T_Expressions_vIn43 _argumentsOallTypeConstructors _argumentsOallValueConstructors _argumentsOclassEnvironment _argumentsOcollectScopeInfos _argumentsOcounter _argumentsOkindErrors _argumentsOmiscerrors _argumentsOnamesInScope _argumentsOoptions _argumentsOorderedTypeSynonyms _argumentsOtypeConstructors _argumentsOvalueConstructors _argumentsOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule939 _argumentsIcollectInstances _functionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule940 _argumentsIunboundNames _functionIunboundNames
         _self = rule941 _argumentsIself _functionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule942 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule943 _argumentsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule944 _argumentsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule945 _argumentsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule946 _argumentsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule947 _argumentsIwarnings
         _functionOallTypeConstructors = rule948 _lhsIallTypeConstructors
         _functionOallValueConstructors = rule949 _lhsIallValueConstructors
         _functionOclassEnvironment = rule950 _lhsIclassEnvironment
         _functionOcollectScopeInfos = rule951 _lhsIcollectScopeInfos
         _functionOcounter = rule952 _lhsIcounter
         _functionOkindErrors = rule953 _lhsIkindErrors
         _functionOmiscerrors = rule954 _lhsImiscerrors
         _functionOnamesInScope = rule955 _lhsInamesInScope
         _functionOoptions = rule956 _lhsIoptions
         _functionOorderedTypeSynonyms = rule957 _lhsIorderedTypeSynonyms
         _functionOtypeConstructors = rule958 _lhsItypeConstructors
         _functionOvalueConstructors = rule959 _lhsIvalueConstructors
         _functionOwarnings = rule960 _lhsIwarnings
         _argumentsOallTypeConstructors = rule961 _lhsIallTypeConstructors
         _argumentsOallValueConstructors = rule962 _lhsIallValueConstructors
         _argumentsOclassEnvironment = rule963 _lhsIclassEnvironment
         _argumentsOcollectScopeInfos = rule964 _functionIcollectScopeInfos
         _argumentsOcounter = rule965 _functionIcounter
         _argumentsOkindErrors = rule966 _functionIkindErrors
         _argumentsOmiscerrors = rule967 _functionImiscerrors
         _argumentsOnamesInScope = rule968 _lhsInamesInScope
         _argumentsOoptions = rule969 _lhsIoptions
         _argumentsOorderedTypeSynonyms = rule970 _lhsIorderedTypeSynonyms
         _argumentsOtypeConstructors = rule971 _lhsItypeConstructors
         _argumentsOvalueConstructors = rule972 _lhsIvalueConstructors
         _argumentsOwarnings = rule973 _functionIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule939 #-}
   rule939 = \ ((_argumentsIcollectInstances) :: [(Name, Instance)]) ((_functionIcollectInstances) :: [(Name, Instance)]) ->
     _functionIcollectInstances  ++  _argumentsIcollectInstances
   {-# INLINE rule940 #-}
   rule940 = \ ((_argumentsIunboundNames) :: Names) ((_functionIunboundNames) :: Names) ->
     _functionIunboundNames ++ _argumentsIunboundNames
   {-# INLINE rule941 #-}
   rule941 = \ ((_argumentsIself) :: Expressions) ((_functionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_NormalApplication _rangeIself _functionIself _argumentsIself
   {-# INLINE rule942 #-}
   rule942 = \ _self ->
     _self
   {-# INLINE rule943 #-}
   rule943 = \ ((_argumentsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _argumentsIcollectScopeInfos
   {-# INLINE rule944 #-}
   rule944 = \ ((_argumentsIcounter) :: Int) ->
     _argumentsIcounter
   {-# INLINE rule945 #-}
   rule945 = \ ((_argumentsIkindErrors) :: [Error]) ->
     _argumentsIkindErrors
   {-# INLINE rule946 #-}
   rule946 = \ ((_argumentsImiscerrors) :: [Error]) ->
     _argumentsImiscerrors
   {-# INLINE rule947 #-}
   rule947 = \ ((_argumentsIwarnings) :: [Warning]) ->
     _argumentsIwarnings
   {-# INLINE rule948 #-}
   rule948 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule949 #-}
   rule949 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule950 #-}
   rule950 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule951 #-}
   rule951 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule952 #-}
   rule952 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule953 #-}
   rule953 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule954 #-}
   rule954 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule955 #-}
   rule955 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule956 #-}
   rule956 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule957 #-}
   rule957 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule958 #-}
   rule958 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule959 #-}
   rule959 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule960 #-}
   rule960 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule961 #-}
   rule961 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule962 #-}
   rule962 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule963 #-}
   rule963 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule964 #-}
   rule964 = \ ((_functionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _functionIcollectScopeInfos
   {-# INLINE rule965 #-}
   rule965 = \ ((_functionIcounter) :: Int) ->
     _functionIcounter
   {-# INLINE rule966 #-}
   rule966 = \ ((_functionIkindErrors) :: [Error]) ->
     _functionIkindErrors
   {-# INLINE rule967 #-}
   rule967 = \ ((_functionImiscerrors) :: [Error]) ->
     _functionImiscerrors
   {-# INLINE rule968 #-}
   rule968 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule969 #-}
   rule969 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule970 #-}
   rule970 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule971 #-}
   rule971 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule972 #-}
   rule972 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule973 #-}
   rule973 = \ ((_functionIwarnings) :: [Warning]) ->
     _functionIwarnings
{-# NOINLINE sem_Expression_InfixApplication #-}
sem_Expression_InfixApplication :: T_Range  -> T_MaybeExpression  -> T_Expression  -> T_MaybeExpression  -> T_Expression 
sem_Expression_InfixApplication arg_range_ arg_leftExpression_ arg_operator_ arg_rightExpression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftExpressionX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_leftExpression_))
         _operatorX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_operator_))
         _rightExpressionX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_rightExpression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_MaybeExpression_vOut94 _leftExpressionIcollectInstances _leftExpressionIcollectScopeInfos _leftExpressionIcounter _leftExpressionIkindErrors _leftExpressionImiscerrors _leftExpressionIself _leftExpressionIunboundNames _leftExpressionIwarnings) = inv_MaybeExpression_s95 _leftExpressionX95 (T_MaybeExpression_vIn94 _leftExpressionOallTypeConstructors _leftExpressionOallValueConstructors _leftExpressionOclassEnvironment _leftExpressionOcollectScopeInfos _leftExpressionOcounter _leftExpressionOkindErrors _leftExpressionOmiscerrors _leftExpressionOnamesInScope _leftExpressionOoptions _leftExpressionOorderedTypeSynonyms _leftExpressionOtypeConstructors _leftExpressionOvalueConstructors _leftExpressionOwarnings)
         (T_Expression_vOut40 _operatorIcollectInstances _operatorIcollectScopeInfos _operatorIcounter _operatorIkindErrors _operatorImiscerrors _operatorIself _operatorIunboundNames _operatorIwarnings) = inv_Expression_s41 _operatorX41 (T_Expression_vIn40 _operatorOallTypeConstructors _operatorOallValueConstructors _operatorOclassEnvironment _operatorOcollectScopeInfos _operatorOcounter _operatorOkindErrors _operatorOmiscerrors _operatorOnamesInScope _operatorOoptions _operatorOorderedTypeSynonyms _operatorOtypeConstructors _operatorOvalueConstructors _operatorOwarnings)
         (T_MaybeExpression_vOut94 _rightExpressionIcollectInstances _rightExpressionIcollectScopeInfos _rightExpressionIcounter _rightExpressionIkindErrors _rightExpressionImiscerrors _rightExpressionIself _rightExpressionIunboundNames _rightExpressionIwarnings) = inv_MaybeExpression_s95 _rightExpressionX95 (T_MaybeExpression_vIn94 _rightExpressionOallTypeConstructors _rightExpressionOallValueConstructors _rightExpressionOclassEnvironment _rightExpressionOcollectScopeInfos _rightExpressionOcounter _rightExpressionOkindErrors _rightExpressionOmiscerrors _rightExpressionOnamesInScope _rightExpressionOoptions _rightExpressionOorderedTypeSynonyms _rightExpressionOtypeConstructors _rightExpressionOvalueConstructors _rightExpressionOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule974 _leftExpressionIcollectInstances _operatorIcollectInstances _rightExpressionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule975 _leftExpressionIunboundNames _operatorIunboundNames _rightExpressionIunboundNames
         _self = rule976 _leftExpressionIself _operatorIself _rangeIself _rightExpressionIself
         _lhsOself :: Expression
         _lhsOself = rule977 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule978 _rightExpressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule979 _rightExpressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule980 _rightExpressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule981 _rightExpressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule982 _rightExpressionIwarnings
         _leftExpressionOallTypeConstructors = rule983 _lhsIallTypeConstructors
         _leftExpressionOallValueConstructors = rule984 _lhsIallValueConstructors
         _leftExpressionOclassEnvironment = rule985 _lhsIclassEnvironment
         _leftExpressionOcollectScopeInfos = rule986 _lhsIcollectScopeInfos
         _leftExpressionOcounter = rule987 _lhsIcounter
         _leftExpressionOkindErrors = rule988 _lhsIkindErrors
         _leftExpressionOmiscerrors = rule989 _lhsImiscerrors
         _leftExpressionOnamesInScope = rule990 _lhsInamesInScope
         _leftExpressionOoptions = rule991 _lhsIoptions
         _leftExpressionOorderedTypeSynonyms = rule992 _lhsIorderedTypeSynonyms
         _leftExpressionOtypeConstructors = rule993 _lhsItypeConstructors
         _leftExpressionOvalueConstructors = rule994 _lhsIvalueConstructors
         _leftExpressionOwarnings = rule995 _lhsIwarnings
         _operatorOallTypeConstructors = rule996 _lhsIallTypeConstructors
         _operatorOallValueConstructors = rule997 _lhsIallValueConstructors
         _operatorOclassEnvironment = rule998 _lhsIclassEnvironment
         _operatorOcollectScopeInfos = rule999 _leftExpressionIcollectScopeInfos
         _operatorOcounter = rule1000 _leftExpressionIcounter
         _operatorOkindErrors = rule1001 _leftExpressionIkindErrors
         _operatorOmiscerrors = rule1002 _leftExpressionImiscerrors
         _operatorOnamesInScope = rule1003 _lhsInamesInScope
         _operatorOoptions = rule1004 _lhsIoptions
         _operatorOorderedTypeSynonyms = rule1005 _lhsIorderedTypeSynonyms
         _operatorOtypeConstructors = rule1006 _lhsItypeConstructors
         _operatorOvalueConstructors = rule1007 _lhsIvalueConstructors
         _operatorOwarnings = rule1008 _leftExpressionIwarnings
         _rightExpressionOallTypeConstructors = rule1009 _lhsIallTypeConstructors
         _rightExpressionOallValueConstructors = rule1010 _lhsIallValueConstructors
         _rightExpressionOclassEnvironment = rule1011 _lhsIclassEnvironment
         _rightExpressionOcollectScopeInfos = rule1012 _operatorIcollectScopeInfos
         _rightExpressionOcounter = rule1013 _operatorIcounter
         _rightExpressionOkindErrors = rule1014 _operatorIkindErrors
         _rightExpressionOmiscerrors = rule1015 _operatorImiscerrors
         _rightExpressionOnamesInScope = rule1016 _lhsInamesInScope
         _rightExpressionOoptions = rule1017 _lhsIoptions
         _rightExpressionOorderedTypeSynonyms = rule1018 _lhsIorderedTypeSynonyms
         _rightExpressionOtypeConstructors = rule1019 _lhsItypeConstructors
         _rightExpressionOvalueConstructors = rule1020 _lhsIvalueConstructors
         _rightExpressionOwarnings = rule1021 _operatorIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule974 #-}
   rule974 = \ ((_leftExpressionIcollectInstances) :: [(Name, Instance)]) ((_operatorIcollectInstances) :: [(Name, Instance)]) ((_rightExpressionIcollectInstances) :: [(Name, Instance)]) ->
     _leftExpressionIcollectInstances  ++  _operatorIcollectInstances  ++  _rightExpressionIcollectInstances
   {-# INLINE rule975 #-}
   rule975 = \ ((_leftExpressionIunboundNames) :: Names) ((_operatorIunboundNames) :: Names) ((_rightExpressionIunboundNames) :: Names) ->
     _leftExpressionIunboundNames ++ _operatorIunboundNames ++ _rightExpressionIunboundNames
   {-# INLINE rule976 #-}
   rule976 = \ ((_leftExpressionIself) :: MaybeExpression) ((_operatorIself) :: Expression) ((_rangeIself) :: Range) ((_rightExpressionIself) :: MaybeExpression) ->
     Expression_InfixApplication _rangeIself _leftExpressionIself _operatorIself _rightExpressionIself
   {-# INLINE rule977 #-}
   rule977 = \ _self ->
     _self
   {-# INLINE rule978 #-}
   rule978 = \ ((_rightExpressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _rightExpressionIcollectScopeInfos
   {-# INLINE rule979 #-}
   rule979 = \ ((_rightExpressionIcounter) :: Int) ->
     _rightExpressionIcounter
   {-# INLINE rule980 #-}
   rule980 = \ ((_rightExpressionIkindErrors) :: [Error]) ->
     _rightExpressionIkindErrors
   {-# INLINE rule981 #-}
   rule981 = \ ((_rightExpressionImiscerrors) :: [Error]) ->
     _rightExpressionImiscerrors
   {-# INLINE rule982 #-}
   rule982 = \ ((_rightExpressionIwarnings) :: [Warning]) ->
     _rightExpressionIwarnings
   {-# INLINE rule983 #-}
   rule983 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule984 #-}
   rule984 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule985 #-}
   rule985 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule986 #-}
   rule986 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule987 #-}
   rule987 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule988 #-}
   rule988 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule989 #-}
   rule989 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule990 #-}
   rule990 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule991 #-}
   rule991 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule992 #-}
   rule992 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule993 #-}
   rule993 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule994 #-}
   rule994 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule995 #-}
   rule995 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule996 #-}
   rule996 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule997 #-}
   rule997 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule998 #-}
   rule998 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule999 #-}
   rule999 = \ ((_leftExpressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _leftExpressionIcollectScopeInfos
   {-# INLINE rule1000 #-}
   rule1000 = \ ((_leftExpressionIcounter) :: Int) ->
     _leftExpressionIcounter
   {-# INLINE rule1001 #-}
   rule1001 = \ ((_leftExpressionIkindErrors) :: [Error]) ->
     _leftExpressionIkindErrors
   {-# INLINE rule1002 #-}
   rule1002 = \ ((_leftExpressionImiscerrors) :: [Error]) ->
     _leftExpressionImiscerrors
   {-# INLINE rule1003 #-}
   rule1003 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1004 #-}
   rule1004 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1005 #-}
   rule1005 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1006 #-}
   rule1006 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1007 #-}
   rule1007 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1008 #-}
   rule1008 = \ ((_leftExpressionIwarnings) :: [Warning]) ->
     _leftExpressionIwarnings
   {-# INLINE rule1009 #-}
   rule1009 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1010 #-}
   rule1010 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1011 #-}
   rule1011 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1012 #-}
   rule1012 = \ ((_operatorIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _operatorIcollectScopeInfos
   {-# INLINE rule1013 #-}
   rule1013 = \ ((_operatorIcounter) :: Int) ->
     _operatorIcounter
   {-# INLINE rule1014 #-}
   rule1014 = \ ((_operatorIkindErrors) :: [Error]) ->
     _operatorIkindErrors
   {-# INLINE rule1015 #-}
   rule1015 = \ ((_operatorImiscerrors) :: [Error]) ->
     _operatorImiscerrors
   {-# INLINE rule1016 #-}
   rule1016 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1017 #-}
   rule1017 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1018 #-}
   rule1018 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1019 #-}
   rule1019 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1020 #-}
   rule1020 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1021 #-}
   rule1021 = \ ((_operatorIwarnings) :: [Warning]) ->
     _operatorIwarnings
{-# NOINLINE sem_Expression_If #-}
sem_Expression_If :: T_Range  -> T_Expression  -> T_Expression  -> T_Expression  -> T_Expression 
sem_Expression_If arg_range_ arg_guardExpression_ arg_thenExpression_ arg_elseExpression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardExpressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_guardExpression_))
         _thenExpressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_thenExpression_))
         _elseExpressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_elseExpression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _guardExpressionIcollectInstances _guardExpressionIcollectScopeInfos _guardExpressionIcounter _guardExpressionIkindErrors _guardExpressionImiscerrors _guardExpressionIself _guardExpressionIunboundNames _guardExpressionIwarnings) = inv_Expression_s41 _guardExpressionX41 (T_Expression_vIn40 _guardExpressionOallTypeConstructors _guardExpressionOallValueConstructors _guardExpressionOclassEnvironment _guardExpressionOcollectScopeInfos _guardExpressionOcounter _guardExpressionOkindErrors _guardExpressionOmiscerrors _guardExpressionOnamesInScope _guardExpressionOoptions _guardExpressionOorderedTypeSynonyms _guardExpressionOtypeConstructors _guardExpressionOvalueConstructors _guardExpressionOwarnings)
         (T_Expression_vOut40 _thenExpressionIcollectInstances _thenExpressionIcollectScopeInfos _thenExpressionIcounter _thenExpressionIkindErrors _thenExpressionImiscerrors _thenExpressionIself _thenExpressionIunboundNames _thenExpressionIwarnings) = inv_Expression_s41 _thenExpressionX41 (T_Expression_vIn40 _thenExpressionOallTypeConstructors _thenExpressionOallValueConstructors _thenExpressionOclassEnvironment _thenExpressionOcollectScopeInfos _thenExpressionOcounter _thenExpressionOkindErrors _thenExpressionOmiscerrors _thenExpressionOnamesInScope _thenExpressionOoptions _thenExpressionOorderedTypeSynonyms _thenExpressionOtypeConstructors _thenExpressionOvalueConstructors _thenExpressionOwarnings)
         (T_Expression_vOut40 _elseExpressionIcollectInstances _elseExpressionIcollectScopeInfos _elseExpressionIcounter _elseExpressionIkindErrors _elseExpressionImiscerrors _elseExpressionIself _elseExpressionIunboundNames _elseExpressionIwarnings) = inv_Expression_s41 _elseExpressionX41 (T_Expression_vIn40 _elseExpressionOallTypeConstructors _elseExpressionOallValueConstructors _elseExpressionOclassEnvironment _elseExpressionOcollectScopeInfos _elseExpressionOcounter _elseExpressionOkindErrors _elseExpressionOmiscerrors _elseExpressionOnamesInScope _elseExpressionOoptions _elseExpressionOorderedTypeSynonyms _elseExpressionOtypeConstructors _elseExpressionOvalueConstructors _elseExpressionOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1022 _elseExpressionIcollectInstances _guardExpressionIcollectInstances _thenExpressionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1023 _elseExpressionIunboundNames _guardExpressionIunboundNames _thenExpressionIunboundNames
         _self = rule1024 _elseExpressionIself _guardExpressionIself _rangeIself _thenExpressionIself
         _lhsOself :: Expression
         _lhsOself = rule1025 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1026 _elseExpressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1027 _elseExpressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1028 _elseExpressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1029 _elseExpressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1030 _elseExpressionIwarnings
         _guardExpressionOallTypeConstructors = rule1031 _lhsIallTypeConstructors
         _guardExpressionOallValueConstructors = rule1032 _lhsIallValueConstructors
         _guardExpressionOclassEnvironment = rule1033 _lhsIclassEnvironment
         _guardExpressionOcollectScopeInfos = rule1034 _lhsIcollectScopeInfos
         _guardExpressionOcounter = rule1035 _lhsIcounter
         _guardExpressionOkindErrors = rule1036 _lhsIkindErrors
         _guardExpressionOmiscerrors = rule1037 _lhsImiscerrors
         _guardExpressionOnamesInScope = rule1038 _lhsInamesInScope
         _guardExpressionOoptions = rule1039 _lhsIoptions
         _guardExpressionOorderedTypeSynonyms = rule1040 _lhsIorderedTypeSynonyms
         _guardExpressionOtypeConstructors = rule1041 _lhsItypeConstructors
         _guardExpressionOvalueConstructors = rule1042 _lhsIvalueConstructors
         _guardExpressionOwarnings = rule1043 _lhsIwarnings
         _thenExpressionOallTypeConstructors = rule1044 _lhsIallTypeConstructors
         _thenExpressionOallValueConstructors = rule1045 _lhsIallValueConstructors
         _thenExpressionOclassEnvironment = rule1046 _lhsIclassEnvironment
         _thenExpressionOcollectScopeInfos = rule1047 _guardExpressionIcollectScopeInfos
         _thenExpressionOcounter = rule1048 _guardExpressionIcounter
         _thenExpressionOkindErrors = rule1049 _guardExpressionIkindErrors
         _thenExpressionOmiscerrors = rule1050 _guardExpressionImiscerrors
         _thenExpressionOnamesInScope = rule1051 _lhsInamesInScope
         _thenExpressionOoptions = rule1052 _lhsIoptions
         _thenExpressionOorderedTypeSynonyms = rule1053 _lhsIorderedTypeSynonyms
         _thenExpressionOtypeConstructors = rule1054 _lhsItypeConstructors
         _thenExpressionOvalueConstructors = rule1055 _lhsIvalueConstructors
         _thenExpressionOwarnings = rule1056 _guardExpressionIwarnings
         _elseExpressionOallTypeConstructors = rule1057 _lhsIallTypeConstructors
         _elseExpressionOallValueConstructors = rule1058 _lhsIallValueConstructors
         _elseExpressionOclassEnvironment = rule1059 _lhsIclassEnvironment
         _elseExpressionOcollectScopeInfos = rule1060 _thenExpressionIcollectScopeInfos
         _elseExpressionOcounter = rule1061 _thenExpressionIcounter
         _elseExpressionOkindErrors = rule1062 _thenExpressionIkindErrors
         _elseExpressionOmiscerrors = rule1063 _thenExpressionImiscerrors
         _elseExpressionOnamesInScope = rule1064 _lhsInamesInScope
         _elseExpressionOoptions = rule1065 _lhsIoptions
         _elseExpressionOorderedTypeSynonyms = rule1066 _lhsIorderedTypeSynonyms
         _elseExpressionOtypeConstructors = rule1067 _lhsItypeConstructors
         _elseExpressionOvalueConstructors = rule1068 _lhsIvalueConstructors
         _elseExpressionOwarnings = rule1069 _thenExpressionIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1022 #-}
   rule1022 = \ ((_elseExpressionIcollectInstances) :: [(Name, Instance)]) ((_guardExpressionIcollectInstances) :: [(Name, Instance)]) ((_thenExpressionIcollectInstances) :: [(Name, Instance)]) ->
     _guardExpressionIcollectInstances  ++  _thenExpressionIcollectInstances  ++  _elseExpressionIcollectInstances
   {-# INLINE rule1023 #-}
   rule1023 = \ ((_elseExpressionIunboundNames) :: Names) ((_guardExpressionIunboundNames) :: Names) ((_thenExpressionIunboundNames) :: Names) ->
     _guardExpressionIunboundNames ++ _thenExpressionIunboundNames ++ _elseExpressionIunboundNames
   {-# INLINE rule1024 #-}
   rule1024 = \ ((_elseExpressionIself) :: Expression) ((_guardExpressionIself) :: Expression) ((_rangeIself) :: Range) ((_thenExpressionIself) :: Expression) ->
     Expression_If _rangeIself _guardExpressionIself _thenExpressionIself _elseExpressionIself
   {-# INLINE rule1025 #-}
   rule1025 = \ _self ->
     _self
   {-# INLINE rule1026 #-}
   rule1026 = \ ((_elseExpressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _elseExpressionIcollectScopeInfos
   {-# INLINE rule1027 #-}
   rule1027 = \ ((_elseExpressionIcounter) :: Int) ->
     _elseExpressionIcounter
   {-# INLINE rule1028 #-}
   rule1028 = \ ((_elseExpressionIkindErrors) :: [Error]) ->
     _elseExpressionIkindErrors
   {-# INLINE rule1029 #-}
   rule1029 = \ ((_elseExpressionImiscerrors) :: [Error]) ->
     _elseExpressionImiscerrors
   {-# INLINE rule1030 #-}
   rule1030 = \ ((_elseExpressionIwarnings) :: [Warning]) ->
     _elseExpressionIwarnings
   {-# INLINE rule1031 #-}
   rule1031 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1032 #-}
   rule1032 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1033 #-}
   rule1033 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1034 #-}
   rule1034 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1035 #-}
   rule1035 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1036 #-}
   rule1036 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1037 #-}
   rule1037 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1038 #-}
   rule1038 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1039 #-}
   rule1039 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1040 #-}
   rule1040 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1041 #-}
   rule1041 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1042 #-}
   rule1042 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1043 #-}
   rule1043 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1044 #-}
   rule1044 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1045 #-}
   rule1045 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1046 #-}
   rule1046 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1047 #-}
   rule1047 = \ ((_guardExpressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _guardExpressionIcollectScopeInfos
   {-# INLINE rule1048 #-}
   rule1048 = \ ((_guardExpressionIcounter) :: Int) ->
     _guardExpressionIcounter
   {-# INLINE rule1049 #-}
   rule1049 = \ ((_guardExpressionIkindErrors) :: [Error]) ->
     _guardExpressionIkindErrors
   {-# INLINE rule1050 #-}
   rule1050 = \ ((_guardExpressionImiscerrors) :: [Error]) ->
     _guardExpressionImiscerrors
   {-# INLINE rule1051 #-}
   rule1051 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1052 #-}
   rule1052 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1053 #-}
   rule1053 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1054 #-}
   rule1054 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1055 #-}
   rule1055 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1056 #-}
   rule1056 = \ ((_guardExpressionIwarnings) :: [Warning]) ->
     _guardExpressionIwarnings
   {-# INLINE rule1057 #-}
   rule1057 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1058 #-}
   rule1058 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1059 #-}
   rule1059 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1060 #-}
   rule1060 = \ ((_thenExpressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _thenExpressionIcollectScopeInfos
   {-# INLINE rule1061 #-}
   rule1061 = \ ((_thenExpressionIcounter) :: Int) ->
     _thenExpressionIcounter
   {-# INLINE rule1062 #-}
   rule1062 = \ ((_thenExpressionIkindErrors) :: [Error]) ->
     _thenExpressionIkindErrors
   {-# INLINE rule1063 #-}
   rule1063 = \ ((_thenExpressionImiscerrors) :: [Error]) ->
     _thenExpressionImiscerrors
   {-# INLINE rule1064 #-}
   rule1064 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1065 #-}
   rule1065 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1066 #-}
   rule1066 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1067 #-}
   rule1067 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1068 #-}
   rule1068 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1069 #-}
   rule1069 = \ ((_thenExpressionIwarnings) :: [Warning]) ->
     _thenExpressionIwarnings
{-# NOINLINE sem_Expression_Lambda #-}
sem_Expression_Lambda :: T_Range  -> T_Patterns  -> T_Expression  -> T_Expression 
sem_Expression_Lambda arg_range_ arg_patterns_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Patterns_vOut121 _patternsIcollectScopeInfos _patternsIcounter _patternsImiscerrors _patternsInumberOfPatterns _patternsIpatVarNames _patternsIself _patternsIunboundNames _patternsIwarnings) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOcounter _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings)
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         (_namesInScope,_unboundNames,_scopeInfo) = rule1070 _expressionIunboundNames _lhsInamesInScope _patternsIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1071 _unboundNames
         _patternsOlhsPattern = rule1072  ()
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1073 _expressionIcollectScopeInfos _scopeInfo
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1074 _expressionIcollectInstances
         _self = rule1075 _expressionIself _patternsIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule1076 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule1077 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1078 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1079 _expressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1080 _expressionIwarnings
         _patternsOallTypeConstructors = rule1081 _lhsIallTypeConstructors
         _patternsOallValueConstructors = rule1082 _lhsIallValueConstructors
         _patternsOcollectScopeInfos = rule1083 _lhsIcollectScopeInfos
         _patternsOcounter = rule1084 _lhsIcounter
         _patternsOmiscerrors = rule1085 _lhsImiscerrors
         _patternsOnamesInScope = rule1086 _namesInScope
         _patternsOtypeConstructors = rule1087 _lhsItypeConstructors
         _patternsOvalueConstructors = rule1088 _lhsIvalueConstructors
         _patternsOwarnings = rule1089 _lhsIwarnings
         _expressionOallTypeConstructors = rule1090 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule1091 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule1092 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule1093 _patternsIcollectScopeInfos
         _expressionOcounter = rule1094 _patternsIcounter
         _expressionOkindErrors = rule1095 _lhsIkindErrors
         _expressionOmiscerrors = rule1096 _patternsImiscerrors
         _expressionOnamesInScope = rule1097 _namesInScope
         _expressionOoptions = rule1098 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule1099 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule1100 _lhsItypeConstructors
         _expressionOvalueConstructors = rule1101 _lhsIvalueConstructors
         _expressionOwarnings = rule1102 _patternsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1070 #-}
   rule1070 = \ ((_expressionIunboundNames) :: Names) ((_lhsInamesInScope) :: Names) ((_patternsIpatVarNames) :: Names) ->
                                                                        changeOfScope _patternsIpatVarNames _expressionIunboundNames _lhsInamesInScope
   {-# INLINE rule1071 #-}
   rule1071 = \ _unboundNames ->
                                             _unboundNames
   {-# INLINE rule1072 #-}
   rule1072 = \  (_ :: ()) ->
                                                                False
   {-# INLINE rule1073 #-}
   rule1073 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) _scopeInfo ->
                                                 (_scopeInfo, Variable)   : _expressionIcollectScopeInfos
   {-# INLINE rule1074 #-}
   rule1074 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule1075 #-}
   rule1075 = \ ((_expressionIself) :: Expression) ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     Expression_Lambda _rangeIself _patternsIself _expressionIself
   {-# INLINE rule1076 #-}
   rule1076 = \ _self ->
     _self
   {-# INLINE rule1077 #-}
   rule1077 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule1078 #-}
   rule1078 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule1079 #-}
   rule1079 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule1080 #-}
   rule1080 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule1081 #-}
   rule1081 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1082 #-}
   rule1082 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1083 #-}
   rule1083 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1084 #-}
   rule1084 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1085 #-}
   rule1085 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1086 #-}
   rule1086 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule1087 #-}
   rule1087 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1088 #-}
   rule1088 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1089 #-}
   rule1089 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1090 #-}
   rule1090 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1091 #-}
   rule1091 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1092 #-}
   rule1092 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1093 #-}
   rule1093 = \ ((_patternsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternsIcollectScopeInfos
   {-# INLINE rule1094 #-}
   rule1094 = \ ((_patternsIcounter) :: Int) ->
     _patternsIcounter
   {-# INLINE rule1095 #-}
   rule1095 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1096 #-}
   rule1096 = \ ((_patternsImiscerrors) :: [Error]) ->
     _patternsImiscerrors
   {-# INLINE rule1097 #-}
   rule1097 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule1098 #-}
   rule1098 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1099 #-}
   rule1099 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1100 #-}
   rule1100 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1101 #-}
   rule1101 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1102 #-}
   rule1102 = \ ((_patternsIwarnings) :: [Warning]) ->
     _patternsIwarnings
{-# NOINLINE sem_Expression_Case #-}
sem_Expression_Case :: T_Range  -> T_Expression  -> T_Alternatives  -> T_Expression 
sem_Expression_Case arg_range_ arg_expression_ arg_alternatives_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _alternativesX5 = Control.Monad.Identity.runIdentity (attach_T_Alternatives (arg_alternatives_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         (T_Alternatives_vOut4 _alternativesIcollectInstances _alternativesIcollectScopeInfos _alternativesIcounter _alternativesIkindErrors _alternativesImiscerrors _alternativesIself _alternativesIunboundNames _alternativesIwarnings) = inv_Alternatives_s5 _alternativesX5 (T_Alternatives_vIn4 _alternativesOallTypeConstructors _alternativesOallValueConstructors _alternativesOclassEnvironment _alternativesOcollectScopeInfos _alternativesOcounter _alternativesOkindErrors _alternativesOmiscerrors _alternativesOnamesInScope _alternativesOoptions _alternativesOorderedTypeSynonyms _alternativesOtypeConstructors _alternativesOvalueConstructors _alternativesOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1103 _alternativesIcollectInstances _expressionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1104 _alternativesIunboundNames _expressionIunboundNames
         _self = rule1105 _alternativesIself _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule1106 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1107 _alternativesIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1108 _alternativesIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1109 _alternativesIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1110 _alternativesImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1111 _alternativesIwarnings
         _expressionOallTypeConstructors = rule1112 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule1113 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule1114 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule1115 _lhsIcollectScopeInfos
         _expressionOcounter = rule1116 _lhsIcounter
         _expressionOkindErrors = rule1117 _lhsIkindErrors
         _expressionOmiscerrors = rule1118 _lhsImiscerrors
         _expressionOnamesInScope = rule1119 _lhsInamesInScope
         _expressionOoptions = rule1120 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule1121 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule1122 _lhsItypeConstructors
         _expressionOvalueConstructors = rule1123 _lhsIvalueConstructors
         _expressionOwarnings = rule1124 _lhsIwarnings
         _alternativesOallTypeConstructors = rule1125 _lhsIallTypeConstructors
         _alternativesOallValueConstructors = rule1126 _lhsIallValueConstructors
         _alternativesOclassEnvironment = rule1127 _lhsIclassEnvironment
         _alternativesOcollectScopeInfos = rule1128 _expressionIcollectScopeInfos
         _alternativesOcounter = rule1129 _expressionIcounter
         _alternativesOkindErrors = rule1130 _expressionIkindErrors
         _alternativesOmiscerrors = rule1131 _expressionImiscerrors
         _alternativesOnamesInScope = rule1132 _lhsInamesInScope
         _alternativesOoptions = rule1133 _lhsIoptions
         _alternativesOorderedTypeSynonyms = rule1134 _lhsIorderedTypeSynonyms
         _alternativesOtypeConstructors = rule1135 _lhsItypeConstructors
         _alternativesOvalueConstructors = rule1136 _lhsIvalueConstructors
         _alternativesOwarnings = rule1137 _expressionIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1103 #-}
   rule1103 = \ ((_alternativesIcollectInstances) :: [(Name, Instance)]) ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances  ++  _alternativesIcollectInstances
   {-# INLINE rule1104 #-}
   rule1104 = \ ((_alternativesIunboundNames) :: Names) ((_expressionIunboundNames) :: Names) ->
     _expressionIunboundNames ++ _alternativesIunboundNames
   {-# INLINE rule1105 #-}
   rule1105 = \ ((_alternativesIself) :: Alternatives) ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_Case _rangeIself _expressionIself _alternativesIself
   {-# INLINE rule1106 #-}
   rule1106 = \ _self ->
     _self
   {-# INLINE rule1107 #-}
   rule1107 = \ ((_alternativesIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _alternativesIcollectScopeInfos
   {-# INLINE rule1108 #-}
   rule1108 = \ ((_alternativesIcounter) :: Int) ->
     _alternativesIcounter
   {-# INLINE rule1109 #-}
   rule1109 = \ ((_alternativesIkindErrors) :: [Error]) ->
     _alternativesIkindErrors
   {-# INLINE rule1110 #-}
   rule1110 = \ ((_alternativesImiscerrors) :: [Error]) ->
     _alternativesImiscerrors
   {-# INLINE rule1111 #-}
   rule1111 = \ ((_alternativesIwarnings) :: [Warning]) ->
     _alternativesIwarnings
   {-# INLINE rule1112 #-}
   rule1112 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1113 #-}
   rule1113 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1114 #-}
   rule1114 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1115 #-}
   rule1115 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1116 #-}
   rule1116 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1117 #-}
   rule1117 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1118 #-}
   rule1118 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1119 #-}
   rule1119 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1120 #-}
   rule1120 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1121 #-}
   rule1121 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1122 #-}
   rule1122 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1123 #-}
   rule1123 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1124 #-}
   rule1124 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1125 #-}
   rule1125 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1126 #-}
   rule1126 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1127 #-}
   rule1127 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1128 #-}
   rule1128 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule1129 #-}
   rule1129 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule1130 #-}
   rule1130 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule1131 #-}
   rule1131 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule1132 #-}
   rule1132 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1133 #-}
   rule1133 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1134 #-}
   rule1134 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1135 #-}
   rule1135 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1136 #-}
   rule1136 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1137 #-}
   rule1137 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
{-# NOINLINE sem_Expression_Let #-}
sem_Expression_Let :: T_Range  -> T_Declarations  -> T_Expression  -> T_Expression 
sem_Expression_Let arg_range_ arg_declarations_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Declarations_vOut31 _declarationsIcollectInstances _declarationsIcollectScopeInfos _declarationsIcollectTypeConstructors _declarationsIcollectTypeSynonyms _declarationsIcollectValueConstructors _declarationsIcounter _declarationsIdeclVarNames _declarationsIkindErrors _declarationsImiscerrors _declarationsIoperatorFixities _declarationsIpreviousWasAlsoFB _declarationsIrestrictedNames _declarationsIself _declarationsIsuspiciousFBs _declarationsItypeSignatures _declarationsIunboundNames _declarationsIwarnings) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 _declarationsOallTypeConstructors _declarationsOallValueConstructors _declarationsOclassEnvironment _declarationsOcollectScopeInfos _declarationsOcollectTypeConstructors _declarationsOcollectTypeSynonyms _declarationsOcollectValueConstructors _declarationsOcounter _declarationsOkindErrors _declarationsOmiscerrors _declarationsOnamesInScope _declarationsOoperatorFixities _declarationsOoptions _declarationsOorderedTypeSynonyms _declarationsOpreviousWasAlsoFB _declarationsOsuspiciousFBs _declarationsOtypeConstructors _declarationsOtypeSignatures _declarationsOvalueConstructors _declarationsOwarnings)
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         _declarationsOtypeSignatures = rule1138  ()
         (_namesInScope,_unboundNames,_scopeInfo) = rule1139 _declarationsIdeclVarNames _declarationsIunboundNames _expressionIunboundNames _lhsInamesInScope
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1140 _unboundNames
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1141 _expressionIwarnings _suspiciousErrors
         _declarationsOpreviousWasAlsoFB = rule1142  ()
         _declarationsOsuspiciousFBs = rule1143  ()
         _suspiciousErrors = rule1144 _declarationsIsuspiciousFBs _declarationsItypeSignatures
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1145 _expressionImiscerrors _typeSignatureErrors
         (_,_doubles) = rule1146 _declarationsItypeSignatures
         _typeSignatureErrors = rule1147 _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
         (_collectTypeConstructors,_collectValueConstructors,_collectTypeSynonyms,_collectConstructorEnv,_derivedFunctions,_operatorFixities) = rule1148  ()
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1149 _expressionIcollectScopeInfos _scopeInfo
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1150 _declarationsIcollectInstances _expressionIcollectInstances
         _self = rule1151 _declarationsIself _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule1152 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule1153 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1154 _expressionIkindErrors
         _declarationsOallTypeConstructors = rule1155 _lhsIallTypeConstructors
         _declarationsOallValueConstructors = rule1156 _lhsIallValueConstructors
         _declarationsOclassEnvironment = rule1157 _lhsIclassEnvironment
         _declarationsOcollectScopeInfos = rule1158 _lhsIcollectScopeInfos
         _declarationsOcollectTypeConstructors = rule1159 _collectTypeConstructors
         _declarationsOcollectTypeSynonyms = rule1160 _collectTypeSynonyms
         _declarationsOcollectValueConstructors = rule1161 _collectValueConstructors
         _declarationsOcounter = rule1162 _lhsIcounter
         _declarationsOkindErrors = rule1163 _lhsIkindErrors
         _declarationsOmiscerrors = rule1164 _lhsImiscerrors
         _declarationsOnamesInScope = rule1165 _namesInScope
         _declarationsOoperatorFixities = rule1166 _operatorFixities
         _declarationsOoptions = rule1167 _lhsIoptions
         _declarationsOorderedTypeSynonyms = rule1168 _lhsIorderedTypeSynonyms
         _declarationsOtypeConstructors = rule1169 _lhsItypeConstructors
         _declarationsOvalueConstructors = rule1170 _lhsIvalueConstructors
         _declarationsOwarnings = rule1171 _lhsIwarnings
         _expressionOallTypeConstructors = rule1172 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule1173 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule1174 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule1175 _declarationsIcollectScopeInfos
         _expressionOcounter = rule1176 _declarationsIcounter
         _expressionOkindErrors = rule1177 _declarationsIkindErrors
         _expressionOmiscerrors = rule1178 _declarationsImiscerrors
         _expressionOnamesInScope = rule1179 _namesInScope
         _expressionOoptions = rule1180 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule1181 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule1182 _lhsItypeConstructors
         _expressionOvalueConstructors = rule1183 _lhsIvalueConstructors
         _expressionOwarnings = rule1184 _declarationsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1138 #-}
   rule1138 = \  (_ :: ()) ->
                                                                  []
   {-# INLINE rule1139 #-}
   rule1139 = \ ((_declarationsIdeclVarNames) :: Names) ((_declarationsIunboundNames) :: Names) ((_expressionIunboundNames) :: Names) ((_lhsInamesInScope) :: Names) ->
                                                             changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _expressionIunboundNames) _lhsInamesInScope
   {-# INLINE rule1140 #-}
   rule1140 = \ _unboundNames ->
                                  _unboundNames
   {-# INLINE rule1141 #-}
   rule1141 = \ ((_expressionIwarnings) :: [Warning]) _suspiciousErrors ->
                                  _expressionIwarnings ++
                                  _suspiciousErrors
   {-# INLINE rule1142 #-}
   rule1142 = \  (_ :: ()) ->
                                                Nothing
   {-# INLINE rule1143 #-}
   rule1143 = \  (_ :: ()) ->
                                                []
   {-# INLINE rule1144 #-}
   rule1144 = \ ((_declarationsIsuspiciousFBs) :: [(Name,Name)]) ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                                findSimilarFunctionBindings _declarationsItypeSignatures _declarationsIsuspiciousFBs
   {-# INLINE rule1145 #-}
   rule1145 = \ ((_expressionImiscerrors) :: [Error]) _typeSignatureErrors ->
                                      _typeSignatureErrors ++ _expressionImiscerrors
   {-# INLINE rule1146 #-}
   rule1146 = \ ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                       uniqueAppearance (map fst _declarationsItypeSignatures)
   {-# INLINE rule1147 #-}
   rule1147 = \ ((_declarationsIdeclVarNames) :: Names) ((_declarationsIrestrictedNames) :: Names) ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                               checkTypeSignatures _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
   {-# INLINE rule1148 #-}
   rule1148 = \  (_ :: ()) ->
                                                                                                                                                   internalError "PartialSyntax.ag" "n/a" "toplevel Expression"
   {-# INLINE rule1149 #-}
   rule1149 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) _scopeInfo ->
                                                 (_scopeInfo, Definition) : _expressionIcollectScopeInfos
   {-# INLINE rule1150 #-}
   rule1150 = \ ((_declarationsIcollectInstances) :: [(Name, Instance)]) ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _declarationsIcollectInstances  ++  _expressionIcollectInstances
   {-# INLINE rule1151 #-}
   rule1151 = \ ((_declarationsIself) :: Declarations) ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_Let _rangeIself _declarationsIself _expressionIself
   {-# INLINE rule1152 #-}
   rule1152 = \ _self ->
     _self
   {-# INLINE rule1153 #-}
   rule1153 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule1154 #-}
   rule1154 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule1155 #-}
   rule1155 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1156 #-}
   rule1156 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1157 #-}
   rule1157 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1158 #-}
   rule1158 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1159 #-}
   rule1159 = \ _collectTypeConstructors ->
     _collectTypeConstructors
   {-# INLINE rule1160 #-}
   rule1160 = \ _collectTypeSynonyms ->
     _collectTypeSynonyms
   {-# INLINE rule1161 #-}
   rule1161 = \ _collectValueConstructors ->
     _collectValueConstructors
   {-# INLINE rule1162 #-}
   rule1162 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1163 #-}
   rule1163 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1164 #-}
   rule1164 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1165 #-}
   rule1165 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule1166 #-}
   rule1166 = \ _operatorFixities ->
     _operatorFixities
   {-# INLINE rule1167 #-}
   rule1167 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1168 #-}
   rule1168 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1169 #-}
   rule1169 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1170 #-}
   rule1170 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1171 #-}
   rule1171 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1172 #-}
   rule1172 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1173 #-}
   rule1173 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1174 #-}
   rule1174 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1175 #-}
   rule1175 = \ ((_declarationsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _declarationsIcollectScopeInfos
   {-# INLINE rule1176 #-}
   rule1176 = \ ((_declarationsIcounter) :: Int) ->
     _declarationsIcounter
   {-# INLINE rule1177 #-}
   rule1177 = \ ((_declarationsIkindErrors) :: [Error]) ->
     _declarationsIkindErrors
   {-# INLINE rule1178 #-}
   rule1178 = \ ((_declarationsImiscerrors) :: [Error]) ->
     _declarationsImiscerrors
   {-# INLINE rule1179 #-}
   rule1179 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule1180 #-}
   rule1180 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1181 #-}
   rule1181 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1182 #-}
   rule1182 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1183 #-}
   rule1183 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1184 #-}
   rule1184 = \ ((_declarationsIwarnings) :: [Warning]) ->
     _declarationsIwarnings
{-# NOINLINE sem_Expression_Do #-}
sem_Expression_Do :: T_Range  -> T_Statements  -> T_Expression 
sem_Expression_Do arg_range_ arg_statements_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _statementsX158 = Control.Monad.Identity.runIdentity (attach_T_Statements (arg_statements_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Statements_vOut157 _statementsIcollectInstances _statementsIcollectScopeInfos _statementsIcounter _statementsIkindErrors _statementsIlastStatementIsExpr _statementsImiscerrors _statementsInamesInScope _statementsIself _statementsIunboundNames _statementsIwarnings) = inv_Statements_s158 _statementsX158 (T_Statements_vIn157 _statementsOallTypeConstructors _statementsOallValueConstructors _statementsOclassEnvironment _statementsOcollectScopeInfos _statementsOcounter _statementsOkindErrors _statementsOlastStatementIsExpr _statementsOmiscerrors _statementsOnamesInScope _statementsOoptions _statementsOorderedTypeSynonyms _statementsOtypeConstructors _statementsOunboundNames _statementsOvalueConstructors _statementsOwarnings)
         _statementsOunboundNames = rule1185  ()
         _statementsOlastStatementIsExpr = rule1186  ()
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1187 _lastStatementErrors _statementsImiscerrors
         _lastStatementErrors = rule1188 _statementsIlastStatementIsExpr _statementsIself
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1189 _statementsIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1190 _statementsIunboundNames
         _self = rule1191 _rangeIself _statementsIself
         _lhsOself :: Expression
         _lhsOself = rule1192 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1193 _statementsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1194 _statementsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1195 _statementsIkindErrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1196 _statementsIwarnings
         _statementsOallTypeConstructors = rule1197 _lhsIallTypeConstructors
         _statementsOallValueConstructors = rule1198 _lhsIallValueConstructors
         _statementsOclassEnvironment = rule1199 _lhsIclassEnvironment
         _statementsOcollectScopeInfos = rule1200 _lhsIcollectScopeInfos
         _statementsOcounter = rule1201 _lhsIcounter
         _statementsOkindErrors = rule1202 _lhsIkindErrors
         _statementsOmiscerrors = rule1203 _lhsImiscerrors
         _statementsOnamesInScope = rule1204 _lhsInamesInScope
         _statementsOoptions = rule1205 _lhsIoptions
         _statementsOorderedTypeSynonyms = rule1206 _lhsIorderedTypeSynonyms
         _statementsOtypeConstructors = rule1207 _lhsItypeConstructors
         _statementsOvalueConstructors = rule1208 _lhsIvalueConstructors
         _statementsOwarnings = rule1209 _lhsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1185 #-}
   rule1185 = \  (_ :: ()) ->
                                      []
   {-# INLINE rule1186 #-}
   rule1186 = \  (_ :: ()) ->
                                               False
   {-# INLINE rule1187 #-}
   rule1187 = \ _lastStatementErrors ((_statementsImiscerrors) :: [Error]) ->
                                      _lastStatementErrors ++ _statementsImiscerrors
   {-# INLINE rule1188 #-}
   rule1188 = \ ((_statementsIlastStatementIsExpr) :: Bool) ((_statementsIself) :: Statements) ->
                                               if _statementsIlastStatementIsExpr
                                                 then []
                                                 else let range = getStatementRange (last _statementsIself)
                                                      in [ LastStatementNotExpr range ]
   {-# INLINE rule1189 #-}
   rule1189 = \ ((_statementsIcollectInstances) :: [(Name, Instance)]) ->
     _statementsIcollectInstances
   {-# INLINE rule1190 #-}
   rule1190 = \ ((_statementsIunboundNames) :: Names) ->
     _statementsIunboundNames
   {-# INLINE rule1191 #-}
   rule1191 = \ ((_rangeIself) :: Range) ((_statementsIself) :: Statements) ->
     Expression_Do _rangeIself _statementsIself
   {-# INLINE rule1192 #-}
   rule1192 = \ _self ->
     _self
   {-# INLINE rule1193 #-}
   rule1193 = \ ((_statementsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _statementsIcollectScopeInfos
   {-# INLINE rule1194 #-}
   rule1194 = \ ((_statementsIcounter) :: Int) ->
     _statementsIcounter
   {-# INLINE rule1195 #-}
   rule1195 = \ ((_statementsIkindErrors) :: [Error]) ->
     _statementsIkindErrors
   {-# INLINE rule1196 #-}
   rule1196 = \ ((_statementsIwarnings) :: [Warning]) ->
     _statementsIwarnings
   {-# INLINE rule1197 #-}
   rule1197 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1198 #-}
   rule1198 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1199 #-}
   rule1199 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1200 #-}
   rule1200 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1201 #-}
   rule1201 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1202 #-}
   rule1202 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1203 #-}
   rule1203 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1204 #-}
   rule1204 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1205 #-}
   rule1205 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1206 #-}
   rule1206 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1207 #-}
   rule1207 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1208 #-}
   rule1208 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1209 #-}
   rule1209 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Expression_List #-}
sem_Expression_List :: T_Range  -> T_Expressions  -> T_Expression 
sem_Expression_List arg_range_ arg_expressions_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionsX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_expressions_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expressions_vOut43 _expressionsIcollectInstances _expressionsIcollectScopeInfos _expressionsIcounter _expressionsIkindErrors _expressionsImiscerrors _expressionsIself _expressionsIunboundNames _expressionsIwarnings) = inv_Expressions_s44 _expressionsX44 (T_Expressions_vIn43 _expressionsOallTypeConstructors _expressionsOallValueConstructors _expressionsOclassEnvironment _expressionsOcollectScopeInfos _expressionsOcounter _expressionsOkindErrors _expressionsOmiscerrors _expressionsOnamesInScope _expressionsOoptions _expressionsOorderedTypeSynonyms _expressionsOtypeConstructors _expressionsOvalueConstructors _expressionsOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1210 _expressionsIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1211 _expressionsIunboundNames
         _self = rule1212 _expressionsIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule1213 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1214 _expressionsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1215 _expressionsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1216 _expressionsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1217 _expressionsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1218 _expressionsIwarnings
         _expressionsOallTypeConstructors = rule1219 _lhsIallTypeConstructors
         _expressionsOallValueConstructors = rule1220 _lhsIallValueConstructors
         _expressionsOclassEnvironment = rule1221 _lhsIclassEnvironment
         _expressionsOcollectScopeInfos = rule1222 _lhsIcollectScopeInfos
         _expressionsOcounter = rule1223 _lhsIcounter
         _expressionsOkindErrors = rule1224 _lhsIkindErrors
         _expressionsOmiscerrors = rule1225 _lhsImiscerrors
         _expressionsOnamesInScope = rule1226 _lhsInamesInScope
         _expressionsOoptions = rule1227 _lhsIoptions
         _expressionsOorderedTypeSynonyms = rule1228 _lhsIorderedTypeSynonyms
         _expressionsOtypeConstructors = rule1229 _lhsItypeConstructors
         _expressionsOvalueConstructors = rule1230 _lhsIvalueConstructors
         _expressionsOwarnings = rule1231 _lhsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1210 #-}
   rule1210 = \ ((_expressionsIcollectInstances) :: [(Name, Instance)]) ->
     _expressionsIcollectInstances
   {-# INLINE rule1211 #-}
   rule1211 = \ ((_expressionsIunboundNames) :: Names) ->
     _expressionsIunboundNames
   {-# INLINE rule1212 #-}
   rule1212 = \ ((_expressionsIself) :: Expressions) ((_rangeIself) :: Range) ->
     Expression_List _rangeIself _expressionsIself
   {-# INLINE rule1213 #-}
   rule1213 = \ _self ->
     _self
   {-# INLINE rule1214 #-}
   rule1214 = \ ((_expressionsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionsIcollectScopeInfos
   {-# INLINE rule1215 #-}
   rule1215 = \ ((_expressionsIcounter) :: Int) ->
     _expressionsIcounter
   {-# INLINE rule1216 #-}
   rule1216 = \ ((_expressionsIkindErrors) :: [Error]) ->
     _expressionsIkindErrors
   {-# INLINE rule1217 #-}
   rule1217 = \ ((_expressionsImiscerrors) :: [Error]) ->
     _expressionsImiscerrors
   {-# INLINE rule1218 #-}
   rule1218 = \ ((_expressionsIwarnings) :: [Warning]) ->
     _expressionsIwarnings
   {-# INLINE rule1219 #-}
   rule1219 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1220 #-}
   rule1220 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1221 #-}
   rule1221 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1222 #-}
   rule1222 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1223 #-}
   rule1223 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1224 #-}
   rule1224 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1225 #-}
   rule1225 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1226 #-}
   rule1226 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1227 #-}
   rule1227 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1228 #-}
   rule1228 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1229 #-}
   rule1229 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1230 #-}
   rule1230 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1231 #-}
   rule1231 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Expression_Tuple #-}
sem_Expression_Tuple :: T_Range  -> T_Expressions  -> T_Expression 
sem_Expression_Tuple arg_range_ arg_expressions_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionsX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_expressions_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expressions_vOut43 _expressionsIcollectInstances _expressionsIcollectScopeInfos _expressionsIcounter _expressionsIkindErrors _expressionsImiscerrors _expressionsIself _expressionsIunboundNames _expressionsIwarnings) = inv_Expressions_s44 _expressionsX44 (T_Expressions_vIn43 _expressionsOallTypeConstructors _expressionsOallValueConstructors _expressionsOclassEnvironment _expressionsOcollectScopeInfos _expressionsOcounter _expressionsOkindErrors _expressionsOmiscerrors _expressionsOnamesInScope _expressionsOoptions _expressionsOorderedTypeSynonyms _expressionsOtypeConstructors _expressionsOvalueConstructors _expressionsOwarnings)
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1232 _expressionsImiscerrors _tupleTooBigErrors
         _tupleTooBigErrors = rule1233 _expressionsIself _rangeIself
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1234 _expressionsIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1235 _expressionsIunboundNames
         _self = rule1236 _expressionsIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule1237 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1238 _expressionsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1239 _expressionsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1240 _expressionsIkindErrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1241 _expressionsIwarnings
         _expressionsOallTypeConstructors = rule1242 _lhsIallTypeConstructors
         _expressionsOallValueConstructors = rule1243 _lhsIallValueConstructors
         _expressionsOclassEnvironment = rule1244 _lhsIclassEnvironment
         _expressionsOcollectScopeInfos = rule1245 _lhsIcollectScopeInfos
         _expressionsOcounter = rule1246 _lhsIcounter
         _expressionsOkindErrors = rule1247 _lhsIkindErrors
         _expressionsOmiscerrors = rule1248 _lhsImiscerrors
         _expressionsOnamesInScope = rule1249 _lhsInamesInScope
         _expressionsOoptions = rule1250 _lhsIoptions
         _expressionsOorderedTypeSynonyms = rule1251 _lhsIorderedTypeSynonyms
         _expressionsOtypeConstructors = rule1252 _lhsItypeConstructors
         _expressionsOvalueConstructors = rule1253 _lhsIvalueConstructors
         _expressionsOwarnings = rule1254 _lhsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1232 #-}
   rule1232 = \ ((_expressionsImiscerrors) :: [Error]) _tupleTooBigErrors ->
                                      _tupleTooBigErrors ++ _expressionsImiscerrors
   {-# INLINE rule1233 #-}
   rule1233 = \ ((_expressionsIself) :: Expressions) ((_rangeIself) :: Range) ->
                          [ TupleTooBig _rangeIself
                          | length _expressionsIself > 10
                          ]
   {-# INLINE rule1234 #-}
   rule1234 = \ ((_expressionsIcollectInstances) :: [(Name, Instance)]) ->
     _expressionsIcollectInstances
   {-# INLINE rule1235 #-}
   rule1235 = \ ((_expressionsIunboundNames) :: Names) ->
     _expressionsIunboundNames
   {-# INLINE rule1236 #-}
   rule1236 = \ ((_expressionsIself) :: Expressions) ((_rangeIself) :: Range) ->
     Expression_Tuple _rangeIself _expressionsIself
   {-# INLINE rule1237 #-}
   rule1237 = \ _self ->
     _self
   {-# INLINE rule1238 #-}
   rule1238 = \ ((_expressionsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionsIcollectScopeInfos
   {-# INLINE rule1239 #-}
   rule1239 = \ ((_expressionsIcounter) :: Int) ->
     _expressionsIcounter
   {-# INLINE rule1240 #-}
   rule1240 = \ ((_expressionsIkindErrors) :: [Error]) ->
     _expressionsIkindErrors
   {-# INLINE rule1241 #-}
   rule1241 = \ ((_expressionsIwarnings) :: [Warning]) ->
     _expressionsIwarnings
   {-# INLINE rule1242 #-}
   rule1242 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1243 #-}
   rule1243 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1244 #-}
   rule1244 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1245 #-}
   rule1245 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1246 #-}
   rule1246 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1247 #-}
   rule1247 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1248 #-}
   rule1248 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1249 #-}
   rule1249 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1250 #-}
   rule1250 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1251 #-}
   rule1251 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1252 #-}
   rule1252 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1253 #-}
   rule1253 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1254 #-}
   rule1254 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Expression_Comprehension #-}
sem_Expression_Comprehension :: T_Range  -> T_Expression  -> T_Qualifiers  -> T_Expression 
sem_Expression_Comprehension arg_range_ arg_expression_ arg_qualifiers_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _qualifiersX131 = Control.Monad.Identity.runIdentity (attach_T_Qualifiers (arg_qualifiers_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         (T_Qualifiers_vOut130 _qualifiersIcollectInstances _qualifiersIcollectScopeInfos _qualifiersIcounter _qualifiersIkindErrors _qualifiersImiscerrors _qualifiersInamesInScope _qualifiersIself _qualifiersIunboundNames _qualifiersIwarnings) = inv_Qualifiers_s131 _qualifiersX131 (T_Qualifiers_vIn130 _qualifiersOallTypeConstructors _qualifiersOallValueConstructors _qualifiersOclassEnvironment _qualifiersOcollectScopeInfos _qualifiersOcounter _qualifiersOkindErrors _qualifiersOmiscerrors _qualifiersOnamesInScope _qualifiersOoptions _qualifiersOorderedTypeSynonyms _qualifiersOtypeConstructors _qualifiersOunboundNames _qualifiersOvalueConstructors _qualifiersOwarnings)
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1255 _qualifiersIunboundNames
         _expressionOnamesInScope = rule1256 _qualifiersInamesInScope
         _qualifiersOnamesInScope = rule1257 _lhsInamesInScope
         _qualifiersOunboundNames = rule1258 _expressionIunboundNames
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1259 _expressionIcollectInstances _qualifiersIcollectInstances
         _self = rule1260 _expressionIself _qualifiersIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule1261 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1262 _qualifiersIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1263 _qualifiersIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1264 _qualifiersIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1265 _qualifiersImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1266 _qualifiersIwarnings
         _expressionOallTypeConstructors = rule1267 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule1268 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule1269 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule1270 _lhsIcollectScopeInfos
         _expressionOcounter = rule1271 _lhsIcounter
         _expressionOkindErrors = rule1272 _lhsIkindErrors
         _expressionOmiscerrors = rule1273 _lhsImiscerrors
         _expressionOoptions = rule1274 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule1275 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule1276 _lhsItypeConstructors
         _expressionOvalueConstructors = rule1277 _lhsIvalueConstructors
         _expressionOwarnings = rule1278 _lhsIwarnings
         _qualifiersOallTypeConstructors = rule1279 _lhsIallTypeConstructors
         _qualifiersOallValueConstructors = rule1280 _lhsIallValueConstructors
         _qualifiersOclassEnvironment = rule1281 _lhsIclassEnvironment
         _qualifiersOcollectScopeInfos = rule1282 _expressionIcollectScopeInfos
         _qualifiersOcounter = rule1283 _expressionIcounter
         _qualifiersOkindErrors = rule1284 _expressionIkindErrors
         _qualifiersOmiscerrors = rule1285 _expressionImiscerrors
         _qualifiersOoptions = rule1286 _lhsIoptions
         _qualifiersOorderedTypeSynonyms = rule1287 _lhsIorderedTypeSynonyms
         _qualifiersOtypeConstructors = rule1288 _lhsItypeConstructors
         _qualifiersOvalueConstructors = rule1289 _lhsIvalueConstructors
         _qualifiersOwarnings = rule1290 _expressionIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1255 #-}
   rule1255 = \ ((_qualifiersIunboundNames) :: Names) ->
                                                   _qualifiersIunboundNames
   {-# INLINE rule1256 #-}
   rule1256 = \ ((_qualifiersInamesInScope) :: Names) ->
                                                   _qualifiersInamesInScope
   {-# INLINE rule1257 #-}
   rule1257 = \ ((_lhsInamesInScope) :: Names) ->
                                                   _lhsInamesInScope
   {-# INLINE rule1258 #-}
   rule1258 = \ ((_expressionIunboundNames) :: Names) ->
                                                   _expressionIunboundNames
   {-# INLINE rule1259 #-}
   rule1259 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ((_qualifiersIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances  ++  _qualifiersIcollectInstances
   {-# INLINE rule1260 #-}
   rule1260 = \ ((_expressionIself) :: Expression) ((_qualifiersIself) :: Qualifiers) ((_rangeIself) :: Range) ->
     Expression_Comprehension _rangeIself _expressionIself _qualifiersIself
   {-# INLINE rule1261 #-}
   rule1261 = \ _self ->
     _self
   {-# INLINE rule1262 #-}
   rule1262 = \ ((_qualifiersIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _qualifiersIcollectScopeInfos
   {-# INLINE rule1263 #-}
   rule1263 = \ ((_qualifiersIcounter) :: Int) ->
     _qualifiersIcounter
   {-# INLINE rule1264 #-}
   rule1264 = \ ((_qualifiersIkindErrors) :: [Error]) ->
     _qualifiersIkindErrors
   {-# INLINE rule1265 #-}
   rule1265 = \ ((_qualifiersImiscerrors) :: [Error]) ->
     _qualifiersImiscerrors
   {-# INLINE rule1266 #-}
   rule1266 = \ ((_qualifiersIwarnings) :: [Warning]) ->
     _qualifiersIwarnings
   {-# INLINE rule1267 #-}
   rule1267 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1268 #-}
   rule1268 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1269 #-}
   rule1269 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1270 #-}
   rule1270 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1271 #-}
   rule1271 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1272 #-}
   rule1272 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1273 #-}
   rule1273 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1274 #-}
   rule1274 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1275 #-}
   rule1275 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1276 #-}
   rule1276 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1277 #-}
   rule1277 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1278 #-}
   rule1278 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1279 #-}
   rule1279 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1280 #-}
   rule1280 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1281 #-}
   rule1281 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1282 #-}
   rule1282 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule1283 #-}
   rule1283 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule1284 #-}
   rule1284 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule1285 #-}
   rule1285 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule1286 #-}
   rule1286 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1287 #-}
   rule1287 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1288 #-}
   rule1288 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1289 #-}
   rule1289 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1290 #-}
   rule1290 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
{-# NOINLINE sem_Expression_Typed #-}
sem_Expression_Typed :: T_Range  -> T_Expression  -> T_Type  -> T_Expression 
sem_Expression_Typed arg_range_ arg_expression_ arg_type_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         (T_Type_vOut163 _typeIcontextRange _typeImiscerrors _typeIself _typeItypevariables _typeIwarnings) = inv_Type_s164 _typeX164 (T_Type_vIn163 _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings)
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1291 _expressionIkindErrors _newErrors
         _newErrors = rule1292 _lhsIallValueConstructors _lhsInamesInScope _lhsItypeConstructors _typeIself
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1293 _expressionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1294 _expressionIunboundNames
         _self = rule1295 _expressionIself _rangeIself _typeIself
         _lhsOself :: Expression
         _lhsOself = rule1296 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1297 _expressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1298 _expressionIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1299 _typeImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1300 _typeIwarnings
         _expressionOallTypeConstructors = rule1301 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule1302 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule1303 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule1304 _lhsIcollectScopeInfos
         _expressionOcounter = rule1305 _lhsIcounter
         _expressionOkindErrors = rule1306 _lhsIkindErrors
         _expressionOmiscerrors = rule1307 _lhsImiscerrors
         _expressionOnamesInScope = rule1308 _lhsInamesInScope
         _expressionOoptions = rule1309 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule1310 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule1311 _lhsItypeConstructors
         _expressionOvalueConstructors = rule1312 _lhsIvalueConstructors
         _expressionOwarnings = rule1313 _lhsIwarnings
         _typeOallTypeConstructors = rule1314 _lhsIallTypeConstructors
         _typeOmiscerrors = rule1315 _expressionImiscerrors
         _typeOoptions = rule1316 _lhsIoptions
         _typeOtypeConstructors = rule1317 _lhsItypeConstructors
         _typeOwarnings = rule1318 _expressionIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1291 #-}
   rule1291 = \ ((_expressionIkindErrors) :: [Error]) _newErrors ->
                                         _newErrors ++ _expressionIkindErrors
   {-# INLINE rule1292 #-}
   rule1292 = \ ((_lhsIallValueConstructors) :: Names) ((_lhsInamesInScope) :: Names) ((_lhsItypeConstructors) :: M.Map Name Int) ((_typeIself) :: Type) ->
                                         checkType _lhsItypeConstructors (_lhsInamesInScope ++ _lhsIallValueConstructors) _typeIself
   {-# INLINE rule1293 #-}
   rule1293 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule1294 #-}
   rule1294 = \ ((_expressionIunboundNames) :: Names) ->
     _expressionIunboundNames
   {-# INLINE rule1295 #-}
   rule1295 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ((_typeIself) :: Type) ->
     Expression_Typed _rangeIself _expressionIself _typeIself
   {-# INLINE rule1296 #-}
   rule1296 = \ _self ->
     _self
   {-# INLINE rule1297 #-}
   rule1297 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule1298 #-}
   rule1298 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule1299 #-}
   rule1299 = \ ((_typeImiscerrors) :: [Error]) ->
     _typeImiscerrors
   {-# INLINE rule1300 #-}
   rule1300 = \ ((_typeIwarnings) :: [Warning]) ->
     _typeIwarnings
   {-# INLINE rule1301 #-}
   rule1301 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1302 #-}
   rule1302 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1303 #-}
   rule1303 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1304 #-}
   rule1304 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1305 #-}
   rule1305 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1306 #-}
   rule1306 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1307 #-}
   rule1307 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1308 #-}
   rule1308 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1309 #-}
   rule1309 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1310 #-}
   rule1310 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1311 #-}
   rule1311 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1312 #-}
   rule1312 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1313 #-}
   rule1313 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1314 #-}
   rule1314 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1315 #-}
   rule1315 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule1316 #-}
   rule1316 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1317 #-}
   rule1317 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1318 #-}
   rule1318 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
{-# NOINLINE sem_Expression_RecordConstruction #-}
sem_Expression_RecordConstruction :: T_Range  -> T_Name  -> T_RecordExpressionBindings  -> T_Expression 
sem_Expression_RecordConstruction arg_range_ arg_name_ arg_recordExpressionBindings_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _recordExpressionBindingsX140 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBindings (arg_recordExpressionBindings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_RecordExpressionBindings_vOut139 _recordExpressionBindingsIcollectInstances _recordExpressionBindingsIcollectScopeInfos _recordExpressionBindingsIcounter _recordExpressionBindingsIself _recordExpressionBindingsIunboundNames) = inv_RecordExpressionBindings_s140 _recordExpressionBindingsX140 (T_RecordExpressionBindings_vIn139 _recordExpressionBindingsOclassEnvironment _recordExpressionBindingsOcollectScopeInfos _recordExpressionBindingsOcounter _recordExpressionBindingsOnamesInScope _recordExpressionBindingsOoptions _recordExpressionBindingsOorderedTypeSynonyms)
         (_assumptions,_constraints,_beta) = rule1319  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1320 _recordExpressionBindingsIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1321 _recordExpressionBindingsIunboundNames
         _self = rule1322 _nameIself _rangeIself _recordExpressionBindingsIself
         _lhsOself :: Expression
         _lhsOself = rule1323 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1324 _recordExpressionBindingsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1325 _recordExpressionBindingsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1326 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1327 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1328 _lhsIwarnings
         _recordExpressionBindingsOclassEnvironment = rule1329 _lhsIclassEnvironment
         _recordExpressionBindingsOcollectScopeInfos = rule1330 _lhsIcollectScopeInfos
         _recordExpressionBindingsOcounter = rule1331 _lhsIcounter
         _recordExpressionBindingsOnamesInScope = rule1332 _lhsInamesInScope
         _recordExpressionBindingsOoptions = rule1333 _lhsIoptions
         _recordExpressionBindingsOorderedTypeSynonyms = rule1334 _lhsIorderedTypeSynonyms
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1319 #-}
   rule1319 = \  (_ :: ()) ->
                                                                 internalError "PartialSyntax.ag" "n/a" "Expression.RecordConstruction"
   {-# INLINE rule1320 #-}
   rule1320 = \ ((_recordExpressionBindingsIcollectInstances) :: [(Name, Instance)]) ->
     _recordExpressionBindingsIcollectInstances
   {-# INLINE rule1321 #-}
   rule1321 = \ ((_recordExpressionBindingsIunboundNames) :: Names) ->
     _recordExpressionBindingsIunboundNames
   {-# INLINE rule1322 #-}
   rule1322 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ((_recordExpressionBindingsIself) :: RecordExpressionBindings) ->
     Expression_RecordConstruction _rangeIself _nameIself _recordExpressionBindingsIself
   {-# INLINE rule1323 #-}
   rule1323 = \ _self ->
     _self
   {-# INLINE rule1324 #-}
   rule1324 = \ ((_recordExpressionBindingsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _recordExpressionBindingsIcollectScopeInfos
   {-# INLINE rule1325 #-}
   rule1325 = \ ((_recordExpressionBindingsIcounter) :: Int) ->
     _recordExpressionBindingsIcounter
   {-# INLINE rule1326 #-}
   rule1326 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1327 #-}
   rule1327 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1328 #-}
   rule1328 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1329 #-}
   rule1329 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1330 #-}
   rule1330 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1331 #-}
   rule1331 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1332 #-}
   rule1332 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1333 #-}
   rule1333 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1334 #-}
   rule1334 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
{-# NOINLINE sem_Expression_RecordUpdate #-}
sem_Expression_RecordUpdate :: T_Range  -> T_Expression  -> T_RecordExpressionBindings  -> T_Expression 
sem_Expression_RecordUpdate arg_range_ arg_expression_ arg_recordExpressionBindings_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _recordExpressionBindingsX140 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBindings (arg_recordExpressionBindings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         (T_RecordExpressionBindings_vOut139 _recordExpressionBindingsIcollectInstances _recordExpressionBindingsIcollectScopeInfos _recordExpressionBindingsIcounter _recordExpressionBindingsIself _recordExpressionBindingsIunboundNames) = inv_RecordExpressionBindings_s140 _recordExpressionBindingsX140 (T_RecordExpressionBindings_vIn139 _recordExpressionBindingsOclassEnvironment _recordExpressionBindingsOcollectScopeInfos _recordExpressionBindingsOcounter _recordExpressionBindingsOnamesInScope _recordExpressionBindingsOoptions _recordExpressionBindingsOorderedTypeSynonyms)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1335 _expressionIcollectInstances _recordExpressionBindingsIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1336 _expressionIunboundNames _recordExpressionBindingsIunboundNames
         _self = rule1337 _expressionIself _rangeIself _recordExpressionBindingsIself
         _lhsOself :: Expression
         _lhsOself = rule1338 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1339 _recordExpressionBindingsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1340 _recordExpressionBindingsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1341 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1342 _expressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1343 _expressionIwarnings
         _expressionOallTypeConstructors = rule1344 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule1345 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule1346 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule1347 _lhsIcollectScopeInfos
         _expressionOcounter = rule1348 _lhsIcounter
         _expressionOkindErrors = rule1349 _lhsIkindErrors
         _expressionOmiscerrors = rule1350 _lhsImiscerrors
         _expressionOnamesInScope = rule1351 _lhsInamesInScope
         _expressionOoptions = rule1352 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule1353 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule1354 _lhsItypeConstructors
         _expressionOvalueConstructors = rule1355 _lhsIvalueConstructors
         _expressionOwarnings = rule1356 _lhsIwarnings
         _recordExpressionBindingsOclassEnvironment = rule1357 _lhsIclassEnvironment
         _recordExpressionBindingsOcollectScopeInfos = rule1358 _expressionIcollectScopeInfos
         _recordExpressionBindingsOcounter = rule1359 _expressionIcounter
         _recordExpressionBindingsOnamesInScope = rule1360 _lhsInamesInScope
         _recordExpressionBindingsOoptions = rule1361 _lhsIoptions
         _recordExpressionBindingsOorderedTypeSynonyms = rule1362 _lhsIorderedTypeSynonyms
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1335 #-}
   rule1335 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ((_recordExpressionBindingsIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances  ++  _recordExpressionBindingsIcollectInstances
   {-# INLINE rule1336 #-}
   rule1336 = \ ((_expressionIunboundNames) :: Names) ((_recordExpressionBindingsIunboundNames) :: Names) ->
     _expressionIunboundNames ++ _recordExpressionBindingsIunboundNames
   {-# INLINE rule1337 #-}
   rule1337 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ((_recordExpressionBindingsIself) :: RecordExpressionBindings) ->
     Expression_RecordUpdate _rangeIself _expressionIself _recordExpressionBindingsIself
   {-# INLINE rule1338 #-}
   rule1338 = \ _self ->
     _self
   {-# INLINE rule1339 #-}
   rule1339 = \ ((_recordExpressionBindingsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _recordExpressionBindingsIcollectScopeInfos
   {-# INLINE rule1340 #-}
   rule1340 = \ ((_recordExpressionBindingsIcounter) :: Int) ->
     _recordExpressionBindingsIcounter
   {-# INLINE rule1341 #-}
   rule1341 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule1342 #-}
   rule1342 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule1343 #-}
   rule1343 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule1344 #-}
   rule1344 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1345 #-}
   rule1345 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1346 #-}
   rule1346 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1347 #-}
   rule1347 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1348 #-}
   rule1348 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1349 #-}
   rule1349 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1350 #-}
   rule1350 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1351 #-}
   rule1351 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1352 #-}
   rule1352 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1353 #-}
   rule1353 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1354 #-}
   rule1354 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1355 #-}
   rule1355 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1356 #-}
   rule1356 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1357 #-}
   rule1357 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1358 #-}
   rule1358 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule1359 #-}
   rule1359 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule1360 #-}
   rule1360 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1361 #-}
   rule1361 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1362 #-}
   rule1362 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
{-# NOINLINE sem_Expression_Enum #-}
sem_Expression_Enum :: T_Range  -> T_Expression  -> T_MaybeExpression  -> T_MaybeExpression  -> T_Expression 
sem_Expression_Enum arg_range_ arg_from_ arg_then_ arg_to_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _fromX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_from_))
         _thenX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_then_))
         _toX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_to_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _fromIcollectInstances _fromIcollectScopeInfos _fromIcounter _fromIkindErrors _fromImiscerrors _fromIself _fromIunboundNames _fromIwarnings) = inv_Expression_s41 _fromX41 (T_Expression_vIn40 _fromOallTypeConstructors _fromOallValueConstructors _fromOclassEnvironment _fromOcollectScopeInfos _fromOcounter _fromOkindErrors _fromOmiscerrors _fromOnamesInScope _fromOoptions _fromOorderedTypeSynonyms _fromOtypeConstructors _fromOvalueConstructors _fromOwarnings)
         (T_MaybeExpression_vOut94 _thenIcollectInstances _thenIcollectScopeInfos _thenIcounter _thenIkindErrors _thenImiscerrors _thenIself _thenIunboundNames _thenIwarnings) = inv_MaybeExpression_s95 _thenX95 (T_MaybeExpression_vIn94 _thenOallTypeConstructors _thenOallValueConstructors _thenOclassEnvironment _thenOcollectScopeInfos _thenOcounter _thenOkindErrors _thenOmiscerrors _thenOnamesInScope _thenOoptions _thenOorderedTypeSynonyms _thenOtypeConstructors _thenOvalueConstructors _thenOwarnings)
         (T_MaybeExpression_vOut94 _toIcollectInstances _toIcollectScopeInfos _toIcounter _toIkindErrors _toImiscerrors _toIself _toIunboundNames _toIwarnings) = inv_MaybeExpression_s95 _toX95 (T_MaybeExpression_vIn94 _toOallTypeConstructors _toOallValueConstructors _toOclassEnvironment _toOcollectScopeInfos _toOcounter _toOkindErrors _toOmiscerrors _toOnamesInScope _toOoptions _toOorderedTypeSynonyms _toOtypeConstructors _toOvalueConstructors _toOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1363 _fromIcollectInstances _thenIcollectInstances _toIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1364 _fromIunboundNames _thenIunboundNames _toIunboundNames
         _self = rule1365 _fromIself _rangeIself _thenIself _toIself
         _lhsOself :: Expression
         _lhsOself = rule1366 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1367 _toIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1368 _toIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1369 _toIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1370 _toImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1371 _toIwarnings
         _fromOallTypeConstructors = rule1372 _lhsIallTypeConstructors
         _fromOallValueConstructors = rule1373 _lhsIallValueConstructors
         _fromOclassEnvironment = rule1374 _lhsIclassEnvironment
         _fromOcollectScopeInfos = rule1375 _lhsIcollectScopeInfos
         _fromOcounter = rule1376 _lhsIcounter
         _fromOkindErrors = rule1377 _lhsIkindErrors
         _fromOmiscerrors = rule1378 _lhsImiscerrors
         _fromOnamesInScope = rule1379 _lhsInamesInScope
         _fromOoptions = rule1380 _lhsIoptions
         _fromOorderedTypeSynonyms = rule1381 _lhsIorderedTypeSynonyms
         _fromOtypeConstructors = rule1382 _lhsItypeConstructors
         _fromOvalueConstructors = rule1383 _lhsIvalueConstructors
         _fromOwarnings = rule1384 _lhsIwarnings
         _thenOallTypeConstructors = rule1385 _lhsIallTypeConstructors
         _thenOallValueConstructors = rule1386 _lhsIallValueConstructors
         _thenOclassEnvironment = rule1387 _lhsIclassEnvironment
         _thenOcollectScopeInfos = rule1388 _fromIcollectScopeInfos
         _thenOcounter = rule1389 _fromIcounter
         _thenOkindErrors = rule1390 _fromIkindErrors
         _thenOmiscerrors = rule1391 _fromImiscerrors
         _thenOnamesInScope = rule1392 _lhsInamesInScope
         _thenOoptions = rule1393 _lhsIoptions
         _thenOorderedTypeSynonyms = rule1394 _lhsIorderedTypeSynonyms
         _thenOtypeConstructors = rule1395 _lhsItypeConstructors
         _thenOvalueConstructors = rule1396 _lhsIvalueConstructors
         _thenOwarnings = rule1397 _fromIwarnings
         _toOallTypeConstructors = rule1398 _lhsIallTypeConstructors
         _toOallValueConstructors = rule1399 _lhsIallValueConstructors
         _toOclassEnvironment = rule1400 _lhsIclassEnvironment
         _toOcollectScopeInfos = rule1401 _thenIcollectScopeInfos
         _toOcounter = rule1402 _thenIcounter
         _toOkindErrors = rule1403 _thenIkindErrors
         _toOmiscerrors = rule1404 _thenImiscerrors
         _toOnamesInScope = rule1405 _lhsInamesInScope
         _toOoptions = rule1406 _lhsIoptions
         _toOorderedTypeSynonyms = rule1407 _lhsIorderedTypeSynonyms
         _toOtypeConstructors = rule1408 _lhsItypeConstructors
         _toOvalueConstructors = rule1409 _lhsIvalueConstructors
         _toOwarnings = rule1410 _thenIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1363 #-}
   rule1363 = \ ((_fromIcollectInstances) :: [(Name, Instance)]) ((_thenIcollectInstances) :: [(Name, Instance)]) ((_toIcollectInstances) :: [(Name, Instance)]) ->
     _fromIcollectInstances  ++  _thenIcollectInstances  ++  _toIcollectInstances
   {-# INLINE rule1364 #-}
   rule1364 = \ ((_fromIunboundNames) :: Names) ((_thenIunboundNames) :: Names) ((_toIunboundNames) :: Names) ->
     _fromIunboundNames ++ _thenIunboundNames ++ _toIunboundNames
   {-# INLINE rule1365 #-}
   rule1365 = \ ((_fromIself) :: Expression) ((_rangeIself) :: Range) ((_thenIself) :: MaybeExpression) ((_toIself) :: MaybeExpression) ->
     Expression_Enum _rangeIself _fromIself _thenIself _toIself
   {-# INLINE rule1366 #-}
   rule1366 = \ _self ->
     _self
   {-# INLINE rule1367 #-}
   rule1367 = \ ((_toIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _toIcollectScopeInfos
   {-# INLINE rule1368 #-}
   rule1368 = \ ((_toIcounter) :: Int) ->
     _toIcounter
   {-# INLINE rule1369 #-}
   rule1369 = \ ((_toIkindErrors) :: [Error]) ->
     _toIkindErrors
   {-# INLINE rule1370 #-}
   rule1370 = \ ((_toImiscerrors) :: [Error]) ->
     _toImiscerrors
   {-# INLINE rule1371 #-}
   rule1371 = \ ((_toIwarnings) :: [Warning]) ->
     _toIwarnings
   {-# INLINE rule1372 #-}
   rule1372 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1373 #-}
   rule1373 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1374 #-}
   rule1374 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1375 #-}
   rule1375 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1376 #-}
   rule1376 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1377 #-}
   rule1377 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1378 #-}
   rule1378 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1379 #-}
   rule1379 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1380 #-}
   rule1380 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1381 #-}
   rule1381 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1382 #-}
   rule1382 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1383 #-}
   rule1383 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1384 #-}
   rule1384 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1385 #-}
   rule1385 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1386 #-}
   rule1386 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1387 #-}
   rule1387 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1388 #-}
   rule1388 = \ ((_fromIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _fromIcollectScopeInfos
   {-# INLINE rule1389 #-}
   rule1389 = \ ((_fromIcounter) :: Int) ->
     _fromIcounter
   {-# INLINE rule1390 #-}
   rule1390 = \ ((_fromIkindErrors) :: [Error]) ->
     _fromIkindErrors
   {-# INLINE rule1391 #-}
   rule1391 = \ ((_fromImiscerrors) :: [Error]) ->
     _fromImiscerrors
   {-# INLINE rule1392 #-}
   rule1392 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1393 #-}
   rule1393 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1394 #-}
   rule1394 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1395 #-}
   rule1395 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1396 #-}
   rule1396 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1397 #-}
   rule1397 = \ ((_fromIwarnings) :: [Warning]) ->
     _fromIwarnings
   {-# INLINE rule1398 #-}
   rule1398 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1399 #-}
   rule1399 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1400 #-}
   rule1400 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1401 #-}
   rule1401 = \ ((_thenIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _thenIcollectScopeInfos
   {-# INLINE rule1402 #-}
   rule1402 = \ ((_thenIcounter) :: Int) ->
     _thenIcounter
   {-# INLINE rule1403 #-}
   rule1403 = \ ((_thenIkindErrors) :: [Error]) ->
     _thenIkindErrors
   {-# INLINE rule1404 #-}
   rule1404 = \ ((_thenImiscerrors) :: [Error]) ->
     _thenImiscerrors
   {-# INLINE rule1405 #-}
   rule1405 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1406 #-}
   rule1406 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1407 #-}
   rule1407 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1408 #-}
   rule1408 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1409 #-}
   rule1409 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1410 #-}
   rule1410 = \ ((_thenIwarnings) :: [Warning]) ->
     _thenIwarnings
{-# NOINLINE sem_Expression_Negate #-}
sem_Expression_Negate :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_Negate arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1411 _expressionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1412 _expressionIunboundNames
         _self = rule1413 _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule1414 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1415 _expressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1416 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1417 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1418 _expressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1419 _expressionIwarnings
         _expressionOallTypeConstructors = rule1420 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule1421 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule1422 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule1423 _lhsIcollectScopeInfos
         _expressionOcounter = rule1424 _lhsIcounter
         _expressionOkindErrors = rule1425 _lhsIkindErrors
         _expressionOmiscerrors = rule1426 _lhsImiscerrors
         _expressionOnamesInScope = rule1427 _lhsInamesInScope
         _expressionOoptions = rule1428 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule1429 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule1430 _lhsItypeConstructors
         _expressionOvalueConstructors = rule1431 _lhsIvalueConstructors
         _expressionOwarnings = rule1432 _lhsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1411 #-}
   rule1411 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule1412 #-}
   rule1412 = \ ((_expressionIunboundNames) :: Names) ->
     _expressionIunboundNames
   {-# INLINE rule1413 #-}
   rule1413 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_Negate _rangeIself _expressionIself
   {-# INLINE rule1414 #-}
   rule1414 = \ _self ->
     _self
   {-# INLINE rule1415 #-}
   rule1415 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule1416 #-}
   rule1416 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule1417 #-}
   rule1417 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule1418 #-}
   rule1418 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule1419 #-}
   rule1419 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule1420 #-}
   rule1420 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1421 #-}
   rule1421 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1422 #-}
   rule1422 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1423 #-}
   rule1423 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1424 #-}
   rule1424 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1425 #-}
   rule1425 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1426 #-}
   rule1426 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1427 #-}
   rule1427 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1428 #-}
   rule1428 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1429 #-}
   rule1429 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1430 #-}
   rule1430 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1431 #-}
   rule1431 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1432 #-}
   rule1432 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Expression_NegateFloat #-}
sem_Expression_NegateFloat :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_NegateFloat arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1433 _expressionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1434 _expressionIunboundNames
         _self = rule1435 _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule1436 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1437 _expressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1438 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1439 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1440 _expressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1441 _expressionIwarnings
         _expressionOallTypeConstructors = rule1442 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule1443 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule1444 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule1445 _lhsIcollectScopeInfos
         _expressionOcounter = rule1446 _lhsIcounter
         _expressionOkindErrors = rule1447 _lhsIkindErrors
         _expressionOmiscerrors = rule1448 _lhsImiscerrors
         _expressionOnamesInScope = rule1449 _lhsInamesInScope
         _expressionOoptions = rule1450 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule1451 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule1452 _lhsItypeConstructors
         _expressionOvalueConstructors = rule1453 _lhsIvalueConstructors
         _expressionOwarnings = rule1454 _lhsIwarnings
         __result_ = T_Expression_vOut40 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule1433 #-}
   rule1433 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule1434 #-}
   rule1434 = \ ((_expressionIunboundNames) :: Names) ->
     _expressionIunboundNames
   {-# INLINE rule1435 #-}
   rule1435 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_NegateFloat _rangeIself _expressionIself
   {-# INLINE rule1436 #-}
   rule1436 = \ _self ->
     _self
   {-# INLINE rule1437 #-}
   rule1437 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule1438 #-}
   rule1438 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule1439 #-}
   rule1439 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule1440 #-}
   rule1440 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule1441 #-}
   rule1441 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule1442 #-}
   rule1442 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1443 #-}
   rule1443 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1444 #-}
   rule1444 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1445 #-}
   rule1445 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1446 #-}
   rule1446 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1447 #-}
   rule1447 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1448 #-}
   rule1448 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1449 #-}
   rule1449 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1450 #-}
   rule1450 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1451 #-}
   rule1451 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1452 #-}
   rule1452 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1453 #-}
   rule1453 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1454 #-}
   rule1454 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Expressions -------------------------------------------------
-- wrapper
data Inh_Expressions  = Inh_Expressions { allTypeConstructors_Inh_Expressions :: (Names), allValueConstructors_Inh_Expressions :: (Names), classEnvironment_Inh_Expressions :: (ClassEnvironment), collectScopeInfos_Inh_Expressions :: ([(ScopeInfo, Entity)]), counter_Inh_Expressions :: (Int), kindErrors_Inh_Expressions :: ([Error]), miscerrors_Inh_Expressions :: ([Error]), namesInScope_Inh_Expressions :: (Names), options_Inh_Expressions :: ([Option]), orderedTypeSynonyms_Inh_Expressions :: (OrderedTypeSynonyms), typeConstructors_Inh_Expressions :: (M.Map Name Int), valueConstructors_Inh_Expressions :: (M.Map Name TpScheme), warnings_Inh_Expressions :: ([Warning]) }
data Syn_Expressions  = Syn_Expressions { collectInstances_Syn_Expressions :: ([(Name, Instance)]), collectScopeInfos_Syn_Expressions :: ([(ScopeInfo, Entity)]), counter_Syn_Expressions :: (Int), kindErrors_Syn_Expressions :: ([Error]), miscerrors_Syn_Expressions :: ([Error]), self_Syn_Expressions :: (Expressions), unboundNames_Syn_Expressions :: (Names), warnings_Syn_Expressions :: ([Warning]) }
{-# INLINABLE wrap_Expressions #-}
wrap_Expressions :: T_Expressions  -> Inh_Expressions  -> (Syn_Expressions )
wrap_Expressions (T_Expressions act) (Inh_Expressions _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Expressions_vIn43 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_Expressions_vOut43 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_Expressions_s44 sem arg)
        return (Syn_Expressions _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Expressions #-}
sem_Expressions :: Expressions  -> T_Expressions 
sem_Expressions list = Prelude.foldr sem_Expressions_Cons sem_Expressions_Nil (Prelude.map sem_Expression list)

-- semantic domain
newtype T_Expressions  = T_Expressions {
                                       attach_T_Expressions :: Identity (T_Expressions_s44 )
                                       }
newtype T_Expressions_s44  = C_Expressions_s44 {
                                               inv_Expressions_s44 :: (T_Expressions_v43 )
                                               }
data T_Expressions_s45  = C_Expressions_s45
type T_Expressions_v43  = (T_Expressions_vIn43 ) -> (T_Expressions_vOut43 )
data T_Expressions_vIn43  = T_Expressions_vIn43 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_Expressions_vOut43  = T_Expressions_vOut43 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Expressions) (Names) ([Warning])
{-# NOINLINE sem_Expressions_Cons #-}
sem_Expressions_Cons :: T_Expression  -> T_Expressions  -> T_Expressions 
sem_Expressions_Cons arg_hd_ arg_tl_ = T_Expressions (return st44) where
   {-# NOINLINE st44 #-}
   st44 = let
      v43 :: T_Expressions_v43 
      v43 = \ (T_Expressions_vIn43 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _hdX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_hd_))
         _tlX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_tl_))
         (T_Expression_vOut40 _hdIcollectInstances _hdIcollectScopeInfos _hdIcounter _hdIkindErrors _hdImiscerrors _hdIself _hdIunboundNames _hdIwarnings) = inv_Expression_s41 _hdX41 (T_Expression_vIn40 _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOcounter _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings)
         (T_Expressions_vOut43 _tlIcollectInstances _tlIcollectScopeInfos _tlIcounter _tlIkindErrors _tlImiscerrors _tlIself _tlIunboundNames _tlIwarnings) = inv_Expressions_s44 _tlX44 (T_Expressions_vIn43 _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOcounter _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1455 _hdIcollectInstances _tlIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1456 _hdIunboundNames _tlIunboundNames
         _self = rule1457 _hdIself _tlIself
         _lhsOself :: Expressions
         _lhsOself = rule1458 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1459 _tlIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1460 _tlIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1461 _tlIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1462 _tlImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1463 _tlIwarnings
         _hdOallTypeConstructors = rule1464 _lhsIallTypeConstructors
         _hdOallValueConstructors = rule1465 _lhsIallValueConstructors
         _hdOclassEnvironment = rule1466 _lhsIclassEnvironment
         _hdOcollectScopeInfos = rule1467 _lhsIcollectScopeInfos
         _hdOcounter = rule1468 _lhsIcounter
         _hdOkindErrors = rule1469 _lhsIkindErrors
         _hdOmiscerrors = rule1470 _lhsImiscerrors
         _hdOnamesInScope = rule1471 _lhsInamesInScope
         _hdOoptions = rule1472 _lhsIoptions
         _hdOorderedTypeSynonyms = rule1473 _lhsIorderedTypeSynonyms
         _hdOtypeConstructors = rule1474 _lhsItypeConstructors
         _hdOvalueConstructors = rule1475 _lhsIvalueConstructors
         _hdOwarnings = rule1476 _lhsIwarnings
         _tlOallTypeConstructors = rule1477 _lhsIallTypeConstructors
         _tlOallValueConstructors = rule1478 _lhsIallValueConstructors
         _tlOclassEnvironment = rule1479 _lhsIclassEnvironment
         _tlOcollectScopeInfos = rule1480 _hdIcollectScopeInfos
         _tlOcounter = rule1481 _hdIcounter
         _tlOkindErrors = rule1482 _hdIkindErrors
         _tlOmiscerrors = rule1483 _hdImiscerrors
         _tlOnamesInScope = rule1484 _lhsInamesInScope
         _tlOoptions = rule1485 _lhsIoptions
         _tlOorderedTypeSynonyms = rule1486 _lhsIorderedTypeSynonyms
         _tlOtypeConstructors = rule1487 _lhsItypeConstructors
         _tlOvalueConstructors = rule1488 _lhsIvalueConstructors
         _tlOwarnings = rule1489 _hdIwarnings
         __result_ = T_Expressions_vOut43 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expressions_s44 v43
   {-# INLINE rule1455 #-}
   rule1455 = \ ((_hdIcollectInstances) :: [(Name, Instance)]) ((_tlIcollectInstances) :: [(Name, Instance)]) ->
     _hdIcollectInstances  ++  _tlIcollectInstances
   {-# INLINE rule1456 #-}
   rule1456 = \ ((_hdIunboundNames) :: Names) ((_tlIunboundNames) :: Names) ->
     _hdIunboundNames ++ _tlIunboundNames
   {-# INLINE rule1457 #-}
   rule1457 = \ ((_hdIself) :: Expression) ((_tlIself) :: Expressions) ->
     (:) _hdIself _tlIself
   {-# INLINE rule1458 #-}
   rule1458 = \ _self ->
     _self
   {-# INLINE rule1459 #-}
   rule1459 = \ ((_tlIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _tlIcollectScopeInfos
   {-# INLINE rule1460 #-}
   rule1460 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule1461 #-}
   rule1461 = \ ((_tlIkindErrors) :: [Error]) ->
     _tlIkindErrors
   {-# INLINE rule1462 #-}
   rule1462 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule1463 #-}
   rule1463 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule1464 #-}
   rule1464 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1465 #-}
   rule1465 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1466 #-}
   rule1466 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1467 #-}
   rule1467 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1468 #-}
   rule1468 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1469 #-}
   rule1469 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1470 #-}
   rule1470 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1471 #-}
   rule1471 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1472 #-}
   rule1472 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1473 #-}
   rule1473 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1474 #-}
   rule1474 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1475 #-}
   rule1475 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1476 #-}
   rule1476 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1477 #-}
   rule1477 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1478 #-}
   rule1478 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1479 #-}
   rule1479 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1480 #-}
   rule1480 = \ ((_hdIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _hdIcollectScopeInfos
   {-# INLINE rule1481 #-}
   rule1481 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule1482 #-}
   rule1482 = \ ((_hdIkindErrors) :: [Error]) ->
     _hdIkindErrors
   {-# INLINE rule1483 #-}
   rule1483 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule1484 #-}
   rule1484 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1485 #-}
   rule1485 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1486 #-}
   rule1486 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1487 #-}
   rule1487 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1488 #-}
   rule1488 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1489 #-}
   rule1489 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_Expressions_Nil #-}
sem_Expressions_Nil ::  T_Expressions 
sem_Expressions_Nil  = T_Expressions (return st44) where
   {-# NOINLINE st44 #-}
   st44 = let
      v43 :: T_Expressions_v43 
      v43 = \ (T_Expressions_vIn43 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1490  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1491  ()
         _self = rule1492  ()
         _lhsOself :: Expressions
         _lhsOself = rule1493 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1494 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1495 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1496 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1497 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1498 _lhsIwarnings
         __result_ = T_Expressions_vOut43 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Expressions_s44 v43
   {-# INLINE rule1490 #-}
   rule1490 = \  (_ :: ()) ->
     []
   {-# INLINE rule1491 #-}
   rule1491 = \  (_ :: ()) ->
     []
   {-# INLINE rule1492 #-}
   rule1492 = \  (_ :: ()) ->
     []
   {-# INLINE rule1493 #-}
   rule1493 = \ _self ->
     _self
   {-# INLINE rule1494 #-}
   rule1494 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1495 #-}
   rule1495 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1496 #-}
   rule1496 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1497 #-}
   rule1497 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1498 #-}
   rule1498 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- FieldDeclaration --------------------------------------------
-- wrapper
data Inh_FieldDeclaration  = Inh_FieldDeclaration { counter_Inh_FieldDeclaration :: (Int), miscerrors_Inh_FieldDeclaration :: ([Error]), namesInScope_Inh_FieldDeclaration :: (Names), options_Inh_FieldDeclaration :: ([Option]) }
data Syn_FieldDeclaration  = Syn_FieldDeclaration { counter_Syn_FieldDeclaration :: (Int), miscerrors_Syn_FieldDeclaration :: ([Error]), self_Syn_FieldDeclaration :: (FieldDeclaration), unboundNames_Syn_FieldDeclaration :: (Names) }
{-# INLINABLE wrap_FieldDeclaration #-}
wrap_FieldDeclaration :: T_FieldDeclaration  -> Inh_FieldDeclaration  -> (Syn_FieldDeclaration )
wrap_FieldDeclaration (T_FieldDeclaration act) (Inh_FieldDeclaration _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsIoptions) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_FieldDeclaration_vIn46 _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsIoptions
        (T_FieldDeclaration_vOut46 _lhsOcounter _lhsOmiscerrors _lhsOself _lhsOunboundNames) <- return (inv_FieldDeclaration_s47 sem arg)
        return (Syn_FieldDeclaration _lhsOcounter _lhsOmiscerrors _lhsOself _lhsOunboundNames)
   )

-- cata
{-# INLINE sem_FieldDeclaration #-}
sem_FieldDeclaration :: FieldDeclaration  -> T_FieldDeclaration 
sem_FieldDeclaration ( FieldDeclaration_FieldDeclaration range_ names_ type_ ) = sem_FieldDeclaration_FieldDeclaration ( sem_Range range_ ) ( sem_Names names_ ) ( sem_AnnotatedType type_ )

-- semantic domain
newtype T_FieldDeclaration  = T_FieldDeclaration {
                                                 attach_T_FieldDeclaration :: Identity (T_FieldDeclaration_s47 )
                                                 }
newtype T_FieldDeclaration_s47  = C_FieldDeclaration_s47 {
                                                         inv_FieldDeclaration_s47 :: (T_FieldDeclaration_v46 )
                                                         }
data T_FieldDeclaration_s48  = C_FieldDeclaration_s48
type T_FieldDeclaration_v46  = (T_FieldDeclaration_vIn46 ) -> (T_FieldDeclaration_vOut46 )
data T_FieldDeclaration_vIn46  = T_FieldDeclaration_vIn46 (Int) ([Error]) (Names) ([Option])
data T_FieldDeclaration_vOut46  = T_FieldDeclaration_vOut46 (Int) ([Error]) (FieldDeclaration) (Names)
{-# NOINLINE sem_FieldDeclaration_FieldDeclaration #-}
sem_FieldDeclaration_FieldDeclaration :: T_Range  -> T_Names  -> T_AnnotatedType  -> T_FieldDeclaration 
sem_FieldDeclaration_FieldDeclaration arg_range_ arg_names_ arg_type_ = T_FieldDeclaration (return st47) where
   {-# NOINLINE st47 #-}
   st47 = let
      v46 :: T_FieldDeclaration_v46 
      v46 = \ (T_FieldDeclaration_vIn46 _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsIoptions) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _namesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_names_))
         _typeX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _namesIself) = inv_Names_s116 _namesX116 (T_Names_vIn115 )
         (T_AnnotatedType_vOut7 _typeIcounter _typeIkindErrors _typeImiscerrors _typeIself _typeItype _typeItypevariables _typeIunboundNames _typeIwarnings) = inv_AnnotatedType_s8 _typeX8 (T_AnnotatedType_vIn7 _typeOallTypeConstructors _typeOallValueConstructors _typeOcounter _typeOkindErrors _typeOmiscerrors _typeOnamesInScope _typeOoptions _typeOtypeConstructors _typeOvalueConstructors _typeOwarnings)
         (_kindErrors,_tyconEnv,_constructorenv,_importEnvironment,_valueConstructors,_allValueConstructors,_typeConstructors,_allTypeConstructors,_warnings) = rule1499  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1500 _typeIunboundNames
         _self = rule1501 _namesIself _rangeIself _typeIself
         _lhsOself :: FieldDeclaration
         _lhsOself = rule1502 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule1503 _typeIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1504 _typeImiscerrors
         _typeOallTypeConstructors = rule1505 _allTypeConstructors
         _typeOallValueConstructors = rule1506 _allValueConstructors
         _typeOcounter = rule1507 _lhsIcounter
         _typeOkindErrors = rule1508 _kindErrors
         _typeOmiscerrors = rule1509 _lhsImiscerrors
         _typeOnamesInScope = rule1510 _lhsInamesInScope
         _typeOoptions = rule1511 _lhsIoptions
         _typeOtypeConstructors = rule1512 _typeConstructors
         _typeOvalueConstructors = rule1513 _valueConstructors
         _typeOwarnings = rule1514 _warnings
         __result_ = T_FieldDeclaration_vOut46 _lhsOcounter _lhsOmiscerrors _lhsOself _lhsOunboundNames
         in __result_ )
     in C_FieldDeclaration_s47 v46
   {-# INLINE rule1499 #-}
   rule1499 = \  (_ :: ()) ->
                                                                                                                                                                              internalError "PartialSyntax.ag" "n/a" "FieldDeclaration.FieldDeclaration"
   {-# INLINE rule1500 #-}
   rule1500 = \ ((_typeIunboundNames) :: Names) ->
     _typeIunboundNames
   {-# INLINE rule1501 #-}
   rule1501 = \ ((_namesIself) :: Names) ((_rangeIself) :: Range) ((_typeIself) :: AnnotatedType) ->
     FieldDeclaration_FieldDeclaration _rangeIself _namesIself _typeIself
   {-# INLINE rule1502 #-}
   rule1502 = \ _self ->
     _self
   {-# INLINE rule1503 #-}
   rule1503 = \ ((_typeIcounter) :: Int) ->
     _typeIcounter
   {-# INLINE rule1504 #-}
   rule1504 = \ ((_typeImiscerrors) :: [Error]) ->
     _typeImiscerrors
   {-# INLINE rule1505 #-}
   rule1505 = \ _allTypeConstructors ->
     _allTypeConstructors
   {-# INLINE rule1506 #-}
   rule1506 = \ _allValueConstructors ->
     _allValueConstructors
   {-# INLINE rule1507 #-}
   rule1507 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1508 #-}
   rule1508 = \ _kindErrors ->
     _kindErrors
   {-# INLINE rule1509 #-}
   rule1509 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1510 #-}
   rule1510 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1511 #-}
   rule1511 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1512 #-}
   rule1512 = \ _typeConstructors ->
     _typeConstructors
   {-# INLINE rule1513 #-}
   rule1513 = \ _valueConstructors ->
     _valueConstructors
   {-# INLINE rule1514 #-}
   rule1514 = \ _warnings ->
     _warnings

-- FieldDeclarations -------------------------------------------
-- wrapper
data Inh_FieldDeclarations  = Inh_FieldDeclarations { counter_Inh_FieldDeclarations :: (Int), miscerrors_Inh_FieldDeclarations :: ([Error]), namesInScope_Inh_FieldDeclarations :: (Names), options_Inh_FieldDeclarations :: ([Option]) }
data Syn_FieldDeclarations  = Syn_FieldDeclarations { counter_Syn_FieldDeclarations :: (Int), miscerrors_Syn_FieldDeclarations :: ([Error]), self_Syn_FieldDeclarations :: (FieldDeclarations), unboundNames_Syn_FieldDeclarations :: (Names) }
{-# INLINABLE wrap_FieldDeclarations #-}
wrap_FieldDeclarations :: T_FieldDeclarations  -> Inh_FieldDeclarations  -> (Syn_FieldDeclarations )
wrap_FieldDeclarations (T_FieldDeclarations act) (Inh_FieldDeclarations _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsIoptions) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_FieldDeclarations_vIn49 _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsIoptions
        (T_FieldDeclarations_vOut49 _lhsOcounter _lhsOmiscerrors _lhsOself _lhsOunboundNames) <- return (inv_FieldDeclarations_s50 sem arg)
        return (Syn_FieldDeclarations _lhsOcounter _lhsOmiscerrors _lhsOself _lhsOunboundNames)
   )

-- cata
{-# NOINLINE sem_FieldDeclarations #-}
sem_FieldDeclarations :: FieldDeclarations  -> T_FieldDeclarations 
sem_FieldDeclarations list = Prelude.foldr sem_FieldDeclarations_Cons sem_FieldDeclarations_Nil (Prelude.map sem_FieldDeclaration list)

-- semantic domain
newtype T_FieldDeclarations  = T_FieldDeclarations {
                                                   attach_T_FieldDeclarations :: Identity (T_FieldDeclarations_s50 )
                                                   }
newtype T_FieldDeclarations_s50  = C_FieldDeclarations_s50 {
                                                           inv_FieldDeclarations_s50 :: (T_FieldDeclarations_v49 )
                                                           }
data T_FieldDeclarations_s51  = C_FieldDeclarations_s51
type T_FieldDeclarations_v49  = (T_FieldDeclarations_vIn49 ) -> (T_FieldDeclarations_vOut49 )
data T_FieldDeclarations_vIn49  = T_FieldDeclarations_vIn49 (Int) ([Error]) (Names) ([Option])
data T_FieldDeclarations_vOut49  = T_FieldDeclarations_vOut49 (Int) ([Error]) (FieldDeclarations) (Names)
{-# NOINLINE sem_FieldDeclarations_Cons #-}
sem_FieldDeclarations_Cons :: T_FieldDeclaration  -> T_FieldDeclarations  -> T_FieldDeclarations 
sem_FieldDeclarations_Cons arg_hd_ arg_tl_ = T_FieldDeclarations (return st50) where
   {-# NOINLINE st50 #-}
   st50 = let
      v49 :: T_FieldDeclarations_v49 
      v49 = \ (T_FieldDeclarations_vIn49 _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsIoptions) -> ( let
         _hdX47 = Control.Monad.Identity.runIdentity (attach_T_FieldDeclaration (arg_hd_))
         _tlX50 = Control.Monad.Identity.runIdentity (attach_T_FieldDeclarations (arg_tl_))
         (T_FieldDeclaration_vOut46 _hdIcounter _hdImiscerrors _hdIself _hdIunboundNames) = inv_FieldDeclaration_s47 _hdX47 (T_FieldDeclaration_vIn46 _hdOcounter _hdOmiscerrors _hdOnamesInScope _hdOoptions)
         (T_FieldDeclarations_vOut49 _tlIcounter _tlImiscerrors _tlIself _tlIunboundNames) = inv_FieldDeclarations_s50 _tlX50 (T_FieldDeclarations_vIn49 _tlOcounter _tlOmiscerrors _tlOnamesInScope _tlOoptions)
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1515 _hdIunboundNames _tlIunboundNames
         _self = rule1516 _hdIself _tlIself
         _lhsOself :: FieldDeclarations
         _lhsOself = rule1517 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule1518 _tlIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1519 _tlImiscerrors
         _hdOcounter = rule1520 _lhsIcounter
         _hdOmiscerrors = rule1521 _lhsImiscerrors
         _hdOnamesInScope = rule1522 _lhsInamesInScope
         _hdOoptions = rule1523 _lhsIoptions
         _tlOcounter = rule1524 _hdIcounter
         _tlOmiscerrors = rule1525 _hdImiscerrors
         _tlOnamesInScope = rule1526 _lhsInamesInScope
         _tlOoptions = rule1527 _lhsIoptions
         __result_ = T_FieldDeclarations_vOut49 _lhsOcounter _lhsOmiscerrors _lhsOself _lhsOunboundNames
         in __result_ )
     in C_FieldDeclarations_s50 v49
   {-# INLINE rule1515 #-}
   rule1515 = \ ((_hdIunboundNames) :: Names) ((_tlIunboundNames) :: Names) ->
     _hdIunboundNames ++ _tlIunboundNames
   {-# INLINE rule1516 #-}
   rule1516 = \ ((_hdIself) :: FieldDeclaration) ((_tlIself) :: FieldDeclarations) ->
     (:) _hdIself _tlIself
   {-# INLINE rule1517 #-}
   rule1517 = \ _self ->
     _self
   {-# INLINE rule1518 #-}
   rule1518 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule1519 #-}
   rule1519 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule1520 #-}
   rule1520 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1521 #-}
   rule1521 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1522 #-}
   rule1522 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1523 #-}
   rule1523 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1524 #-}
   rule1524 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule1525 #-}
   rule1525 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule1526 #-}
   rule1526 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1527 #-}
   rule1527 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
{-# NOINLINE sem_FieldDeclarations_Nil #-}
sem_FieldDeclarations_Nil ::  T_FieldDeclarations 
sem_FieldDeclarations_Nil  = T_FieldDeclarations (return st50) where
   {-# NOINLINE st50 #-}
   st50 = let
      v49 :: T_FieldDeclarations_v49 
      v49 = \ (T_FieldDeclarations_vIn49 _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsIoptions) -> ( let
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1528  ()
         _self = rule1529  ()
         _lhsOself :: FieldDeclarations
         _lhsOself = rule1530 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule1531 _lhsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1532 _lhsImiscerrors
         __result_ = T_FieldDeclarations_vOut49 _lhsOcounter _lhsOmiscerrors _lhsOself _lhsOunboundNames
         in __result_ )
     in C_FieldDeclarations_s50 v49
   {-# INLINE rule1528 #-}
   rule1528 = \  (_ :: ()) ->
     []
   {-# INLINE rule1529 #-}
   rule1529 = \  (_ :: ()) ->
     []
   {-# INLINE rule1530 #-}
   rule1530 = \ _self ->
     _self
   {-# INLINE rule1531 #-}
   rule1531 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1532 #-}
   rule1532 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors

-- Fixity ------------------------------------------------------
-- wrapper
data Inh_Fixity  = Inh_Fixity {  }
data Syn_Fixity  = Syn_Fixity { self_Syn_Fixity :: (Fixity) }
{-# INLINABLE wrap_Fixity #-}
wrap_Fixity :: T_Fixity  -> Inh_Fixity  -> (Syn_Fixity )
wrap_Fixity (T_Fixity act) (Inh_Fixity ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Fixity_vIn52 
        (T_Fixity_vOut52 _lhsOself) <- return (inv_Fixity_s53 sem arg)
        return (Syn_Fixity _lhsOself)
   )

-- cata
{-# NOINLINE sem_Fixity #-}
sem_Fixity :: Fixity  -> T_Fixity 
sem_Fixity ( Fixity_Infixl range_ ) = sem_Fixity_Infixl ( sem_Range range_ )
sem_Fixity ( Fixity_Infixr range_ ) = sem_Fixity_Infixr ( sem_Range range_ )
sem_Fixity ( Fixity_Infix range_ ) = sem_Fixity_Infix ( sem_Range range_ )

-- semantic domain
newtype T_Fixity  = T_Fixity {
                             attach_T_Fixity :: Identity (T_Fixity_s53 )
                             }
newtype T_Fixity_s53  = C_Fixity_s53 {
                                     inv_Fixity_s53 :: (T_Fixity_v52 )
                                     }
data T_Fixity_s54  = C_Fixity_s54
type T_Fixity_v52  = (T_Fixity_vIn52 ) -> (T_Fixity_vOut52 )
data T_Fixity_vIn52  = T_Fixity_vIn52 
data T_Fixity_vOut52  = T_Fixity_vOut52 (Fixity)
{-# NOINLINE sem_Fixity_Infixl #-}
sem_Fixity_Infixl :: T_Range  -> T_Fixity 
sem_Fixity_Infixl arg_range_ = T_Fixity (return st53) where
   {-# NOINLINE st53 #-}
   st53 = let
      v52 :: T_Fixity_v52 
      v52 = \ (T_Fixity_vIn52 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _self = rule1533 _rangeIself
         _lhsOself :: Fixity
         _lhsOself = rule1534 _self
         __result_ = T_Fixity_vOut52 _lhsOself
         in __result_ )
     in C_Fixity_s53 v52
   {-# INLINE rule1533 #-}
   rule1533 = \ ((_rangeIself) :: Range) ->
     Fixity_Infixl _rangeIself
   {-# INLINE rule1534 #-}
   rule1534 = \ _self ->
     _self
{-# NOINLINE sem_Fixity_Infixr #-}
sem_Fixity_Infixr :: T_Range  -> T_Fixity 
sem_Fixity_Infixr arg_range_ = T_Fixity (return st53) where
   {-# NOINLINE st53 #-}
   st53 = let
      v52 :: T_Fixity_v52 
      v52 = \ (T_Fixity_vIn52 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _self = rule1535 _rangeIself
         _lhsOself :: Fixity
         _lhsOself = rule1536 _self
         __result_ = T_Fixity_vOut52 _lhsOself
         in __result_ )
     in C_Fixity_s53 v52
   {-# INLINE rule1535 #-}
   rule1535 = \ ((_rangeIself) :: Range) ->
     Fixity_Infixr _rangeIself
   {-# INLINE rule1536 #-}
   rule1536 = \ _self ->
     _self
{-# NOINLINE sem_Fixity_Infix #-}
sem_Fixity_Infix :: T_Range  -> T_Fixity 
sem_Fixity_Infix arg_range_ = T_Fixity (return st53) where
   {-# NOINLINE st53 #-}
   st53 = let
      v52 :: T_Fixity_v52 
      v52 = \ (T_Fixity_vIn52 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _self = rule1537 _rangeIself
         _lhsOself :: Fixity
         _lhsOself = rule1538 _self
         __result_ = T_Fixity_vOut52 _lhsOself
         in __result_ )
     in C_Fixity_s53 v52
   {-# INLINE rule1537 #-}
   rule1537 = \ ((_rangeIself) :: Range) ->
     Fixity_Infix _rangeIself
   {-# INLINE rule1538 #-}
   rule1538 = \ _self ->
     _self

-- FunctionBinding ---------------------------------------------
-- wrapper
data Inh_FunctionBinding  = Inh_FunctionBinding { allTypeConstructors_Inh_FunctionBinding :: (Names), allValueConstructors_Inh_FunctionBinding :: (Names), classEnvironment_Inh_FunctionBinding :: (ClassEnvironment), collectScopeInfos_Inh_FunctionBinding :: ([(ScopeInfo, Entity)]), counter_Inh_FunctionBinding :: (Int), kindErrors_Inh_FunctionBinding :: ([Error]), miscerrors_Inh_FunctionBinding :: ([Error]), namesInScope_Inh_FunctionBinding :: (Names), options_Inh_FunctionBinding :: ([Option]), orderedTypeSynonyms_Inh_FunctionBinding :: (OrderedTypeSynonyms), typeConstructors_Inh_FunctionBinding :: (M.Map Name Int), valueConstructors_Inh_FunctionBinding :: (M.Map Name TpScheme), warnings_Inh_FunctionBinding :: ([Warning]) }
data Syn_FunctionBinding  = Syn_FunctionBinding { arity_Syn_FunctionBinding :: (Int), collectInstances_Syn_FunctionBinding :: ([(Name, Instance)]), collectScopeInfos_Syn_FunctionBinding :: ([(ScopeInfo, Entity)]), counter_Syn_FunctionBinding :: (Int), kindErrors_Syn_FunctionBinding :: ([Error]), miscerrors_Syn_FunctionBinding :: ([Error]), name_Syn_FunctionBinding :: (Name), self_Syn_FunctionBinding :: (FunctionBinding), unboundNames_Syn_FunctionBinding :: (Names), warnings_Syn_FunctionBinding :: ([Warning]) }
{-# INLINABLE wrap_FunctionBinding #-}
wrap_FunctionBinding :: T_FunctionBinding  -> Inh_FunctionBinding  -> (Syn_FunctionBinding )
wrap_FunctionBinding (T_FunctionBinding act) (Inh_FunctionBinding _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_FunctionBinding_vIn55 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_FunctionBinding_vOut55 _lhsOarity _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOname _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_FunctionBinding_s56 sem arg)
        return (Syn_FunctionBinding _lhsOarity _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOname _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_FunctionBinding #-}
sem_FunctionBinding :: FunctionBinding  -> T_FunctionBinding 
sem_FunctionBinding ( FunctionBinding_Hole range_ id_ ) = sem_FunctionBinding_Hole ( sem_Range range_ ) id_
sem_FunctionBinding ( FunctionBinding_Feedback range_ feedback_ functionBinding_ ) = sem_FunctionBinding_Feedback ( sem_Range range_ ) feedback_ ( sem_FunctionBinding functionBinding_ )
sem_FunctionBinding ( FunctionBinding_FunctionBinding range_ lefthandside_ righthandside_ ) = sem_FunctionBinding_FunctionBinding ( sem_Range range_ ) ( sem_LeftHandSide lefthandside_ ) ( sem_RightHandSide righthandside_ )

-- semantic domain
newtype T_FunctionBinding  = T_FunctionBinding {
                                               attach_T_FunctionBinding :: Identity (T_FunctionBinding_s56 )
                                               }
newtype T_FunctionBinding_s56  = C_FunctionBinding_s56 {
                                                       inv_FunctionBinding_s56 :: (T_FunctionBinding_v55 )
                                                       }
data T_FunctionBinding_s57  = C_FunctionBinding_s57
type T_FunctionBinding_v55  = (T_FunctionBinding_vIn55 ) -> (T_FunctionBinding_vOut55 )
data T_FunctionBinding_vIn55  = T_FunctionBinding_vIn55 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_FunctionBinding_vOut55  = T_FunctionBinding_vOut55 (Int) ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Name) (FunctionBinding) (Names) ([Warning])
{-# NOINLINE sem_FunctionBinding_Hole #-}
sem_FunctionBinding_Hole :: T_Range  -> (Integer) -> T_FunctionBinding 
sem_FunctionBinding_Hole arg_range_ arg_id_ = T_FunctionBinding (return st56) where
   {-# NOINLINE st56 #-}
   st56 = let
      v55 :: T_FunctionBinding_v55 
      v55 = \ (T_FunctionBinding_vIn55 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOname :: Name
         _lhsOname = rule1539  ()
         _lhsOarity :: Int
         _lhsOarity = rule1540  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1541  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1542  ()
         _self = rule1543 _rangeIself arg_id_
         _lhsOself :: FunctionBinding
         _lhsOself = rule1544 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1545 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1546 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1547 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1548 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1549 _lhsIwarnings
         __result_ = T_FunctionBinding_vOut55 _lhsOarity _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOname _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_FunctionBinding_s56 v55
   {-# INLINE rule1539 #-}
   rule1539 = \  (_ :: ()) ->
                         internalError "StaticChecks.ag" "n/a" "empty FunctionBindings"
   {-# INLINE rule1540 #-}
   rule1540 = \  (_ :: ()) ->
                                    0
   {-# INLINE rule1541 #-}
   rule1541 = \  (_ :: ()) ->
     []
   {-# INLINE rule1542 #-}
   rule1542 = \  (_ :: ()) ->
     []
   {-# INLINE rule1543 #-}
   rule1543 = \ ((_rangeIself) :: Range) id_ ->
     FunctionBinding_Hole _rangeIself id_
   {-# INLINE rule1544 #-}
   rule1544 = \ _self ->
     _self
   {-# INLINE rule1545 #-}
   rule1545 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1546 #-}
   rule1546 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1547 #-}
   rule1547 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1548 #-}
   rule1548 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1549 #-}
   rule1549 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_FunctionBinding_Feedback #-}
sem_FunctionBinding_Feedback :: T_Range  -> (String) -> T_FunctionBinding  -> T_FunctionBinding 
sem_FunctionBinding_Feedback arg_range_ arg_feedback_ arg_functionBinding_ = T_FunctionBinding (return st56) where
   {-# NOINLINE st56 #-}
   st56 = let
      v55 :: T_FunctionBinding_v55 
      v55 = \ (T_FunctionBinding_vIn55 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _functionBindingX56 = Control.Monad.Identity.runIdentity (attach_T_FunctionBinding (arg_functionBinding_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_FunctionBinding_vOut55 _functionBindingIarity _functionBindingIcollectInstances _functionBindingIcollectScopeInfos _functionBindingIcounter _functionBindingIkindErrors _functionBindingImiscerrors _functionBindingIname _functionBindingIself _functionBindingIunboundNames _functionBindingIwarnings) = inv_FunctionBinding_s56 _functionBindingX56 (T_FunctionBinding_vIn55 _functionBindingOallTypeConstructors _functionBindingOallValueConstructors _functionBindingOclassEnvironment _functionBindingOcollectScopeInfos _functionBindingOcounter _functionBindingOkindErrors _functionBindingOmiscerrors _functionBindingOnamesInScope _functionBindingOoptions _functionBindingOorderedTypeSynonyms _functionBindingOtypeConstructors _functionBindingOvalueConstructors _functionBindingOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1550 _functionBindingIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1551 _functionBindingIunboundNames
         _self = rule1552 _functionBindingIself _rangeIself arg_feedback_
         _lhsOself :: FunctionBinding
         _lhsOself = rule1553 _self
         _lhsOarity :: Int
         _lhsOarity = rule1554 _functionBindingIarity
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1555 _functionBindingIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1556 _functionBindingIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1557 _functionBindingIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1558 _functionBindingImiscerrors
         _lhsOname :: Name
         _lhsOname = rule1559 _functionBindingIname
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1560 _functionBindingIwarnings
         _functionBindingOallTypeConstructors = rule1561 _lhsIallTypeConstructors
         _functionBindingOallValueConstructors = rule1562 _lhsIallValueConstructors
         _functionBindingOclassEnvironment = rule1563 _lhsIclassEnvironment
         _functionBindingOcollectScopeInfos = rule1564 _lhsIcollectScopeInfos
         _functionBindingOcounter = rule1565 _lhsIcounter
         _functionBindingOkindErrors = rule1566 _lhsIkindErrors
         _functionBindingOmiscerrors = rule1567 _lhsImiscerrors
         _functionBindingOnamesInScope = rule1568 _lhsInamesInScope
         _functionBindingOoptions = rule1569 _lhsIoptions
         _functionBindingOorderedTypeSynonyms = rule1570 _lhsIorderedTypeSynonyms
         _functionBindingOtypeConstructors = rule1571 _lhsItypeConstructors
         _functionBindingOvalueConstructors = rule1572 _lhsIvalueConstructors
         _functionBindingOwarnings = rule1573 _lhsIwarnings
         __result_ = T_FunctionBinding_vOut55 _lhsOarity _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOname _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_FunctionBinding_s56 v55
   {-# INLINE rule1550 #-}
   rule1550 = \ ((_functionBindingIcollectInstances) :: [(Name, Instance)]) ->
     _functionBindingIcollectInstances
   {-# INLINE rule1551 #-}
   rule1551 = \ ((_functionBindingIunboundNames) :: Names) ->
     _functionBindingIunboundNames
   {-# INLINE rule1552 #-}
   rule1552 = \ ((_functionBindingIself) :: FunctionBinding) ((_rangeIself) :: Range) feedback_ ->
     FunctionBinding_Feedback _rangeIself feedback_ _functionBindingIself
   {-# INLINE rule1553 #-}
   rule1553 = \ _self ->
     _self
   {-# INLINE rule1554 #-}
   rule1554 = \ ((_functionBindingIarity) :: Int) ->
     _functionBindingIarity
   {-# INLINE rule1555 #-}
   rule1555 = \ ((_functionBindingIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _functionBindingIcollectScopeInfos
   {-# INLINE rule1556 #-}
   rule1556 = \ ((_functionBindingIcounter) :: Int) ->
     _functionBindingIcounter
   {-# INLINE rule1557 #-}
   rule1557 = \ ((_functionBindingIkindErrors) :: [Error]) ->
     _functionBindingIkindErrors
   {-# INLINE rule1558 #-}
   rule1558 = \ ((_functionBindingImiscerrors) :: [Error]) ->
     _functionBindingImiscerrors
   {-# INLINE rule1559 #-}
   rule1559 = \ ((_functionBindingIname) :: Name) ->
     _functionBindingIname
   {-# INLINE rule1560 #-}
   rule1560 = \ ((_functionBindingIwarnings) :: [Warning]) ->
     _functionBindingIwarnings
   {-# INLINE rule1561 #-}
   rule1561 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1562 #-}
   rule1562 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1563 #-}
   rule1563 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1564 #-}
   rule1564 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1565 #-}
   rule1565 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1566 #-}
   rule1566 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1567 #-}
   rule1567 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1568 #-}
   rule1568 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1569 #-}
   rule1569 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1570 #-}
   rule1570 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1571 #-}
   rule1571 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1572 #-}
   rule1572 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1573 #-}
   rule1573 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_FunctionBinding_FunctionBinding #-}
sem_FunctionBinding_FunctionBinding :: T_Range  -> T_LeftHandSide  -> T_RightHandSide  -> T_FunctionBinding 
sem_FunctionBinding_FunctionBinding arg_range_ arg_lefthandside_ arg_righthandside_ = T_FunctionBinding (return st56) where
   {-# NOINLINE st56 #-}
   st56 = let
      v55 :: T_FunctionBinding_v55 
      v55 = \ (T_FunctionBinding_vIn55 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _lefthandsideX83 = Control.Monad.Identity.runIdentity (attach_T_LeftHandSide (arg_lefthandside_))
         _righthandsideX149 = Control.Monad.Identity.runIdentity (attach_T_RightHandSide (arg_righthandside_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_LeftHandSide_vOut82 _lefthandsideIcollectScopeInfos _lefthandsideIcounter _lefthandsideImiscerrors _lefthandsideIname _lefthandsideInumberOfPatterns _lefthandsideIpatVarNames _lefthandsideIself _lefthandsideIunboundNames _lefthandsideIwarnings) = inv_LeftHandSide_s83 _lefthandsideX83 (T_LeftHandSide_vIn82 _lefthandsideOallTypeConstructors _lefthandsideOallValueConstructors _lefthandsideOcollectScopeInfos _lefthandsideOcounter _lefthandsideOmiscerrors _lefthandsideOnamesInScope _lefthandsideOtypeConstructors _lefthandsideOvalueConstructors _lefthandsideOwarnings)
         (T_RightHandSide_vOut148 _righthandsideIcollectInstances _righthandsideIcollectScopeInfos _righthandsideIcounter _righthandsideIkindErrors _righthandsideImiscerrors _righthandsideIself _righthandsideIunboundNames _righthandsideIwarnings) = inv_RightHandSide_s149 _righthandsideX149 (T_RightHandSide_vIn148 _righthandsideOallTypeConstructors _righthandsideOallValueConstructors _righthandsideOclassEnvironment _righthandsideOcollectScopeInfos _righthandsideOcounter _righthandsideOkindErrors _righthandsideOmiscerrors _righthandsideOnamesInScope _righthandsideOoptions _righthandsideOorderedTypeSynonyms _righthandsideOtypeConstructors _righthandsideOvalueConstructors _righthandsideOwarnings)
         (_namesInScope,_unboundNames,_scopeInfo) = rule1574 _lefthandsideIpatVarNames _lhsInamesInScope _righthandsideIunboundNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1575 _unboundNames
         _lhsOarity :: Int
         _lhsOarity = rule1576 _lefthandsideInumberOfPatterns
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1577 _righthandsideIcollectScopeInfos _scopeInfo
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1578 _righthandsideIcollectInstances
         _self = rule1579 _lefthandsideIself _rangeIself _righthandsideIself
         _lhsOself :: FunctionBinding
         _lhsOself = rule1580 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule1581 _righthandsideIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1582 _righthandsideIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1583 _righthandsideImiscerrors
         _lhsOname :: Name
         _lhsOname = rule1584 _lefthandsideIname
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1585 _righthandsideIwarnings
         _lefthandsideOallTypeConstructors = rule1586 _lhsIallTypeConstructors
         _lefthandsideOallValueConstructors = rule1587 _lhsIallValueConstructors
         _lefthandsideOcollectScopeInfos = rule1588 _lhsIcollectScopeInfos
         _lefthandsideOcounter = rule1589 _lhsIcounter
         _lefthandsideOmiscerrors = rule1590 _lhsImiscerrors
         _lefthandsideOnamesInScope = rule1591 _namesInScope
         _lefthandsideOtypeConstructors = rule1592 _lhsItypeConstructors
         _lefthandsideOvalueConstructors = rule1593 _lhsIvalueConstructors
         _lefthandsideOwarnings = rule1594 _lhsIwarnings
         _righthandsideOallTypeConstructors = rule1595 _lhsIallTypeConstructors
         _righthandsideOallValueConstructors = rule1596 _lhsIallValueConstructors
         _righthandsideOclassEnvironment = rule1597 _lhsIclassEnvironment
         _righthandsideOcollectScopeInfos = rule1598 _lefthandsideIcollectScopeInfos
         _righthandsideOcounter = rule1599 _lefthandsideIcounter
         _righthandsideOkindErrors = rule1600 _lhsIkindErrors
         _righthandsideOmiscerrors = rule1601 _lefthandsideImiscerrors
         _righthandsideOnamesInScope = rule1602 _namesInScope
         _righthandsideOoptions = rule1603 _lhsIoptions
         _righthandsideOorderedTypeSynonyms = rule1604 _lhsIorderedTypeSynonyms
         _righthandsideOtypeConstructors = rule1605 _lhsItypeConstructors
         _righthandsideOvalueConstructors = rule1606 _lhsIvalueConstructors
         _righthandsideOwarnings = rule1607 _lefthandsideIwarnings
         __result_ = T_FunctionBinding_vOut55 _lhsOarity _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOname _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_FunctionBinding_s56 v55
   {-# INLINE rule1574 #-}
   rule1574 = \ ((_lefthandsideIpatVarNames) :: Names) ((_lhsInamesInScope) :: Names) ((_righthandsideIunboundNames) :: Names) ->
                                                                        changeOfScope _lefthandsideIpatVarNames _righthandsideIunboundNames _lhsInamesInScope
   {-# INLINE rule1575 #-}
   rule1575 = \ _unboundNames ->
                                             _unboundNames
   {-# INLINE rule1576 #-}
   rule1576 = \ ((_lefthandsideInumberOfPatterns) :: Int) ->
                                    _lefthandsideInumberOfPatterns
   {-# INLINE rule1577 #-}
   rule1577 = \ ((_righthandsideIcollectScopeInfos) :: [(ScopeInfo, Entity)]) _scopeInfo ->
                                                 (_scopeInfo, Variable)   : _righthandsideIcollectScopeInfos
   {-# INLINE rule1578 #-}
   rule1578 = \ ((_righthandsideIcollectInstances) :: [(Name, Instance)]) ->
     _righthandsideIcollectInstances
   {-# INLINE rule1579 #-}
   rule1579 = \ ((_lefthandsideIself) :: LeftHandSide) ((_rangeIself) :: Range) ((_righthandsideIself) :: RightHandSide) ->
     FunctionBinding_FunctionBinding _rangeIself _lefthandsideIself _righthandsideIself
   {-# INLINE rule1580 #-}
   rule1580 = \ _self ->
     _self
   {-# INLINE rule1581 #-}
   rule1581 = \ ((_righthandsideIcounter) :: Int) ->
     _righthandsideIcounter
   {-# INLINE rule1582 #-}
   rule1582 = \ ((_righthandsideIkindErrors) :: [Error]) ->
     _righthandsideIkindErrors
   {-# INLINE rule1583 #-}
   rule1583 = \ ((_righthandsideImiscerrors) :: [Error]) ->
     _righthandsideImiscerrors
   {-# INLINE rule1584 #-}
   rule1584 = \ ((_lefthandsideIname) :: Name) ->
     _lefthandsideIname
   {-# INLINE rule1585 #-}
   rule1585 = \ ((_righthandsideIwarnings) :: [Warning]) ->
     _righthandsideIwarnings
   {-# INLINE rule1586 #-}
   rule1586 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1587 #-}
   rule1587 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1588 #-}
   rule1588 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1589 #-}
   rule1589 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1590 #-}
   rule1590 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1591 #-}
   rule1591 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule1592 #-}
   rule1592 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1593 #-}
   rule1593 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1594 #-}
   rule1594 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1595 #-}
   rule1595 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1596 #-}
   rule1596 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1597 #-}
   rule1597 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1598 #-}
   rule1598 = \ ((_lefthandsideIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lefthandsideIcollectScopeInfos
   {-# INLINE rule1599 #-}
   rule1599 = \ ((_lefthandsideIcounter) :: Int) ->
     _lefthandsideIcounter
   {-# INLINE rule1600 #-}
   rule1600 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1601 #-}
   rule1601 = \ ((_lefthandsideImiscerrors) :: [Error]) ->
     _lefthandsideImiscerrors
   {-# INLINE rule1602 #-}
   rule1602 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule1603 #-}
   rule1603 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1604 #-}
   rule1604 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1605 #-}
   rule1605 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1606 #-}
   rule1606 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1607 #-}
   rule1607 = \ ((_lefthandsideIwarnings) :: [Warning]) ->
     _lefthandsideIwarnings

-- FunctionBindings --------------------------------------------
-- wrapper
data Inh_FunctionBindings  = Inh_FunctionBindings { allTypeConstructors_Inh_FunctionBindings :: (Names), allValueConstructors_Inh_FunctionBindings :: (Names), classEnvironment_Inh_FunctionBindings :: (ClassEnvironment), collectScopeInfos_Inh_FunctionBindings :: ([(ScopeInfo, Entity)]), counter_Inh_FunctionBindings :: (Int), kindErrors_Inh_FunctionBindings :: ([Error]), miscerrors_Inh_FunctionBindings :: ([Error]), namesInScope_Inh_FunctionBindings :: (Names), options_Inh_FunctionBindings :: ([Option]), orderedTypeSynonyms_Inh_FunctionBindings :: (OrderedTypeSynonyms), typeConstructors_Inh_FunctionBindings :: (M.Map Name Int), valueConstructors_Inh_FunctionBindings :: (M.Map Name TpScheme), warnings_Inh_FunctionBindings :: ([Warning]) }
data Syn_FunctionBindings  = Syn_FunctionBindings { arities_Syn_FunctionBindings :: ( [Int] ), collectInstances_Syn_FunctionBindings :: ([(Name, Instance)]), collectScopeInfos_Syn_FunctionBindings :: ([(ScopeInfo, Entity)]), counter_Syn_FunctionBindings :: (Int), kindErrors_Syn_FunctionBindings :: ([Error]), miscerrors_Syn_FunctionBindings :: ([Error]), name_Syn_FunctionBindings :: (Name), self_Syn_FunctionBindings :: (FunctionBindings), unboundNames_Syn_FunctionBindings :: (Names), warnings_Syn_FunctionBindings :: ([Warning]) }
{-# INLINABLE wrap_FunctionBindings #-}
wrap_FunctionBindings :: T_FunctionBindings  -> Inh_FunctionBindings  -> (Syn_FunctionBindings )
wrap_FunctionBindings (T_FunctionBindings act) (Inh_FunctionBindings _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_FunctionBindings_vIn58 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_FunctionBindings_vOut58 _lhsOarities _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOname _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_FunctionBindings_s59 sem arg)
        return (Syn_FunctionBindings _lhsOarities _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOname _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_FunctionBindings #-}
sem_FunctionBindings :: FunctionBindings  -> T_FunctionBindings 
sem_FunctionBindings list = Prelude.foldr sem_FunctionBindings_Cons sem_FunctionBindings_Nil (Prelude.map sem_FunctionBinding list)

-- semantic domain
newtype T_FunctionBindings  = T_FunctionBindings {
                                                 attach_T_FunctionBindings :: Identity (T_FunctionBindings_s59 )
                                                 }
newtype T_FunctionBindings_s59  = C_FunctionBindings_s59 {
                                                         inv_FunctionBindings_s59 :: (T_FunctionBindings_v58 )
                                                         }
data T_FunctionBindings_s60  = C_FunctionBindings_s60
type T_FunctionBindings_v58  = (T_FunctionBindings_vIn58 ) -> (T_FunctionBindings_vOut58 )
data T_FunctionBindings_vIn58  = T_FunctionBindings_vIn58 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_FunctionBindings_vOut58  = T_FunctionBindings_vOut58 ( [Int] ) ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Name) (FunctionBindings) (Names) ([Warning])
{-# NOINLINE sem_FunctionBindings_Cons #-}
sem_FunctionBindings_Cons :: T_FunctionBinding  -> T_FunctionBindings  -> T_FunctionBindings 
sem_FunctionBindings_Cons arg_hd_ arg_tl_ = T_FunctionBindings (return st59) where
   {-# NOINLINE st59 #-}
   st59 = let
      v58 :: T_FunctionBindings_v58 
      v58 = \ (T_FunctionBindings_vIn58 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _hdX56 = Control.Monad.Identity.runIdentity (attach_T_FunctionBinding (arg_hd_))
         _tlX59 = Control.Monad.Identity.runIdentity (attach_T_FunctionBindings (arg_tl_))
         (T_FunctionBinding_vOut55 _hdIarity _hdIcollectInstances _hdIcollectScopeInfos _hdIcounter _hdIkindErrors _hdImiscerrors _hdIname _hdIself _hdIunboundNames _hdIwarnings) = inv_FunctionBinding_s56 _hdX56 (T_FunctionBinding_vIn55 _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOcounter _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings)
         (T_FunctionBindings_vOut58 _tlIarities _tlIcollectInstances _tlIcollectScopeInfos _tlIcounter _tlIkindErrors _tlImiscerrors _tlIname _tlIself _tlIunboundNames _tlIwarnings) = inv_FunctionBindings_s59 _tlX59 (T_FunctionBindings_vIn58 _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOcounter _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings)
         _lhsOname :: Name
         _lhsOname = rule1608 _hdIname
         _lhsOarities ::  [Int] 
         _lhsOarities = rule1609 _hdIarity _tlIarities
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1610 _hdIcollectInstances _tlIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1611 _hdIunboundNames _tlIunboundNames
         _self = rule1612 _hdIself _tlIself
         _lhsOself :: FunctionBindings
         _lhsOself = rule1613 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1614 _tlIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1615 _tlIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1616 _tlIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1617 _tlImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1618 _tlIwarnings
         _hdOallTypeConstructors = rule1619 _lhsIallTypeConstructors
         _hdOallValueConstructors = rule1620 _lhsIallValueConstructors
         _hdOclassEnvironment = rule1621 _lhsIclassEnvironment
         _hdOcollectScopeInfos = rule1622 _lhsIcollectScopeInfos
         _hdOcounter = rule1623 _lhsIcounter
         _hdOkindErrors = rule1624 _lhsIkindErrors
         _hdOmiscerrors = rule1625 _lhsImiscerrors
         _hdOnamesInScope = rule1626 _lhsInamesInScope
         _hdOoptions = rule1627 _lhsIoptions
         _hdOorderedTypeSynonyms = rule1628 _lhsIorderedTypeSynonyms
         _hdOtypeConstructors = rule1629 _lhsItypeConstructors
         _hdOvalueConstructors = rule1630 _lhsIvalueConstructors
         _hdOwarnings = rule1631 _lhsIwarnings
         _tlOallTypeConstructors = rule1632 _lhsIallTypeConstructors
         _tlOallValueConstructors = rule1633 _lhsIallValueConstructors
         _tlOclassEnvironment = rule1634 _lhsIclassEnvironment
         _tlOcollectScopeInfos = rule1635 _hdIcollectScopeInfos
         _tlOcounter = rule1636 _hdIcounter
         _tlOkindErrors = rule1637 _hdIkindErrors
         _tlOmiscerrors = rule1638 _hdImiscerrors
         _tlOnamesInScope = rule1639 _lhsInamesInScope
         _tlOoptions = rule1640 _lhsIoptions
         _tlOorderedTypeSynonyms = rule1641 _lhsIorderedTypeSynonyms
         _tlOtypeConstructors = rule1642 _lhsItypeConstructors
         _tlOvalueConstructors = rule1643 _lhsIvalueConstructors
         _tlOwarnings = rule1644 _hdIwarnings
         __result_ = T_FunctionBindings_vOut58 _lhsOarities _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOname _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_FunctionBindings_s59 v58
   {-# INLINE rule1608 #-}
   rule1608 = \ ((_hdIname) :: Name) ->
                         _hdIname
   {-# INLINE rule1609 #-}
   rule1609 = \ ((_hdIarity) :: Int) ((_tlIarities) ::  [Int] ) ->
                         _hdIarity : _tlIarities
   {-# INLINE rule1610 #-}
   rule1610 = \ ((_hdIcollectInstances) :: [(Name, Instance)]) ((_tlIcollectInstances) :: [(Name, Instance)]) ->
     _hdIcollectInstances  ++  _tlIcollectInstances
   {-# INLINE rule1611 #-}
   rule1611 = \ ((_hdIunboundNames) :: Names) ((_tlIunboundNames) :: Names) ->
     _hdIunboundNames ++ _tlIunboundNames
   {-# INLINE rule1612 #-}
   rule1612 = \ ((_hdIself) :: FunctionBinding) ((_tlIself) :: FunctionBindings) ->
     (:) _hdIself _tlIself
   {-# INLINE rule1613 #-}
   rule1613 = \ _self ->
     _self
   {-# INLINE rule1614 #-}
   rule1614 = \ ((_tlIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _tlIcollectScopeInfos
   {-# INLINE rule1615 #-}
   rule1615 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule1616 #-}
   rule1616 = \ ((_tlIkindErrors) :: [Error]) ->
     _tlIkindErrors
   {-# INLINE rule1617 #-}
   rule1617 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule1618 #-}
   rule1618 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule1619 #-}
   rule1619 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1620 #-}
   rule1620 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1621 #-}
   rule1621 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1622 #-}
   rule1622 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1623 #-}
   rule1623 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1624 #-}
   rule1624 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1625 #-}
   rule1625 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1626 #-}
   rule1626 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1627 #-}
   rule1627 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1628 #-}
   rule1628 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1629 #-}
   rule1629 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1630 #-}
   rule1630 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1631 #-}
   rule1631 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1632 #-}
   rule1632 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1633 #-}
   rule1633 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1634 #-}
   rule1634 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1635 #-}
   rule1635 = \ ((_hdIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _hdIcollectScopeInfos
   {-# INLINE rule1636 #-}
   rule1636 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule1637 #-}
   rule1637 = \ ((_hdIkindErrors) :: [Error]) ->
     _hdIkindErrors
   {-# INLINE rule1638 #-}
   rule1638 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule1639 #-}
   rule1639 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1640 #-}
   rule1640 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1641 #-}
   rule1641 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1642 #-}
   rule1642 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1643 #-}
   rule1643 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1644 #-}
   rule1644 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_FunctionBindings_Nil #-}
sem_FunctionBindings_Nil ::  T_FunctionBindings 
sem_FunctionBindings_Nil  = T_FunctionBindings (return st59) where
   {-# NOINLINE st59 #-}
   st59 = let
      v58 :: T_FunctionBindings_v58 
      v58 = \ (T_FunctionBindings_vIn58 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOname :: Name
         _lhsOname = rule1645  ()
         _lhsOarities ::  [Int] 
         _lhsOarities = rule1646  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1647  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1648  ()
         _self = rule1649  ()
         _lhsOself :: FunctionBindings
         _lhsOself = rule1650 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1651 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1652 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1653 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1654 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1655 _lhsIwarnings
         __result_ = T_FunctionBindings_vOut58 _lhsOarities _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOname _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_FunctionBindings_s59 v58
   {-# INLINE rule1645 #-}
   rule1645 = \  (_ :: ()) ->
                         internalError "StaticChecks.ag" "n/a" "empty FunctionBindings"
   {-# INLINE rule1646 #-}
   rule1646 = \  (_ :: ()) ->
                         []
   {-# INLINE rule1647 #-}
   rule1647 = \  (_ :: ()) ->
     []
   {-# INLINE rule1648 #-}
   rule1648 = \  (_ :: ()) ->
     []
   {-# INLINE rule1649 #-}
   rule1649 = \  (_ :: ()) ->
     []
   {-# INLINE rule1650 #-}
   rule1650 = \ _self ->
     _self
   {-# INLINE rule1651 #-}
   rule1651 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1652 #-}
   rule1652 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1653 #-}
   rule1653 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1654 #-}
   rule1654 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1655 #-}
   rule1655 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- GuardedExpression -------------------------------------------
-- wrapper
data Inh_GuardedExpression  = Inh_GuardedExpression { allTypeConstructors_Inh_GuardedExpression :: (Names), allValueConstructors_Inh_GuardedExpression :: (Names), classEnvironment_Inh_GuardedExpression :: (ClassEnvironment), collectScopeInfos_Inh_GuardedExpression :: ([(ScopeInfo, Entity)]), counter_Inh_GuardedExpression :: (Int), kindErrors_Inh_GuardedExpression :: ([Error]), miscerrors_Inh_GuardedExpression :: ([Error]), namesInScope_Inh_GuardedExpression :: (Names), options_Inh_GuardedExpression :: ([Option]), orderedTypeSynonyms_Inh_GuardedExpression :: (OrderedTypeSynonyms), typeConstructors_Inh_GuardedExpression :: (M.Map Name Int), valueConstructors_Inh_GuardedExpression :: (M.Map Name TpScheme), warnings_Inh_GuardedExpression :: ([Warning]) }
data Syn_GuardedExpression  = Syn_GuardedExpression { collectInstances_Syn_GuardedExpression :: ([(Name, Instance)]), collectScopeInfos_Syn_GuardedExpression :: ([(ScopeInfo, Entity)]), counter_Syn_GuardedExpression :: (Int), kindErrors_Syn_GuardedExpression :: ([Error]), miscerrors_Syn_GuardedExpression :: ([Error]), self_Syn_GuardedExpression :: (GuardedExpression), unboundNames_Syn_GuardedExpression :: (Names), warnings_Syn_GuardedExpression :: ([Warning]) }
{-# INLINABLE wrap_GuardedExpression #-}
wrap_GuardedExpression :: T_GuardedExpression  -> Inh_GuardedExpression  -> (Syn_GuardedExpression )
wrap_GuardedExpression (T_GuardedExpression act) (Inh_GuardedExpression _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_GuardedExpression_vIn61 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_GuardedExpression_vOut61 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_GuardedExpression_s62 sem arg)
        return (Syn_GuardedExpression _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_GuardedExpression #-}
sem_GuardedExpression :: GuardedExpression  -> T_GuardedExpression 
sem_GuardedExpression ( GuardedExpression_GuardedExpression range_ guard_ expression_ ) = sem_GuardedExpression_GuardedExpression ( sem_Range range_ ) ( sem_Expression guard_ ) ( sem_Expression expression_ )

-- semantic domain
newtype T_GuardedExpression  = T_GuardedExpression {
                                                   attach_T_GuardedExpression :: Identity (T_GuardedExpression_s62 )
                                                   }
newtype T_GuardedExpression_s62  = C_GuardedExpression_s62 {
                                                           inv_GuardedExpression_s62 :: (T_GuardedExpression_v61 )
                                                           }
data T_GuardedExpression_s63  = C_GuardedExpression_s63
type T_GuardedExpression_v61  = (T_GuardedExpression_vIn61 ) -> (T_GuardedExpression_vOut61 )
data T_GuardedExpression_vIn61  = T_GuardedExpression_vIn61 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_GuardedExpression_vOut61  = T_GuardedExpression_vOut61 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (GuardedExpression) (Names) ([Warning])
{-# NOINLINE sem_GuardedExpression_GuardedExpression #-}
sem_GuardedExpression_GuardedExpression :: T_Range  -> T_Expression  -> T_Expression  -> T_GuardedExpression 
sem_GuardedExpression_GuardedExpression arg_range_ arg_guard_ arg_expression_ = T_GuardedExpression (return st62) where
   {-# NOINLINE st62 #-}
   st62 = let
      v61 :: T_GuardedExpression_v61 
      v61 = \ (T_GuardedExpression_vIn61 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_guard_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _guardIcollectInstances _guardIcollectScopeInfos _guardIcounter _guardIkindErrors _guardImiscerrors _guardIself _guardIunboundNames _guardIwarnings) = inv_Expression_s41 _guardX41 (T_Expression_vIn40 _guardOallTypeConstructors _guardOallValueConstructors _guardOclassEnvironment _guardOcollectScopeInfos _guardOcounter _guardOkindErrors _guardOmiscerrors _guardOnamesInScope _guardOoptions _guardOorderedTypeSynonyms _guardOtypeConstructors _guardOvalueConstructors _guardOwarnings)
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1656 _expressionIcollectInstances _guardIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1657 _expressionIunboundNames _guardIunboundNames
         _self = rule1658 _expressionIself _guardIself _rangeIself
         _lhsOself :: GuardedExpression
         _lhsOself = rule1659 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1660 _expressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1661 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1662 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1663 _expressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1664 _expressionIwarnings
         _guardOallTypeConstructors = rule1665 _lhsIallTypeConstructors
         _guardOallValueConstructors = rule1666 _lhsIallValueConstructors
         _guardOclassEnvironment = rule1667 _lhsIclassEnvironment
         _guardOcollectScopeInfos = rule1668 _lhsIcollectScopeInfos
         _guardOcounter = rule1669 _lhsIcounter
         _guardOkindErrors = rule1670 _lhsIkindErrors
         _guardOmiscerrors = rule1671 _lhsImiscerrors
         _guardOnamesInScope = rule1672 _lhsInamesInScope
         _guardOoptions = rule1673 _lhsIoptions
         _guardOorderedTypeSynonyms = rule1674 _lhsIorderedTypeSynonyms
         _guardOtypeConstructors = rule1675 _lhsItypeConstructors
         _guardOvalueConstructors = rule1676 _lhsIvalueConstructors
         _guardOwarnings = rule1677 _lhsIwarnings
         _expressionOallTypeConstructors = rule1678 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule1679 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule1680 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule1681 _guardIcollectScopeInfos
         _expressionOcounter = rule1682 _guardIcounter
         _expressionOkindErrors = rule1683 _guardIkindErrors
         _expressionOmiscerrors = rule1684 _guardImiscerrors
         _expressionOnamesInScope = rule1685 _lhsInamesInScope
         _expressionOoptions = rule1686 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule1687 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule1688 _lhsItypeConstructors
         _expressionOvalueConstructors = rule1689 _lhsIvalueConstructors
         _expressionOwarnings = rule1690 _guardIwarnings
         __result_ = T_GuardedExpression_vOut61 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_GuardedExpression_s62 v61
   {-# INLINE rule1656 #-}
   rule1656 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ((_guardIcollectInstances) :: [(Name, Instance)]) ->
     _guardIcollectInstances  ++  _expressionIcollectInstances
   {-# INLINE rule1657 #-}
   rule1657 = \ ((_expressionIunboundNames) :: Names) ((_guardIunboundNames) :: Names) ->
     _guardIunboundNames ++ _expressionIunboundNames
   {-# INLINE rule1658 #-}
   rule1658 = \ ((_expressionIself) :: Expression) ((_guardIself) :: Expression) ((_rangeIself) :: Range) ->
     GuardedExpression_GuardedExpression _rangeIself _guardIself _expressionIself
   {-# INLINE rule1659 #-}
   rule1659 = \ _self ->
     _self
   {-# INLINE rule1660 #-}
   rule1660 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule1661 #-}
   rule1661 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule1662 #-}
   rule1662 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule1663 #-}
   rule1663 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule1664 #-}
   rule1664 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule1665 #-}
   rule1665 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1666 #-}
   rule1666 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1667 #-}
   rule1667 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1668 #-}
   rule1668 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1669 #-}
   rule1669 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1670 #-}
   rule1670 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1671 #-}
   rule1671 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1672 #-}
   rule1672 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1673 #-}
   rule1673 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1674 #-}
   rule1674 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1675 #-}
   rule1675 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1676 #-}
   rule1676 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1677 #-}
   rule1677 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1678 #-}
   rule1678 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1679 #-}
   rule1679 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1680 #-}
   rule1680 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1681 #-}
   rule1681 = \ ((_guardIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _guardIcollectScopeInfos
   {-# INLINE rule1682 #-}
   rule1682 = \ ((_guardIcounter) :: Int) ->
     _guardIcounter
   {-# INLINE rule1683 #-}
   rule1683 = \ ((_guardIkindErrors) :: [Error]) ->
     _guardIkindErrors
   {-# INLINE rule1684 #-}
   rule1684 = \ ((_guardImiscerrors) :: [Error]) ->
     _guardImiscerrors
   {-# INLINE rule1685 #-}
   rule1685 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1686 #-}
   rule1686 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1687 #-}
   rule1687 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1688 #-}
   rule1688 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1689 #-}
   rule1689 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1690 #-}
   rule1690 = \ ((_guardIwarnings) :: [Warning]) ->
     _guardIwarnings

-- GuardedExpressions ------------------------------------------
-- wrapper
data Inh_GuardedExpressions  = Inh_GuardedExpressions { allTypeConstructors_Inh_GuardedExpressions :: (Names), allValueConstructors_Inh_GuardedExpressions :: (Names), classEnvironment_Inh_GuardedExpressions :: (ClassEnvironment), collectScopeInfos_Inh_GuardedExpressions :: ([(ScopeInfo, Entity)]), counter_Inh_GuardedExpressions :: (Int), kindErrors_Inh_GuardedExpressions :: ([Error]), miscerrors_Inh_GuardedExpressions :: ([Error]), namesInScope_Inh_GuardedExpressions :: (Names), options_Inh_GuardedExpressions :: ([Option]), orderedTypeSynonyms_Inh_GuardedExpressions :: (OrderedTypeSynonyms), typeConstructors_Inh_GuardedExpressions :: (M.Map Name Int), valueConstructors_Inh_GuardedExpressions :: (M.Map Name TpScheme), warnings_Inh_GuardedExpressions :: ([Warning]) }
data Syn_GuardedExpressions  = Syn_GuardedExpressions { collectInstances_Syn_GuardedExpressions :: ([(Name, Instance)]), collectScopeInfos_Syn_GuardedExpressions :: ([(ScopeInfo, Entity)]), counter_Syn_GuardedExpressions :: (Int), kindErrors_Syn_GuardedExpressions :: ([Error]), miscerrors_Syn_GuardedExpressions :: ([Error]), self_Syn_GuardedExpressions :: (GuardedExpressions), unboundNames_Syn_GuardedExpressions :: (Names), warnings_Syn_GuardedExpressions :: ([Warning]) }
{-# INLINABLE wrap_GuardedExpressions #-}
wrap_GuardedExpressions :: T_GuardedExpressions  -> Inh_GuardedExpressions  -> (Syn_GuardedExpressions )
wrap_GuardedExpressions (T_GuardedExpressions act) (Inh_GuardedExpressions _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_GuardedExpressions_vIn64 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_GuardedExpressions_vOut64 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_GuardedExpressions_s65 sem arg)
        return (Syn_GuardedExpressions _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_GuardedExpressions #-}
sem_GuardedExpressions :: GuardedExpressions  -> T_GuardedExpressions 
sem_GuardedExpressions list = Prelude.foldr sem_GuardedExpressions_Cons sem_GuardedExpressions_Nil (Prelude.map sem_GuardedExpression list)

-- semantic domain
newtype T_GuardedExpressions  = T_GuardedExpressions {
                                                     attach_T_GuardedExpressions :: Identity (T_GuardedExpressions_s65 )
                                                     }
newtype T_GuardedExpressions_s65  = C_GuardedExpressions_s65 {
                                                             inv_GuardedExpressions_s65 :: (T_GuardedExpressions_v64 )
                                                             }
data T_GuardedExpressions_s66  = C_GuardedExpressions_s66
type T_GuardedExpressions_v64  = (T_GuardedExpressions_vIn64 ) -> (T_GuardedExpressions_vOut64 )
data T_GuardedExpressions_vIn64  = T_GuardedExpressions_vIn64 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_GuardedExpressions_vOut64  = T_GuardedExpressions_vOut64 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (GuardedExpressions) (Names) ([Warning])
{-# NOINLINE sem_GuardedExpressions_Cons #-}
sem_GuardedExpressions_Cons :: T_GuardedExpression  -> T_GuardedExpressions  -> T_GuardedExpressions 
sem_GuardedExpressions_Cons arg_hd_ arg_tl_ = T_GuardedExpressions (return st65) where
   {-# NOINLINE st65 #-}
   st65 = let
      v64 :: T_GuardedExpressions_v64 
      v64 = \ (T_GuardedExpressions_vIn64 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _hdX62 = Control.Monad.Identity.runIdentity (attach_T_GuardedExpression (arg_hd_))
         _tlX65 = Control.Monad.Identity.runIdentity (attach_T_GuardedExpressions (arg_tl_))
         (T_GuardedExpression_vOut61 _hdIcollectInstances _hdIcollectScopeInfos _hdIcounter _hdIkindErrors _hdImiscerrors _hdIself _hdIunboundNames _hdIwarnings) = inv_GuardedExpression_s62 _hdX62 (T_GuardedExpression_vIn61 _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOcounter _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings)
         (T_GuardedExpressions_vOut64 _tlIcollectInstances _tlIcollectScopeInfos _tlIcounter _tlIkindErrors _tlImiscerrors _tlIself _tlIunboundNames _tlIwarnings) = inv_GuardedExpressions_s65 _tlX65 (T_GuardedExpressions_vIn64 _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOcounter _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1691 _hdIcollectInstances _tlIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1692 _hdIunboundNames _tlIunboundNames
         _self = rule1693 _hdIself _tlIself
         _lhsOself :: GuardedExpressions
         _lhsOself = rule1694 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1695 _tlIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1696 _tlIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1697 _tlIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1698 _tlImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1699 _tlIwarnings
         _hdOallTypeConstructors = rule1700 _lhsIallTypeConstructors
         _hdOallValueConstructors = rule1701 _lhsIallValueConstructors
         _hdOclassEnvironment = rule1702 _lhsIclassEnvironment
         _hdOcollectScopeInfos = rule1703 _lhsIcollectScopeInfos
         _hdOcounter = rule1704 _lhsIcounter
         _hdOkindErrors = rule1705 _lhsIkindErrors
         _hdOmiscerrors = rule1706 _lhsImiscerrors
         _hdOnamesInScope = rule1707 _lhsInamesInScope
         _hdOoptions = rule1708 _lhsIoptions
         _hdOorderedTypeSynonyms = rule1709 _lhsIorderedTypeSynonyms
         _hdOtypeConstructors = rule1710 _lhsItypeConstructors
         _hdOvalueConstructors = rule1711 _lhsIvalueConstructors
         _hdOwarnings = rule1712 _lhsIwarnings
         _tlOallTypeConstructors = rule1713 _lhsIallTypeConstructors
         _tlOallValueConstructors = rule1714 _lhsIallValueConstructors
         _tlOclassEnvironment = rule1715 _lhsIclassEnvironment
         _tlOcollectScopeInfos = rule1716 _hdIcollectScopeInfos
         _tlOcounter = rule1717 _hdIcounter
         _tlOkindErrors = rule1718 _hdIkindErrors
         _tlOmiscerrors = rule1719 _hdImiscerrors
         _tlOnamesInScope = rule1720 _lhsInamesInScope
         _tlOoptions = rule1721 _lhsIoptions
         _tlOorderedTypeSynonyms = rule1722 _lhsIorderedTypeSynonyms
         _tlOtypeConstructors = rule1723 _lhsItypeConstructors
         _tlOvalueConstructors = rule1724 _lhsIvalueConstructors
         _tlOwarnings = rule1725 _hdIwarnings
         __result_ = T_GuardedExpressions_vOut64 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_GuardedExpressions_s65 v64
   {-# INLINE rule1691 #-}
   rule1691 = \ ((_hdIcollectInstances) :: [(Name, Instance)]) ((_tlIcollectInstances) :: [(Name, Instance)]) ->
     _hdIcollectInstances  ++  _tlIcollectInstances
   {-# INLINE rule1692 #-}
   rule1692 = \ ((_hdIunboundNames) :: Names) ((_tlIunboundNames) :: Names) ->
     _hdIunboundNames ++ _tlIunboundNames
   {-# INLINE rule1693 #-}
   rule1693 = \ ((_hdIself) :: GuardedExpression) ((_tlIself) :: GuardedExpressions) ->
     (:) _hdIself _tlIself
   {-# INLINE rule1694 #-}
   rule1694 = \ _self ->
     _self
   {-# INLINE rule1695 #-}
   rule1695 = \ ((_tlIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _tlIcollectScopeInfos
   {-# INLINE rule1696 #-}
   rule1696 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule1697 #-}
   rule1697 = \ ((_tlIkindErrors) :: [Error]) ->
     _tlIkindErrors
   {-# INLINE rule1698 #-}
   rule1698 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule1699 #-}
   rule1699 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule1700 #-}
   rule1700 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1701 #-}
   rule1701 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1702 #-}
   rule1702 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1703 #-}
   rule1703 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1704 #-}
   rule1704 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1705 #-}
   rule1705 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1706 #-}
   rule1706 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1707 #-}
   rule1707 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1708 #-}
   rule1708 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1709 #-}
   rule1709 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1710 #-}
   rule1710 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1711 #-}
   rule1711 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1712 #-}
   rule1712 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1713 #-}
   rule1713 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1714 #-}
   rule1714 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1715 #-}
   rule1715 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1716 #-}
   rule1716 = \ ((_hdIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _hdIcollectScopeInfos
   {-# INLINE rule1717 #-}
   rule1717 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule1718 #-}
   rule1718 = \ ((_hdIkindErrors) :: [Error]) ->
     _hdIkindErrors
   {-# INLINE rule1719 #-}
   rule1719 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule1720 #-}
   rule1720 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1721 #-}
   rule1721 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1722 #-}
   rule1722 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1723 #-}
   rule1723 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1724 #-}
   rule1724 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1725 #-}
   rule1725 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_GuardedExpressions_Nil #-}
sem_GuardedExpressions_Nil ::  T_GuardedExpressions 
sem_GuardedExpressions_Nil  = T_GuardedExpressions (return st65) where
   {-# NOINLINE st65 #-}
   st65 = let
      v64 :: T_GuardedExpressions_v64 
      v64 = \ (T_GuardedExpressions_vIn64 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1726  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1727  ()
         _self = rule1728  ()
         _lhsOself :: GuardedExpressions
         _lhsOself = rule1729 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1730 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1731 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1732 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1733 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1734 _lhsIwarnings
         __result_ = T_GuardedExpressions_vOut64 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_GuardedExpressions_s65 v64
   {-# INLINE rule1726 #-}
   rule1726 = \  (_ :: ()) ->
     []
   {-# INLINE rule1727 #-}
   rule1727 = \  (_ :: ()) ->
     []
   {-# INLINE rule1728 #-}
   rule1728 = \  (_ :: ()) ->
     []
   {-# INLINE rule1729 #-}
   rule1729 = \ _self ->
     _self
   {-# INLINE rule1730 #-}
   rule1730 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1731 #-}
   rule1731 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1732 #-}
   rule1732 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1733 #-}
   rule1733 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1734 #-}
   rule1734 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Import ------------------------------------------------------
-- wrapper
data Inh_Import  = Inh_Import {  }
data Syn_Import  = Syn_Import { self_Syn_Import :: (Import) }
{-# INLINABLE wrap_Import #-}
wrap_Import :: T_Import  -> Inh_Import  -> (Syn_Import )
wrap_Import (T_Import act) (Inh_Import ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Import_vIn67 
        (T_Import_vOut67 _lhsOself) <- return (inv_Import_s68 sem arg)
        return (Syn_Import _lhsOself)
   )

-- cata
{-# NOINLINE sem_Import #-}
sem_Import :: Import  -> T_Import 
sem_Import ( Import_Variable range_ name_ ) = sem_Import_Variable ( sem_Range range_ ) ( sem_Name name_ )
sem_Import ( Import_TypeOrClass range_ name_ names_ ) = sem_Import_TypeOrClass ( sem_Range range_ ) ( sem_Name name_ ) ( sem_MaybeNames names_ )
sem_Import ( Import_TypeOrClassComplete range_ name_ ) = sem_Import_TypeOrClassComplete ( sem_Range range_ ) ( sem_Name name_ )

-- semantic domain
newtype T_Import  = T_Import {
                             attach_T_Import :: Identity (T_Import_s68 )
                             }
newtype T_Import_s68  = C_Import_s68 {
                                     inv_Import_s68 :: (T_Import_v67 )
                                     }
data T_Import_s69  = C_Import_s69
type T_Import_v67  = (T_Import_vIn67 ) -> (T_Import_vOut67 )
data T_Import_vIn67  = T_Import_vIn67 
data T_Import_vOut67  = T_Import_vOut67 (Import)
{-# NOINLINE sem_Import_Variable #-}
sem_Import_Variable :: T_Range  -> T_Name  -> T_Import 
sem_Import_Variable arg_range_ arg_name_ = T_Import (return st68) where
   {-# NOINLINE st68 #-}
   st68 = let
      v67 :: T_Import_v67 
      v67 = \ (T_Import_vIn67 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _self = rule1735 _nameIself _rangeIself
         _lhsOself :: Import
         _lhsOself = rule1736 _self
         __result_ = T_Import_vOut67 _lhsOself
         in __result_ )
     in C_Import_s68 v67
   {-# INLINE rule1735 #-}
   rule1735 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Import_Variable _rangeIself _nameIself
   {-# INLINE rule1736 #-}
   rule1736 = \ _self ->
     _self
{-# NOINLINE sem_Import_TypeOrClass #-}
sem_Import_TypeOrClass :: T_Range  -> T_Name  -> T_MaybeNames  -> T_Import 
sem_Import_TypeOrClass arg_range_ arg_name_ arg_names_ = T_Import (return st68) where
   {-# NOINLINE st68 #-}
   st68 = let
      v67 :: T_Import_v67 
      v67 = \ (T_Import_vIn67 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _namesX107 = Control.Monad.Identity.runIdentity (attach_T_MaybeNames (arg_names_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_MaybeNames_vOut106 _namesIself) = inv_MaybeNames_s107 _namesX107 (T_MaybeNames_vIn106 )
         _self = rule1737 _nameIself _namesIself _rangeIself
         _lhsOself :: Import
         _lhsOself = rule1738 _self
         __result_ = T_Import_vOut67 _lhsOself
         in __result_ )
     in C_Import_s68 v67
   {-# INLINE rule1737 #-}
   rule1737 = \ ((_nameIself) :: Name) ((_namesIself) :: MaybeNames) ((_rangeIself) :: Range) ->
     Import_TypeOrClass _rangeIself _nameIself _namesIself
   {-# INLINE rule1738 #-}
   rule1738 = \ _self ->
     _self
{-# NOINLINE sem_Import_TypeOrClassComplete #-}
sem_Import_TypeOrClassComplete :: T_Range  -> T_Name  -> T_Import 
sem_Import_TypeOrClassComplete arg_range_ arg_name_ = T_Import (return st68) where
   {-# NOINLINE st68 #-}
   st68 = let
      v67 :: T_Import_v67 
      v67 = \ (T_Import_vIn67 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _self = rule1739 _nameIself _rangeIself
         _lhsOself :: Import
         _lhsOself = rule1740 _self
         __result_ = T_Import_vOut67 _lhsOself
         in __result_ )
     in C_Import_s68 v67
   {-# INLINE rule1739 #-}
   rule1739 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Import_TypeOrClassComplete _rangeIself _nameIself
   {-# INLINE rule1740 #-}
   rule1740 = \ _self ->
     _self

-- ImportDeclaration -------------------------------------------
-- wrapper
data Inh_ImportDeclaration  = Inh_ImportDeclaration { importedModules_Inh_ImportDeclaration :: (Names) }
data Syn_ImportDeclaration  = Syn_ImportDeclaration { importedModules_Syn_ImportDeclaration :: (Names), self_Syn_ImportDeclaration :: (ImportDeclaration) }
{-# INLINABLE wrap_ImportDeclaration #-}
wrap_ImportDeclaration :: T_ImportDeclaration  -> Inh_ImportDeclaration  -> (Syn_ImportDeclaration )
wrap_ImportDeclaration (T_ImportDeclaration act) (Inh_ImportDeclaration _lhsIimportedModules) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_ImportDeclaration_vIn70 _lhsIimportedModules
        (T_ImportDeclaration_vOut70 _lhsOimportedModules _lhsOself) <- return (inv_ImportDeclaration_s71 sem arg)
        return (Syn_ImportDeclaration _lhsOimportedModules _lhsOself)
   )

-- cata
{-# NOINLINE sem_ImportDeclaration #-}
sem_ImportDeclaration :: ImportDeclaration  -> T_ImportDeclaration 
sem_ImportDeclaration ( ImportDeclaration_Import range_ qualified_ name_ asname_ importspecification_ ) = sem_ImportDeclaration_Import ( sem_Range range_ ) qualified_ ( sem_Name name_ ) ( sem_MaybeName asname_ ) ( sem_MaybeImportSpecification importspecification_ )
sem_ImportDeclaration ( ImportDeclaration_Empty range_ ) = sem_ImportDeclaration_Empty ( sem_Range range_ )

-- semantic domain
newtype T_ImportDeclaration  = T_ImportDeclaration {
                                                   attach_T_ImportDeclaration :: Identity (T_ImportDeclaration_s71 )
                                                   }
newtype T_ImportDeclaration_s71  = C_ImportDeclaration_s71 {
                                                           inv_ImportDeclaration_s71 :: (T_ImportDeclaration_v70 )
                                                           }
data T_ImportDeclaration_s72  = C_ImportDeclaration_s72
type T_ImportDeclaration_v70  = (T_ImportDeclaration_vIn70 ) -> (T_ImportDeclaration_vOut70 )
data T_ImportDeclaration_vIn70  = T_ImportDeclaration_vIn70 (Names)
data T_ImportDeclaration_vOut70  = T_ImportDeclaration_vOut70 (Names) (ImportDeclaration)
{-# NOINLINE sem_ImportDeclaration_Import #-}
sem_ImportDeclaration_Import :: T_Range  -> (Bool) -> T_Name  -> T_MaybeName  -> T_MaybeImportSpecification  -> T_ImportDeclaration 
sem_ImportDeclaration_Import arg_range_ arg_qualified_ arg_name_ arg_asname_ arg_importspecification_ = T_ImportDeclaration (return st71) where
   {-# NOINLINE st71 #-}
   st71 = let
      v70 :: T_ImportDeclaration_v70 
      v70 = \ (T_ImportDeclaration_vIn70 _lhsIimportedModules) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _asnameX104 = Control.Monad.Identity.runIdentity (attach_T_MaybeName (arg_asname_))
         _importspecificationX98 = Control.Monad.Identity.runIdentity (attach_T_MaybeImportSpecification (arg_importspecification_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_MaybeName_vOut103 _asnameIself) = inv_MaybeName_s104 _asnameX104 (T_MaybeName_vIn103 )
         (T_MaybeImportSpecification_vOut97 _importspecificationIself) = inv_MaybeImportSpecification_s98 _importspecificationX98 (T_MaybeImportSpecification_vIn97 )
         _lhsOimportedModules :: Names
         _lhsOimportedModules = rule1741 _lhsIimportedModules _nameIself
         _self = rule1742 _asnameIself _importspecificationIself _nameIself _rangeIself arg_qualified_
         _lhsOself :: ImportDeclaration
         _lhsOself = rule1743 _self
         __result_ = T_ImportDeclaration_vOut70 _lhsOimportedModules _lhsOself
         in __result_ )
     in C_ImportDeclaration_s71 v70
   {-# INLINE rule1741 #-}
   rule1741 = \ ((_lhsIimportedModules) :: Names) ((_nameIself) :: Name) ->
                                       _nameIself : _lhsIimportedModules
   {-# INLINE rule1742 #-}
   rule1742 = \ ((_asnameIself) :: MaybeName) ((_importspecificationIself) :: MaybeImportSpecification) ((_nameIself) :: Name) ((_rangeIself) :: Range) qualified_ ->
     ImportDeclaration_Import _rangeIself qualified_ _nameIself _asnameIself _importspecificationIself
   {-# INLINE rule1743 #-}
   rule1743 = \ _self ->
     _self
{-# NOINLINE sem_ImportDeclaration_Empty #-}
sem_ImportDeclaration_Empty :: T_Range  -> T_ImportDeclaration 
sem_ImportDeclaration_Empty arg_range_ = T_ImportDeclaration (return st71) where
   {-# NOINLINE st71 #-}
   st71 = let
      v70 :: T_ImportDeclaration_v70 
      v70 = \ (T_ImportDeclaration_vIn70 _lhsIimportedModules) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _self = rule1744 _rangeIself
         _lhsOself :: ImportDeclaration
         _lhsOself = rule1745 _self
         _lhsOimportedModules :: Names
         _lhsOimportedModules = rule1746 _lhsIimportedModules
         __result_ = T_ImportDeclaration_vOut70 _lhsOimportedModules _lhsOself
         in __result_ )
     in C_ImportDeclaration_s71 v70
   {-# INLINE rule1744 #-}
   rule1744 = \ ((_rangeIself) :: Range) ->
     ImportDeclaration_Empty _rangeIself
   {-# INLINE rule1745 #-}
   rule1745 = \ _self ->
     _self
   {-# INLINE rule1746 #-}
   rule1746 = \ ((_lhsIimportedModules) :: Names) ->
     _lhsIimportedModules

-- ImportDeclarations ------------------------------------------
-- wrapper
data Inh_ImportDeclarations  = Inh_ImportDeclarations { importedModules_Inh_ImportDeclarations :: (Names) }
data Syn_ImportDeclarations  = Syn_ImportDeclarations { importedModules_Syn_ImportDeclarations :: (Names), self_Syn_ImportDeclarations :: (ImportDeclarations) }
{-# INLINABLE wrap_ImportDeclarations #-}
wrap_ImportDeclarations :: T_ImportDeclarations  -> Inh_ImportDeclarations  -> (Syn_ImportDeclarations )
wrap_ImportDeclarations (T_ImportDeclarations act) (Inh_ImportDeclarations _lhsIimportedModules) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_ImportDeclarations_vIn73 _lhsIimportedModules
        (T_ImportDeclarations_vOut73 _lhsOimportedModules _lhsOself) <- return (inv_ImportDeclarations_s74 sem arg)
        return (Syn_ImportDeclarations _lhsOimportedModules _lhsOself)
   )

-- cata
{-# NOINLINE sem_ImportDeclarations #-}
sem_ImportDeclarations :: ImportDeclarations  -> T_ImportDeclarations 
sem_ImportDeclarations list = Prelude.foldr sem_ImportDeclarations_Cons sem_ImportDeclarations_Nil (Prelude.map sem_ImportDeclaration list)

-- semantic domain
newtype T_ImportDeclarations  = T_ImportDeclarations {
                                                     attach_T_ImportDeclarations :: Identity (T_ImportDeclarations_s74 )
                                                     }
newtype T_ImportDeclarations_s74  = C_ImportDeclarations_s74 {
                                                             inv_ImportDeclarations_s74 :: (T_ImportDeclarations_v73 )
                                                             }
data T_ImportDeclarations_s75  = C_ImportDeclarations_s75
type T_ImportDeclarations_v73  = (T_ImportDeclarations_vIn73 ) -> (T_ImportDeclarations_vOut73 )
data T_ImportDeclarations_vIn73  = T_ImportDeclarations_vIn73 (Names)
data T_ImportDeclarations_vOut73  = T_ImportDeclarations_vOut73 (Names) (ImportDeclarations)
{-# NOINLINE sem_ImportDeclarations_Cons #-}
sem_ImportDeclarations_Cons :: T_ImportDeclaration  -> T_ImportDeclarations  -> T_ImportDeclarations 
sem_ImportDeclarations_Cons arg_hd_ arg_tl_ = T_ImportDeclarations (return st74) where
   {-# NOINLINE st74 #-}
   st74 = let
      v73 :: T_ImportDeclarations_v73 
      v73 = \ (T_ImportDeclarations_vIn73 _lhsIimportedModules) -> ( let
         _hdX71 = Control.Monad.Identity.runIdentity (attach_T_ImportDeclaration (arg_hd_))
         _tlX74 = Control.Monad.Identity.runIdentity (attach_T_ImportDeclarations (arg_tl_))
         (T_ImportDeclaration_vOut70 _hdIimportedModules _hdIself) = inv_ImportDeclaration_s71 _hdX71 (T_ImportDeclaration_vIn70 _hdOimportedModules)
         (T_ImportDeclarations_vOut73 _tlIimportedModules _tlIself) = inv_ImportDeclarations_s74 _tlX74 (T_ImportDeclarations_vIn73 _tlOimportedModules)
         _self = rule1747 _hdIself _tlIself
         _lhsOself :: ImportDeclarations
         _lhsOself = rule1748 _self
         _lhsOimportedModules :: Names
         _lhsOimportedModules = rule1749 _tlIimportedModules
         _hdOimportedModules = rule1750 _lhsIimportedModules
         _tlOimportedModules = rule1751 _hdIimportedModules
         __result_ = T_ImportDeclarations_vOut73 _lhsOimportedModules _lhsOself
         in __result_ )
     in C_ImportDeclarations_s74 v73
   {-# INLINE rule1747 #-}
   rule1747 = \ ((_hdIself) :: ImportDeclaration) ((_tlIself) :: ImportDeclarations) ->
     (:) _hdIself _tlIself
   {-# INLINE rule1748 #-}
   rule1748 = \ _self ->
     _self
   {-# INLINE rule1749 #-}
   rule1749 = \ ((_tlIimportedModules) :: Names) ->
     _tlIimportedModules
   {-# INLINE rule1750 #-}
   rule1750 = \ ((_lhsIimportedModules) :: Names) ->
     _lhsIimportedModules
   {-# INLINE rule1751 #-}
   rule1751 = \ ((_hdIimportedModules) :: Names) ->
     _hdIimportedModules
{-# NOINLINE sem_ImportDeclarations_Nil #-}
sem_ImportDeclarations_Nil ::  T_ImportDeclarations 
sem_ImportDeclarations_Nil  = T_ImportDeclarations (return st74) where
   {-# NOINLINE st74 #-}
   st74 = let
      v73 :: T_ImportDeclarations_v73 
      v73 = \ (T_ImportDeclarations_vIn73 _lhsIimportedModules) -> ( let
         _self = rule1752  ()
         _lhsOself :: ImportDeclarations
         _lhsOself = rule1753 _self
         _lhsOimportedModules :: Names
         _lhsOimportedModules = rule1754 _lhsIimportedModules
         __result_ = T_ImportDeclarations_vOut73 _lhsOimportedModules _lhsOself
         in __result_ )
     in C_ImportDeclarations_s74 v73
   {-# INLINE rule1752 #-}
   rule1752 = \  (_ :: ()) ->
     []
   {-# INLINE rule1753 #-}
   rule1753 = \ _self ->
     _self
   {-# INLINE rule1754 #-}
   rule1754 = \ ((_lhsIimportedModules) :: Names) ->
     _lhsIimportedModules

-- ImportSpecification -----------------------------------------
-- wrapper
data Inh_ImportSpecification  = Inh_ImportSpecification {  }
data Syn_ImportSpecification  = Syn_ImportSpecification { self_Syn_ImportSpecification :: (ImportSpecification) }
{-# INLINABLE wrap_ImportSpecification #-}
wrap_ImportSpecification :: T_ImportSpecification  -> Inh_ImportSpecification  -> (Syn_ImportSpecification )
wrap_ImportSpecification (T_ImportSpecification act) (Inh_ImportSpecification ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_ImportSpecification_vIn76 
        (T_ImportSpecification_vOut76 _lhsOself) <- return (inv_ImportSpecification_s77 sem arg)
        return (Syn_ImportSpecification _lhsOself)
   )

-- cata
{-# INLINE sem_ImportSpecification #-}
sem_ImportSpecification :: ImportSpecification  -> T_ImportSpecification 
sem_ImportSpecification ( ImportSpecification_Import range_ hiding_ imports_ ) = sem_ImportSpecification_Import ( sem_Range range_ ) hiding_ ( sem_Imports imports_ )

-- semantic domain
newtype T_ImportSpecification  = T_ImportSpecification {
                                                       attach_T_ImportSpecification :: Identity (T_ImportSpecification_s77 )
                                                       }
newtype T_ImportSpecification_s77  = C_ImportSpecification_s77 {
                                                               inv_ImportSpecification_s77 :: (T_ImportSpecification_v76 )
                                                               }
data T_ImportSpecification_s78  = C_ImportSpecification_s78
type T_ImportSpecification_v76  = (T_ImportSpecification_vIn76 ) -> (T_ImportSpecification_vOut76 )
data T_ImportSpecification_vIn76  = T_ImportSpecification_vIn76 
data T_ImportSpecification_vOut76  = T_ImportSpecification_vOut76 (ImportSpecification)
{-# NOINLINE sem_ImportSpecification_Import #-}
sem_ImportSpecification_Import :: T_Range  -> (Bool) -> T_Imports  -> T_ImportSpecification 
sem_ImportSpecification_Import arg_range_ arg_hiding_ arg_imports_ = T_ImportSpecification (return st77) where
   {-# NOINLINE st77 #-}
   st77 = let
      v76 :: T_ImportSpecification_v76 
      v76 = \ (T_ImportSpecification_vIn76 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _importsX80 = Control.Monad.Identity.runIdentity (attach_T_Imports (arg_imports_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Imports_vOut79 _importsIself) = inv_Imports_s80 _importsX80 (T_Imports_vIn79 )
         _self = rule1755 _importsIself _rangeIself arg_hiding_
         _lhsOself :: ImportSpecification
         _lhsOself = rule1756 _self
         __result_ = T_ImportSpecification_vOut76 _lhsOself
         in __result_ )
     in C_ImportSpecification_s77 v76
   {-# INLINE rule1755 #-}
   rule1755 = \ ((_importsIself) :: Imports) ((_rangeIself) :: Range) hiding_ ->
     ImportSpecification_Import _rangeIself hiding_ _importsIself
   {-# INLINE rule1756 #-}
   rule1756 = \ _self ->
     _self

-- Imports -----------------------------------------------------
-- wrapper
data Inh_Imports  = Inh_Imports {  }
data Syn_Imports  = Syn_Imports { self_Syn_Imports :: (Imports) }
{-# INLINABLE wrap_Imports #-}
wrap_Imports :: T_Imports  -> Inh_Imports  -> (Syn_Imports )
wrap_Imports (T_Imports act) (Inh_Imports ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Imports_vIn79 
        (T_Imports_vOut79 _lhsOself) <- return (inv_Imports_s80 sem arg)
        return (Syn_Imports _lhsOself)
   )

-- cata
{-# NOINLINE sem_Imports #-}
sem_Imports :: Imports  -> T_Imports 
sem_Imports list = Prelude.foldr sem_Imports_Cons sem_Imports_Nil (Prelude.map sem_Import list)

-- semantic domain
newtype T_Imports  = T_Imports {
                               attach_T_Imports :: Identity (T_Imports_s80 )
                               }
newtype T_Imports_s80  = C_Imports_s80 {
                                       inv_Imports_s80 :: (T_Imports_v79 )
                                       }
data T_Imports_s81  = C_Imports_s81
type T_Imports_v79  = (T_Imports_vIn79 ) -> (T_Imports_vOut79 )
data T_Imports_vIn79  = T_Imports_vIn79 
data T_Imports_vOut79  = T_Imports_vOut79 (Imports)
{-# NOINLINE sem_Imports_Cons #-}
sem_Imports_Cons :: T_Import  -> T_Imports  -> T_Imports 
sem_Imports_Cons arg_hd_ arg_tl_ = T_Imports (return st80) where
   {-# NOINLINE st80 #-}
   st80 = let
      v79 :: T_Imports_v79 
      v79 = \ (T_Imports_vIn79 ) -> ( let
         _hdX68 = Control.Monad.Identity.runIdentity (attach_T_Import (arg_hd_))
         _tlX80 = Control.Monad.Identity.runIdentity (attach_T_Imports (arg_tl_))
         (T_Import_vOut67 _hdIself) = inv_Import_s68 _hdX68 (T_Import_vIn67 )
         (T_Imports_vOut79 _tlIself) = inv_Imports_s80 _tlX80 (T_Imports_vIn79 )
         _self = rule1757 _hdIself _tlIself
         _lhsOself :: Imports
         _lhsOself = rule1758 _self
         __result_ = T_Imports_vOut79 _lhsOself
         in __result_ )
     in C_Imports_s80 v79
   {-# INLINE rule1757 #-}
   rule1757 = \ ((_hdIself) :: Import) ((_tlIself) :: Imports) ->
     (:) _hdIself _tlIself
   {-# INLINE rule1758 #-}
   rule1758 = \ _self ->
     _self
{-# NOINLINE sem_Imports_Nil #-}
sem_Imports_Nil ::  T_Imports 
sem_Imports_Nil  = T_Imports (return st80) where
   {-# NOINLINE st80 #-}
   st80 = let
      v79 :: T_Imports_v79 
      v79 = \ (T_Imports_vIn79 ) -> ( let
         _self = rule1759  ()
         _lhsOself :: Imports
         _lhsOself = rule1760 _self
         __result_ = T_Imports_vOut79 _lhsOself
         in __result_ )
     in C_Imports_s80 v79
   {-# INLINE rule1759 #-}
   rule1759 = \  (_ :: ()) ->
     []
   {-# INLINE rule1760 #-}
   rule1760 = \ _self ->
     _self

-- LeftHandSide ------------------------------------------------
-- wrapper
data Inh_LeftHandSide  = Inh_LeftHandSide { allTypeConstructors_Inh_LeftHandSide :: (Names), allValueConstructors_Inh_LeftHandSide :: (Names), collectScopeInfos_Inh_LeftHandSide :: ([(ScopeInfo, Entity)]), counter_Inh_LeftHandSide :: (Int), miscerrors_Inh_LeftHandSide :: ([Error]), namesInScope_Inh_LeftHandSide :: (Names), typeConstructors_Inh_LeftHandSide :: (M.Map Name Int), valueConstructors_Inh_LeftHandSide :: (M.Map Name TpScheme), warnings_Inh_LeftHandSide :: ([Warning]) }
data Syn_LeftHandSide  = Syn_LeftHandSide { collectScopeInfos_Syn_LeftHandSide :: ([(ScopeInfo, Entity)]), counter_Syn_LeftHandSide :: (Int), miscerrors_Syn_LeftHandSide :: ([Error]), name_Syn_LeftHandSide :: (Name), numberOfPatterns_Syn_LeftHandSide :: (Int), patVarNames_Syn_LeftHandSide :: (Names), self_Syn_LeftHandSide :: (LeftHandSide), unboundNames_Syn_LeftHandSide :: (Names), warnings_Syn_LeftHandSide :: ([Warning]) }
{-# INLINABLE wrap_LeftHandSide #-}
wrap_LeftHandSide :: T_LeftHandSide  -> Inh_LeftHandSide  -> (Syn_LeftHandSide )
wrap_LeftHandSide (T_LeftHandSide act) (Inh_LeftHandSide _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_LeftHandSide_vIn82 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_LeftHandSide_vOut82 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOname _lhsOnumberOfPatterns _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_LeftHandSide_s83 sem arg)
        return (Syn_LeftHandSide _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOname _lhsOnumberOfPatterns _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_LeftHandSide #-}
sem_LeftHandSide :: LeftHandSide  -> T_LeftHandSide 
sem_LeftHandSide ( LeftHandSide_Function range_ name_ patterns_ ) = sem_LeftHandSide_Function ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Patterns patterns_ )
sem_LeftHandSide ( LeftHandSide_Infix range_ leftPattern_ operator_ rightPattern_ ) = sem_LeftHandSide_Infix ( sem_Range range_ ) ( sem_Pattern leftPattern_ ) ( sem_Name operator_ ) ( sem_Pattern rightPattern_ )
sem_LeftHandSide ( LeftHandSide_Parenthesized range_ lefthandside_ patterns_ ) = sem_LeftHandSide_Parenthesized ( sem_Range range_ ) ( sem_LeftHandSide lefthandside_ ) ( sem_Patterns patterns_ )

-- semantic domain
newtype T_LeftHandSide  = T_LeftHandSide {
                                         attach_T_LeftHandSide :: Identity (T_LeftHandSide_s83 )
                                         }
newtype T_LeftHandSide_s83  = C_LeftHandSide_s83 {
                                                 inv_LeftHandSide_s83 :: (T_LeftHandSide_v82 )
                                                 }
data T_LeftHandSide_s84  = C_LeftHandSide_s84
type T_LeftHandSide_v82  = (T_LeftHandSide_vIn82 ) -> (T_LeftHandSide_vOut82 )
data T_LeftHandSide_vIn82  = T_LeftHandSide_vIn82 (Names) (Names) ([(ScopeInfo, Entity)]) (Int) ([Error]) (Names) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_LeftHandSide_vOut82  = T_LeftHandSide_vOut82 ([(ScopeInfo, Entity)]) (Int) ([Error]) (Name) (Int) (Names) (LeftHandSide) (Names) ([Warning])
{-# NOINLINE sem_LeftHandSide_Function #-}
sem_LeftHandSide_Function :: T_Range  -> T_Name  -> T_Patterns  -> T_LeftHandSide 
sem_LeftHandSide_Function arg_range_ arg_name_ arg_patterns_ = T_LeftHandSide (return st83) where
   {-# NOINLINE st83 #-}
   st83 = let
      v82 :: T_LeftHandSide_v82 
      v82 = \ (T_LeftHandSide_vIn82 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Patterns_vOut121 _patternsIcollectScopeInfos _patternsIcounter _patternsImiscerrors _patternsInumberOfPatterns _patternsIpatVarNames _patternsIself _patternsIunboundNames _patternsIwarnings) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOcounter _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings)
         _lhsOname :: Name
         _lhsOname = rule1761 _nameIself
         _patternsOlhsPattern = rule1762  ()
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule1763 _patternsIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1764 _patternsIunboundNames
         _self = rule1765 _nameIself _patternsIself _rangeIself
         _lhsOself :: LeftHandSide
         _lhsOself = rule1766 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1767 _patternsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1768 _patternsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1769 _patternsImiscerrors
         _lhsOnumberOfPatterns :: Int
         _lhsOnumberOfPatterns = rule1770 _patternsInumberOfPatterns
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1771 _patternsIwarnings
         _patternsOallTypeConstructors = rule1772 _lhsIallTypeConstructors
         _patternsOallValueConstructors = rule1773 _lhsIallValueConstructors
         _patternsOcollectScopeInfos = rule1774 _lhsIcollectScopeInfos
         _patternsOcounter = rule1775 _lhsIcounter
         _patternsOmiscerrors = rule1776 _lhsImiscerrors
         _patternsOnamesInScope = rule1777 _lhsInamesInScope
         _patternsOtypeConstructors = rule1778 _lhsItypeConstructors
         _patternsOvalueConstructors = rule1779 _lhsIvalueConstructors
         _patternsOwarnings = rule1780 _lhsIwarnings
         __result_ = T_LeftHandSide_vOut82 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOname _lhsOnumberOfPatterns _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_LeftHandSide_s83 v82
   {-# INLINE rule1761 #-}
   rule1761 = \ ((_nameIself) :: Name) ->
                             _nameIself
   {-# INLINE rule1762 #-}
   rule1762 = \  (_ :: ()) ->
                                                                False
   {-# INLINE rule1763 #-}
   rule1763 = \ ((_patternsIpatVarNames) :: Names) ->
     _patternsIpatVarNames
   {-# INLINE rule1764 #-}
   rule1764 = \ ((_patternsIunboundNames) :: Names) ->
     _patternsIunboundNames
   {-# INLINE rule1765 #-}
   rule1765 = \ ((_nameIself) :: Name) ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     LeftHandSide_Function _rangeIself _nameIself _patternsIself
   {-# INLINE rule1766 #-}
   rule1766 = \ _self ->
     _self
   {-# INLINE rule1767 #-}
   rule1767 = \ ((_patternsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternsIcollectScopeInfos
   {-# INLINE rule1768 #-}
   rule1768 = \ ((_patternsIcounter) :: Int) ->
     _patternsIcounter
   {-# INLINE rule1769 #-}
   rule1769 = \ ((_patternsImiscerrors) :: [Error]) ->
     _patternsImiscerrors
   {-# INLINE rule1770 #-}
   rule1770 = \ ((_patternsInumberOfPatterns) :: Int) ->
     _patternsInumberOfPatterns
   {-# INLINE rule1771 #-}
   rule1771 = \ ((_patternsIwarnings) :: [Warning]) ->
     _patternsIwarnings
   {-# INLINE rule1772 #-}
   rule1772 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1773 #-}
   rule1773 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1774 #-}
   rule1774 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1775 #-}
   rule1775 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1776 #-}
   rule1776 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1777 #-}
   rule1777 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1778 #-}
   rule1778 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1779 #-}
   rule1779 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1780 #-}
   rule1780 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_LeftHandSide_Infix #-}
sem_LeftHandSide_Infix :: T_Range  -> T_Pattern  -> T_Name  -> T_Pattern  -> T_LeftHandSide 
sem_LeftHandSide_Infix arg_range_ arg_leftPattern_ arg_operator_ arg_rightPattern_ = T_LeftHandSide (return st83) where
   {-# NOINLINE st83 #-}
   st83 = let
      v82 :: T_LeftHandSide_v82 
      v82 = \ (T_LeftHandSide_vIn82 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_leftPattern_))
         _operatorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_operator_))
         _rightPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_rightPattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _leftPatternIcollectScopeInfos _leftPatternIcounter _leftPatternImiscerrors _leftPatternIpatVarNames _leftPatternIself _leftPatternIunboundNames _leftPatternIwarnings) = inv_Pattern_s119 _leftPatternX119 (T_Pattern_vIn118 _leftPatternOallTypeConstructors _leftPatternOallValueConstructors _leftPatternOcollectScopeInfos _leftPatternOcounter _leftPatternOlhsPattern _leftPatternOmiscerrors _leftPatternOnamesInScope _leftPatternOtypeConstructors _leftPatternOvalueConstructors _leftPatternOwarnings)
         (T_Name_vOut112 _operatorIself) = inv_Name_s113 _operatorX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _rightPatternIcollectScopeInfos _rightPatternIcounter _rightPatternImiscerrors _rightPatternIpatVarNames _rightPatternIself _rightPatternIunboundNames _rightPatternIwarnings) = inv_Pattern_s119 _rightPatternX119 (T_Pattern_vIn118 _rightPatternOallTypeConstructors _rightPatternOallValueConstructors _rightPatternOcollectScopeInfos _rightPatternOcounter _rightPatternOlhsPattern _rightPatternOmiscerrors _rightPatternOnamesInScope _rightPatternOtypeConstructors _rightPatternOvalueConstructors _rightPatternOwarnings)
         _lhsOname :: Name
         _lhsOname = rule1781 _operatorIself
         _lhsOnumberOfPatterns :: Int
         _lhsOnumberOfPatterns = rule1782  ()
         _leftPatternOlhsPattern = rule1783  ()
         _rightPatternOlhsPattern = rule1784  ()
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule1785 _leftPatternIpatVarNames _rightPatternIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1786 _leftPatternIunboundNames _rightPatternIunboundNames
         _self = rule1787 _leftPatternIself _operatorIself _rangeIself _rightPatternIself
         _lhsOself :: LeftHandSide
         _lhsOself = rule1788 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1789 _rightPatternIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1790 _rightPatternIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1791 _rightPatternImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1792 _rightPatternIwarnings
         _leftPatternOallTypeConstructors = rule1793 _lhsIallTypeConstructors
         _leftPatternOallValueConstructors = rule1794 _lhsIallValueConstructors
         _leftPatternOcollectScopeInfos = rule1795 _lhsIcollectScopeInfos
         _leftPatternOcounter = rule1796 _lhsIcounter
         _leftPatternOmiscerrors = rule1797 _lhsImiscerrors
         _leftPatternOnamesInScope = rule1798 _lhsInamesInScope
         _leftPatternOtypeConstructors = rule1799 _lhsItypeConstructors
         _leftPatternOvalueConstructors = rule1800 _lhsIvalueConstructors
         _leftPatternOwarnings = rule1801 _lhsIwarnings
         _rightPatternOallTypeConstructors = rule1802 _lhsIallTypeConstructors
         _rightPatternOallValueConstructors = rule1803 _lhsIallValueConstructors
         _rightPatternOcollectScopeInfos = rule1804 _leftPatternIcollectScopeInfos
         _rightPatternOcounter = rule1805 _leftPatternIcounter
         _rightPatternOmiscerrors = rule1806 _leftPatternImiscerrors
         _rightPatternOnamesInScope = rule1807 _lhsInamesInScope
         _rightPatternOtypeConstructors = rule1808 _lhsItypeConstructors
         _rightPatternOvalueConstructors = rule1809 _lhsIvalueConstructors
         _rightPatternOwarnings = rule1810 _leftPatternIwarnings
         __result_ = T_LeftHandSide_vOut82 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOname _lhsOnumberOfPatterns _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_LeftHandSide_s83 v82
   {-# INLINE rule1781 #-}
   rule1781 = \ ((_operatorIself) :: Name) ->
                             _operatorIself
   {-# INLINE rule1782 #-}
   rule1782 = \  (_ :: ()) ->
                                         2
   {-# INLINE rule1783 #-}
   rule1783 = \  (_ :: ()) ->
                                                                False
   {-# INLINE rule1784 #-}
   rule1784 = \  (_ :: ()) ->
                                                                False
   {-# INLINE rule1785 #-}
   rule1785 = \ ((_leftPatternIpatVarNames) :: Names) ((_rightPatternIpatVarNames) :: Names) ->
     _leftPatternIpatVarNames ++ _rightPatternIpatVarNames
   {-# INLINE rule1786 #-}
   rule1786 = \ ((_leftPatternIunboundNames) :: Names) ((_rightPatternIunboundNames) :: Names) ->
     _leftPatternIunboundNames ++ _rightPatternIunboundNames
   {-# INLINE rule1787 #-}
   rule1787 = \ ((_leftPatternIself) :: Pattern) ((_operatorIself) :: Name) ((_rangeIself) :: Range) ((_rightPatternIself) :: Pattern) ->
     LeftHandSide_Infix _rangeIself _leftPatternIself _operatorIself _rightPatternIself
   {-# INLINE rule1788 #-}
   rule1788 = \ _self ->
     _self
   {-# INLINE rule1789 #-}
   rule1789 = \ ((_rightPatternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _rightPatternIcollectScopeInfos
   {-# INLINE rule1790 #-}
   rule1790 = \ ((_rightPatternIcounter) :: Int) ->
     _rightPatternIcounter
   {-# INLINE rule1791 #-}
   rule1791 = \ ((_rightPatternImiscerrors) :: [Error]) ->
     _rightPatternImiscerrors
   {-# INLINE rule1792 #-}
   rule1792 = \ ((_rightPatternIwarnings) :: [Warning]) ->
     _rightPatternIwarnings
   {-# INLINE rule1793 #-}
   rule1793 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1794 #-}
   rule1794 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1795 #-}
   rule1795 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1796 #-}
   rule1796 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1797 #-}
   rule1797 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1798 #-}
   rule1798 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1799 #-}
   rule1799 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1800 #-}
   rule1800 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1801 #-}
   rule1801 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1802 #-}
   rule1802 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1803 #-}
   rule1803 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1804 #-}
   rule1804 = \ ((_leftPatternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _leftPatternIcollectScopeInfos
   {-# INLINE rule1805 #-}
   rule1805 = \ ((_leftPatternIcounter) :: Int) ->
     _leftPatternIcounter
   {-# INLINE rule1806 #-}
   rule1806 = \ ((_leftPatternImiscerrors) :: [Error]) ->
     _leftPatternImiscerrors
   {-# INLINE rule1807 #-}
   rule1807 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1808 #-}
   rule1808 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1809 #-}
   rule1809 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1810 #-}
   rule1810 = \ ((_leftPatternIwarnings) :: [Warning]) ->
     _leftPatternIwarnings
{-# NOINLINE sem_LeftHandSide_Parenthesized #-}
sem_LeftHandSide_Parenthesized :: T_Range  -> T_LeftHandSide  -> T_Patterns  -> T_LeftHandSide 
sem_LeftHandSide_Parenthesized arg_range_ arg_lefthandside_ arg_patterns_ = T_LeftHandSide (return st83) where
   {-# NOINLINE st83 #-}
   st83 = let
      v82 :: T_LeftHandSide_v82 
      v82 = \ (T_LeftHandSide_vIn82 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _lefthandsideX83 = Control.Monad.Identity.runIdentity (attach_T_LeftHandSide (arg_lefthandside_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_LeftHandSide_vOut82 _lefthandsideIcollectScopeInfos _lefthandsideIcounter _lefthandsideImiscerrors _lefthandsideIname _lefthandsideInumberOfPatterns _lefthandsideIpatVarNames _lefthandsideIself _lefthandsideIunboundNames _lefthandsideIwarnings) = inv_LeftHandSide_s83 _lefthandsideX83 (T_LeftHandSide_vIn82 _lefthandsideOallTypeConstructors _lefthandsideOallValueConstructors _lefthandsideOcollectScopeInfos _lefthandsideOcounter _lefthandsideOmiscerrors _lefthandsideOnamesInScope _lefthandsideOtypeConstructors _lefthandsideOvalueConstructors _lefthandsideOwarnings)
         (T_Patterns_vOut121 _patternsIcollectScopeInfos _patternsIcounter _patternsImiscerrors _patternsInumberOfPatterns _patternsIpatVarNames _patternsIself _patternsIunboundNames _patternsIwarnings) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOcounter _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings)
         _lhsOnumberOfPatterns :: Int
         _lhsOnumberOfPatterns = rule1811 _lefthandsideInumberOfPatterns _patternsInumberOfPatterns
         _patternsOlhsPattern = rule1812  ()
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule1813 _lefthandsideIpatVarNames _patternsIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1814 _lefthandsideIunboundNames _patternsIunboundNames
         _self = rule1815 _lefthandsideIself _patternsIself _rangeIself
         _lhsOself :: LeftHandSide
         _lhsOself = rule1816 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1817 _patternsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1818 _patternsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1819 _patternsImiscerrors
         _lhsOname :: Name
         _lhsOname = rule1820 _lefthandsideIname
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1821 _patternsIwarnings
         _lefthandsideOallTypeConstructors = rule1822 _lhsIallTypeConstructors
         _lefthandsideOallValueConstructors = rule1823 _lhsIallValueConstructors
         _lefthandsideOcollectScopeInfos = rule1824 _lhsIcollectScopeInfos
         _lefthandsideOcounter = rule1825 _lhsIcounter
         _lefthandsideOmiscerrors = rule1826 _lhsImiscerrors
         _lefthandsideOnamesInScope = rule1827 _lhsInamesInScope
         _lefthandsideOtypeConstructors = rule1828 _lhsItypeConstructors
         _lefthandsideOvalueConstructors = rule1829 _lhsIvalueConstructors
         _lefthandsideOwarnings = rule1830 _lhsIwarnings
         _patternsOallTypeConstructors = rule1831 _lhsIallTypeConstructors
         _patternsOallValueConstructors = rule1832 _lhsIallValueConstructors
         _patternsOcollectScopeInfos = rule1833 _lefthandsideIcollectScopeInfos
         _patternsOcounter = rule1834 _lefthandsideIcounter
         _patternsOmiscerrors = rule1835 _lefthandsideImiscerrors
         _patternsOnamesInScope = rule1836 _lhsInamesInScope
         _patternsOtypeConstructors = rule1837 _lhsItypeConstructors
         _patternsOvalueConstructors = rule1838 _lhsIvalueConstructors
         _patternsOwarnings = rule1839 _lefthandsideIwarnings
         __result_ = T_LeftHandSide_vOut82 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOname _lhsOnumberOfPatterns _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_LeftHandSide_s83 v82
   {-# INLINE rule1811 #-}
   rule1811 = \ ((_lefthandsideInumberOfPatterns) :: Int) ((_patternsInumberOfPatterns) :: Int) ->
                                             _lefthandsideInumberOfPatterns + _patternsInumberOfPatterns
   {-# INLINE rule1812 #-}
   rule1812 = \  (_ :: ()) ->
                                                                False
   {-# INLINE rule1813 #-}
   rule1813 = \ ((_lefthandsideIpatVarNames) :: Names) ((_patternsIpatVarNames) :: Names) ->
     _lefthandsideIpatVarNames ++ _patternsIpatVarNames
   {-# INLINE rule1814 #-}
   rule1814 = \ ((_lefthandsideIunboundNames) :: Names) ((_patternsIunboundNames) :: Names) ->
     _lefthandsideIunboundNames ++ _patternsIunboundNames
   {-# INLINE rule1815 #-}
   rule1815 = \ ((_lefthandsideIself) :: LeftHandSide) ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     LeftHandSide_Parenthesized _rangeIself _lefthandsideIself _patternsIself
   {-# INLINE rule1816 #-}
   rule1816 = \ _self ->
     _self
   {-# INLINE rule1817 #-}
   rule1817 = \ ((_patternsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternsIcollectScopeInfos
   {-# INLINE rule1818 #-}
   rule1818 = \ ((_patternsIcounter) :: Int) ->
     _patternsIcounter
   {-# INLINE rule1819 #-}
   rule1819 = \ ((_patternsImiscerrors) :: [Error]) ->
     _patternsImiscerrors
   {-# INLINE rule1820 #-}
   rule1820 = \ ((_lefthandsideIname) :: Name) ->
     _lefthandsideIname
   {-# INLINE rule1821 #-}
   rule1821 = \ ((_patternsIwarnings) :: [Warning]) ->
     _patternsIwarnings
   {-# INLINE rule1822 #-}
   rule1822 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1823 #-}
   rule1823 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1824 #-}
   rule1824 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1825 #-}
   rule1825 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1826 #-}
   rule1826 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1827 #-}
   rule1827 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1828 #-}
   rule1828 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1829 #-}
   rule1829 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1830 #-}
   rule1830 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule1831 #-}
   rule1831 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1832 #-}
   rule1832 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1833 #-}
   rule1833 = \ ((_lefthandsideIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lefthandsideIcollectScopeInfos
   {-# INLINE rule1834 #-}
   rule1834 = \ ((_lefthandsideIcounter) :: Int) ->
     _lefthandsideIcounter
   {-# INLINE rule1835 #-}
   rule1835 = \ ((_lefthandsideImiscerrors) :: [Error]) ->
     _lefthandsideImiscerrors
   {-# INLINE rule1836 #-}
   rule1836 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1837 #-}
   rule1837 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1838 #-}
   rule1838 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1839 #-}
   rule1839 = \ ((_lefthandsideIwarnings) :: [Warning]) ->
     _lefthandsideIwarnings

-- Literal -----------------------------------------------------
-- wrapper
data Inh_Literal  = Inh_Literal { collectScopeInfos_Inh_Literal :: ([(ScopeInfo, Entity)]), miscerrors_Inh_Literal :: ([Error]) }
data Syn_Literal  = Syn_Literal { collectScopeInfos_Syn_Literal :: ([(ScopeInfo, Entity)]), miscerrors_Syn_Literal :: ([Error]), self_Syn_Literal :: (Literal) }
{-# INLINABLE wrap_Literal #-}
wrap_Literal :: T_Literal  -> Inh_Literal  -> (Syn_Literal )
wrap_Literal (T_Literal act) (Inh_Literal _lhsIcollectScopeInfos _lhsImiscerrors) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Literal_vIn85 _lhsIcollectScopeInfos _lhsImiscerrors
        (T_Literal_vOut85 _lhsOcollectScopeInfos _lhsOmiscerrors _lhsOself) <- return (inv_Literal_s86 sem arg)
        return (Syn_Literal _lhsOcollectScopeInfos _lhsOmiscerrors _lhsOself)
   )

-- cata
{-# NOINLINE sem_Literal #-}
sem_Literal :: Literal  -> T_Literal 
sem_Literal ( Literal_Int range_ value_ ) = sem_Literal_Int ( sem_Range range_ ) value_
sem_Literal ( Literal_Char range_ value_ ) = sem_Literal_Char ( sem_Range range_ ) value_
sem_Literal ( Literal_Float range_ value_ ) = sem_Literal_Float ( sem_Range range_ ) value_
sem_Literal ( Literal_String range_ value_ ) = sem_Literal_String ( sem_Range range_ ) value_

-- semantic domain
newtype T_Literal  = T_Literal {
                               attach_T_Literal :: Identity (T_Literal_s86 )
                               }
newtype T_Literal_s86  = C_Literal_s86 {
                                       inv_Literal_s86 :: (T_Literal_v85 )
                                       }
data T_Literal_s87  = C_Literal_s87
type T_Literal_v85  = (T_Literal_vIn85 ) -> (T_Literal_vOut85 )
data T_Literal_vIn85  = T_Literal_vIn85 ([(ScopeInfo, Entity)]) ([Error])
data T_Literal_vOut85  = T_Literal_vOut85 ([(ScopeInfo, Entity)]) ([Error]) (Literal)
{-# NOINLINE sem_Literal_Int #-}
sem_Literal_Int :: T_Range  -> (String) -> T_Literal 
sem_Literal_Int arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 _lhsIcollectScopeInfos _lhsImiscerrors) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _intLiteralTooBigErrors = rule1840 _rangeIself arg_value_
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1841 _intLiteralTooBigErrors _lhsImiscerrors
         _self = rule1842 _rangeIself arg_value_
         _lhsOself :: Literal
         _lhsOself = rule1843 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1844 _lhsIcollectScopeInfos
         __result_ = T_Literal_vOut85 _lhsOcollectScopeInfos _lhsOmiscerrors _lhsOself
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule1840 #-}
   rule1840 = \ ((_rangeIself) :: Range) value_ ->
                   let val = read value_ :: Integer in
                   if length value_ > 9 && (val > maxInt || val < minInt)  then
                      [ IntLiteralTooBig _rangeIself value_ ]
                   else
                      []
   {-# INLINE rule1841 #-}
   rule1841 = \ _intLiteralTooBigErrors ((_lhsImiscerrors) :: [Error]) ->
                             _intLiteralTooBigErrors ++ _lhsImiscerrors
   {-# INLINE rule1842 #-}
   rule1842 = \ ((_rangeIself) :: Range) value_ ->
     Literal_Int _rangeIself value_
   {-# INLINE rule1843 #-}
   rule1843 = \ _self ->
     _self
   {-# INLINE rule1844 #-}
   rule1844 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
{-# NOINLINE sem_Literal_Char #-}
sem_Literal_Char :: T_Range  -> (String) -> T_Literal 
sem_Literal_Char arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 _lhsIcollectScopeInfos _lhsImiscerrors) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _self = rule1845 _rangeIself arg_value_
         _lhsOself :: Literal
         _lhsOself = rule1846 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1847 _lhsIcollectScopeInfos
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1848 _lhsImiscerrors
         __result_ = T_Literal_vOut85 _lhsOcollectScopeInfos _lhsOmiscerrors _lhsOself
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule1845 #-}
   rule1845 = \ ((_rangeIself) :: Range) value_ ->
     Literal_Char _rangeIself value_
   {-# INLINE rule1846 #-}
   rule1846 = \ _self ->
     _self
   {-# INLINE rule1847 #-}
   rule1847 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1848 #-}
   rule1848 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
{-# NOINLINE sem_Literal_Float #-}
sem_Literal_Float :: T_Range  -> (String) -> T_Literal 
sem_Literal_Float arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 _lhsIcollectScopeInfos _lhsImiscerrors) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _self = rule1849 _rangeIself arg_value_
         _lhsOself :: Literal
         _lhsOself = rule1850 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1851 _lhsIcollectScopeInfos
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1852 _lhsImiscerrors
         __result_ = T_Literal_vOut85 _lhsOcollectScopeInfos _lhsOmiscerrors _lhsOself
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule1849 #-}
   rule1849 = \ ((_rangeIself) :: Range) value_ ->
     Literal_Float _rangeIself value_
   {-# INLINE rule1850 #-}
   rule1850 = \ _self ->
     _self
   {-# INLINE rule1851 #-}
   rule1851 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1852 #-}
   rule1852 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
{-# NOINLINE sem_Literal_String #-}
sem_Literal_String :: T_Range  -> (String) -> T_Literal 
sem_Literal_String arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 _lhsIcollectScopeInfos _lhsImiscerrors) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _self = rule1853 _rangeIself arg_value_
         _lhsOself :: Literal
         _lhsOself = rule1854 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1855 _lhsIcollectScopeInfos
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1856 _lhsImiscerrors
         __result_ = T_Literal_vOut85 _lhsOcollectScopeInfos _lhsOmiscerrors _lhsOself
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule1853 #-}
   rule1853 = \ ((_rangeIself) :: Range) value_ ->
     Literal_String _rangeIself value_
   {-# INLINE rule1854 #-}
   rule1854 = \ _self ->
     _self
   {-# INLINE rule1855 #-}
   rule1855 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1856 #-}
   rule1856 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors

-- MaybeDeclarations -------------------------------------------
-- wrapper
data Inh_MaybeDeclarations  = Inh_MaybeDeclarations { allTypeConstructors_Inh_MaybeDeclarations :: (Names), allValueConstructors_Inh_MaybeDeclarations :: (Names), classEnvironment_Inh_MaybeDeclarations :: (ClassEnvironment), collectScopeInfos_Inh_MaybeDeclarations :: ([(ScopeInfo, Entity)]), counter_Inh_MaybeDeclarations :: (Int), kindErrors_Inh_MaybeDeclarations :: ([Error]), miscerrors_Inh_MaybeDeclarations :: ([Error]), namesInScope_Inh_MaybeDeclarations :: (Names), options_Inh_MaybeDeclarations :: ([Option]), orderedTypeSynonyms_Inh_MaybeDeclarations :: (OrderedTypeSynonyms), typeConstructors_Inh_MaybeDeclarations :: (M.Map Name Int), unboundNames_Inh_MaybeDeclarations :: (Names), valueConstructors_Inh_MaybeDeclarations :: (M.Map Name TpScheme), warnings_Inh_MaybeDeclarations :: ([Warning]) }
data Syn_MaybeDeclarations  = Syn_MaybeDeclarations { collectInstances_Syn_MaybeDeclarations :: ([(Name, Instance)]), collectScopeInfos_Syn_MaybeDeclarations :: ([(ScopeInfo, Entity)]), counter_Syn_MaybeDeclarations :: (Int), kindErrors_Syn_MaybeDeclarations :: ([Error]), miscerrors_Syn_MaybeDeclarations :: ([Error]), namesInScope_Syn_MaybeDeclarations :: (Names), self_Syn_MaybeDeclarations :: (MaybeDeclarations), unboundNames_Syn_MaybeDeclarations :: (Names), warnings_Syn_MaybeDeclarations :: ([Warning]) }
{-# INLINABLE wrap_MaybeDeclarations #-}
wrap_MaybeDeclarations :: T_MaybeDeclarations  -> Inh_MaybeDeclarations  -> (Syn_MaybeDeclarations )
wrap_MaybeDeclarations (T_MaybeDeclarations act) (Inh_MaybeDeclarations _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeDeclarations_vIn88 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings
        (T_MaybeDeclarations_vOut88 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_MaybeDeclarations_s89 sem arg)
        return (Syn_MaybeDeclarations _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_MaybeDeclarations #-}
sem_MaybeDeclarations :: MaybeDeclarations  -> T_MaybeDeclarations 
sem_MaybeDeclarations ( MaybeDeclarations_Nothing  ) = sem_MaybeDeclarations_Nothing 
sem_MaybeDeclarations ( MaybeDeclarations_Just declarations_ ) = sem_MaybeDeclarations_Just ( sem_Declarations declarations_ )

-- semantic domain
newtype T_MaybeDeclarations  = T_MaybeDeclarations {
                                                   attach_T_MaybeDeclarations :: Identity (T_MaybeDeclarations_s89 )
                                                   }
newtype T_MaybeDeclarations_s89  = C_MaybeDeclarations_s89 {
                                                           inv_MaybeDeclarations_s89 :: (T_MaybeDeclarations_v88 )
                                                           }
data T_MaybeDeclarations_s90  = C_MaybeDeclarations_s90
type T_MaybeDeclarations_v88  = (T_MaybeDeclarations_vIn88 ) -> (T_MaybeDeclarations_vOut88 )
data T_MaybeDeclarations_vIn88  = T_MaybeDeclarations_vIn88 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (Names) (M.Map Name TpScheme) ([Warning])
data T_MaybeDeclarations_vOut88  = T_MaybeDeclarations_vOut88 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) (MaybeDeclarations) (Names) ([Warning])
{-# NOINLINE sem_MaybeDeclarations_Nothing #-}
sem_MaybeDeclarations_Nothing ::  T_MaybeDeclarations 
sem_MaybeDeclarations_Nothing  = T_MaybeDeclarations (return st89) where
   {-# NOINLINE st89 #-}
   st89 = let
      v88 :: T_MaybeDeclarations_v88 
      v88 = \ (T_MaybeDeclarations_vIn88 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1857  ()
         _self = rule1858  ()
         _lhsOself :: MaybeDeclarations
         _lhsOself = rule1859 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1860 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1861 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1862 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1863 _lhsImiscerrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule1864 _lhsInamesInScope
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1865 _lhsIunboundNames
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1866 _lhsIwarnings
         __result_ = T_MaybeDeclarations_vOut88 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_MaybeDeclarations_s89 v88
   {-# INLINE rule1857 #-}
   rule1857 = \  (_ :: ()) ->
     []
   {-# INLINE rule1858 #-}
   rule1858 = \  (_ :: ()) ->
     MaybeDeclarations_Nothing
   {-# INLINE rule1859 #-}
   rule1859 = \ _self ->
     _self
   {-# INLINE rule1860 #-}
   rule1860 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1861 #-}
   rule1861 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1862 #-}
   rule1862 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1863 #-}
   rule1863 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1864 #-}
   rule1864 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1865 #-}
   rule1865 = \ ((_lhsIunboundNames) :: Names) ->
     _lhsIunboundNames
   {-# INLINE rule1866 #-}
   rule1866 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_MaybeDeclarations_Just #-}
sem_MaybeDeclarations_Just :: T_Declarations  -> T_MaybeDeclarations 
sem_MaybeDeclarations_Just arg_declarations_ = T_MaybeDeclarations (return st89) where
   {-# NOINLINE st89 #-}
   st89 = let
      v88 :: T_MaybeDeclarations_v88 
      v88 = \ (T_MaybeDeclarations_vIn88 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Declarations_vOut31 _declarationsIcollectInstances _declarationsIcollectScopeInfos _declarationsIcollectTypeConstructors _declarationsIcollectTypeSynonyms _declarationsIcollectValueConstructors _declarationsIcounter _declarationsIdeclVarNames _declarationsIkindErrors _declarationsImiscerrors _declarationsIoperatorFixities _declarationsIpreviousWasAlsoFB _declarationsIrestrictedNames _declarationsIself _declarationsIsuspiciousFBs _declarationsItypeSignatures _declarationsIunboundNames _declarationsIwarnings) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 _declarationsOallTypeConstructors _declarationsOallValueConstructors _declarationsOclassEnvironment _declarationsOcollectScopeInfos _declarationsOcollectTypeConstructors _declarationsOcollectTypeSynonyms _declarationsOcollectValueConstructors _declarationsOcounter _declarationsOkindErrors _declarationsOmiscerrors _declarationsOnamesInScope _declarationsOoperatorFixities _declarationsOoptions _declarationsOorderedTypeSynonyms _declarationsOpreviousWasAlsoFB _declarationsOsuspiciousFBs _declarationsOtypeConstructors _declarationsOtypeSignatures _declarationsOvalueConstructors _declarationsOwarnings)
         _declarationsOtypeSignatures = rule1867  ()
         (_namesInScope,_unboundNames,_scopeInfo) = rule1868 _declarationsIdeclVarNames _declarationsIunboundNames _lhsInamesInScope _lhsIunboundNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1869 _unboundNames
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1870 _declarationsIwarnings _suspiciousErrors
         _declarationsOpreviousWasAlsoFB = rule1871  ()
         _declarationsOsuspiciousFBs = rule1872  ()
         _suspiciousErrors = rule1873 _declarationsIsuspiciousFBs _declarationsItypeSignatures
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1874 _declarationsImiscerrors _typeSignatureErrors
         (_,_doubles) = rule1875 _declarationsItypeSignatures
         _typeSignatureErrors = rule1876 _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
         (_collectTypeConstructors,_collectValueConstructors,_collectTypeSynonyms,_collectConstructorEnv,_derivedFunctions,_operatorFixities) = rule1877  ()
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1878 _declarationsIcollectScopeInfos _scopeInfo
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1879 _declarationsIcollectInstances
         _self = rule1880 _declarationsIself
         _lhsOself :: MaybeDeclarations
         _lhsOself = rule1881 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule1882 _declarationsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1883 _declarationsIkindErrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule1884 _namesInScope
         _declarationsOallTypeConstructors = rule1885 _lhsIallTypeConstructors
         _declarationsOallValueConstructors = rule1886 _lhsIallValueConstructors
         _declarationsOclassEnvironment = rule1887 _lhsIclassEnvironment
         _declarationsOcollectScopeInfos = rule1888 _lhsIcollectScopeInfos
         _declarationsOcollectTypeConstructors = rule1889 _collectTypeConstructors
         _declarationsOcollectTypeSynonyms = rule1890 _collectTypeSynonyms
         _declarationsOcollectValueConstructors = rule1891 _collectValueConstructors
         _declarationsOcounter = rule1892 _lhsIcounter
         _declarationsOkindErrors = rule1893 _lhsIkindErrors
         _declarationsOmiscerrors = rule1894 _lhsImiscerrors
         _declarationsOnamesInScope = rule1895 _namesInScope
         _declarationsOoperatorFixities = rule1896 _operatorFixities
         _declarationsOoptions = rule1897 _lhsIoptions
         _declarationsOorderedTypeSynonyms = rule1898 _lhsIorderedTypeSynonyms
         _declarationsOtypeConstructors = rule1899 _lhsItypeConstructors
         _declarationsOvalueConstructors = rule1900 _lhsIvalueConstructors
         _declarationsOwarnings = rule1901 _lhsIwarnings
         __result_ = T_MaybeDeclarations_vOut88 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_MaybeDeclarations_s89 v88
   {-# INLINE rule1867 #-}
   rule1867 = \  (_ :: ()) ->
                                                                  []
   {-# INLINE rule1868 #-}
   rule1868 = \ ((_declarationsIdeclVarNames) :: Names) ((_declarationsIunboundNames) :: Names) ((_lhsInamesInScope) :: Names) ((_lhsIunboundNames) :: Names) ->
                                                               changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
   {-# INLINE rule1869 #-}
   rule1869 = \ _unboundNames ->
                                  _unboundNames
   {-# INLINE rule1870 #-}
   rule1870 = \ ((_declarationsIwarnings) :: [Warning]) _suspiciousErrors ->
                            _declarationsIwarnings ++
                            _suspiciousErrors
   {-# INLINE rule1871 #-}
   rule1871 = \  (_ :: ()) ->
                                                Nothing
   {-# INLINE rule1872 #-}
   rule1872 = \  (_ :: ()) ->
                                                []
   {-# INLINE rule1873 #-}
   rule1873 = \ ((_declarationsIsuspiciousFBs) :: [(Name,Name)]) ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                                findSimilarFunctionBindings _declarationsItypeSignatures _declarationsIsuspiciousFBs
   {-# INLINE rule1874 #-}
   rule1874 = \ ((_declarationsImiscerrors) :: [Error]) _typeSignatureErrors ->
                                _typeSignatureErrors ++ _declarationsImiscerrors
   {-# INLINE rule1875 #-}
   rule1875 = \ ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                 uniqueAppearance (map fst _declarationsItypeSignatures)
   {-# INLINE rule1876 #-}
   rule1876 = \ ((_declarationsIdeclVarNames) :: Names) ((_declarationsIrestrictedNames) :: Names) ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                         checkTypeSignatures _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
   {-# INLINE rule1877 #-}
   rule1877 = \  (_ :: ()) ->
                                                                                                                                                   internalError "PartialSyntax.ag" "n/a" "toplevel MaybeDeclaration"
   {-# INLINE rule1878 #-}
   rule1878 = \ ((_declarationsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) _scopeInfo ->
                                                 (_scopeInfo, Definition) : _declarationsIcollectScopeInfos
   {-# INLINE rule1879 #-}
   rule1879 = \ ((_declarationsIcollectInstances) :: [(Name, Instance)]) ->
     _declarationsIcollectInstances
   {-# INLINE rule1880 #-}
   rule1880 = \ ((_declarationsIself) :: Declarations) ->
     MaybeDeclarations_Just _declarationsIself
   {-# INLINE rule1881 #-}
   rule1881 = \ _self ->
     _self
   {-# INLINE rule1882 #-}
   rule1882 = \ ((_declarationsIcounter) :: Int) ->
     _declarationsIcounter
   {-# INLINE rule1883 #-}
   rule1883 = \ ((_declarationsIkindErrors) :: [Error]) ->
     _declarationsIkindErrors
   {-# INLINE rule1884 #-}
   rule1884 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule1885 #-}
   rule1885 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1886 #-}
   rule1886 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1887 #-}
   rule1887 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1888 #-}
   rule1888 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1889 #-}
   rule1889 = \ _collectTypeConstructors ->
     _collectTypeConstructors
   {-# INLINE rule1890 #-}
   rule1890 = \ _collectTypeSynonyms ->
     _collectTypeSynonyms
   {-# INLINE rule1891 #-}
   rule1891 = \ _collectValueConstructors ->
     _collectValueConstructors
   {-# INLINE rule1892 #-}
   rule1892 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1893 #-}
   rule1893 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1894 #-}
   rule1894 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1895 #-}
   rule1895 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule1896 #-}
   rule1896 = \ _operatorFixities ->
     _operatorFixities
   {-# INLINE rule1897 #-}
   rule1897 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1898 #-}
   rule1898 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1899 #-}
   rule1899 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1900 #-}
   rule1900 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1901 #-}
   rule1901 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- MaybeExports ------------------------------------------------
-- wrapper
data Inh_MaybeExports  = Inh_MaybeExports { consInScope_Inh_MaybeExports :: (Names), modulesInScope_Inh_MaybeExports :: (Names), namesInScop_Inh_MaybeExports :: (Names), tyconsInScope_Inh_MaybeExports :: (Names) }
data Syn_MaybeExports  = Syn_MaybeExports { exportErrors_Syn_MaybeExports :: ([Error]), self_Syn_MaybeExports :: (MaybeExports) }
{-# INLINABLE wrap_MaybeExports #-}
wrap_MaybeExports :: T_MaybeExports  -> Inh_MaybeExports  -> (Syn_MaybeExports )
wrap_MaybeExports (T_MaybeExports act) (Inh_MaybeExports _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeExports_vIn91 _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope
        (T_MaybeExports_vOut91 _lhsOexportErrors _lhsOself) <- return (inv_MaybeExports_s92 sem arg)
        return (Syn_MaybeExports _lhsOexportErrors _lhsOself)
   )

-- cata
{-# NOINLINE sem_MaybeExports #-}
sem_MaybeExports :: MaybeExports  -> T_MaybeExports 
sem_MaybeExports ( MaybeExports_Nothing  ) = sem_MaybeExports_Nothing 
sem_MaybeExports ( MaybeExports_Just exports_ ) = sem_MaybeExports_Just ( sem_Exports exports_ )

-- semantic domain
newtype T_MaybeExports  = T_MaybeExports {
                                         attach_T_MaybeExports :: Identity (T_MaybeExports_s92 )
                                         }
newtype T_MaybeExports_s92  = C_MaybeExports_s92 {
                                                 inv_MaybeExports_s92 :: (T_MaybeExports_v91 )
                                                 }
data T_MaybeExports_s93  = C_MaybeExports_s93
type T_MaybeExports_v91  = (T_MaybeExports_vIn91 ) -> (T_MaybeExports_vOut91 )
data T_MaybeExports_vIn91  = T_MaybeExports_vIn91 (Names) (Names) (Names) (Names)
data T_MaybeExports_vOut91  = T_MaybeExports_vOut91 ([Error]) (MaybeExports)
{-# NOINLINE sem_MaybeExports_Nothing #-}
sem_MaybeExports_Nothing ::  T_MaybeExports 
sem_MaybeExports_Nothing  = T_MaybeExports (return st92) where
   {-# NOINLINE st92 #-}
   st92 = let
      v91 :: T_MaybeExports_v91 
      v91 = \ (T_MaybeExports_vIn91 _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope) -> ( let
         _lhsOexportErrors :: [Error]
         _lhsOexportErrors = rule1902  ()
         _self = rule1903  ()
         _lhsOself :: MaybeExports
         _lhsOself = rule1904 _self
         __result_ = T_MaybeExports_vOut91 _lhsOexportErrors _lhsOself
         in __result_ )
     in C_MaybeExports_s92 v91
   {-# INLINE rule1902 #-}
   rule1902 = \  (_ :: ()) ->
     []
   {-# INLINE rule1903 #-}
   rule1903 = \  (_ :: ()) ->
     MaybeExports_Nothing
   {-# INLINE rule1904 #-}
   rule1904 = \ _self ->
     _self
{-# NOINLINE sem_MaybeExports_Just #-}
sem_MaybeExports_Just :: T_Exports  -> T_MaybeExports 
sem_MaybeExports_Just arg_exports_ = T_MaybeExports (return st92) where
   {-# NOINLINE st92 #-}
   st92 = let
      v91 :: T_MaybeExports_v91 
      v91 = \ (T_MaybeExports_vIn91 _lhsIconsInScope _lhsImodulesInScope _lhsInamesInScop _lhsItyconsInScope) -> ( let
         _exportsX38 = Control.Monad.Identity.runIdentity (attach_T_Exports (arg_exports_))
         (T_Exports_vOut37 _exportsIexportErrors _exportsIself) = inv_Exports_s38 _exportsX38 (T_Exports_vIn37 _exportsOconsInScope _exportsOmodulesInScope _exportsOnamesInScop _exportsOtyconsInScope)
         _lhsOexportErrors :: [Error]
         _lhsOexportErrors = rule1905 _exportsIexportErrors
         _self = rule1906 _exportsIself
         _lhsOself :: MaybeExports
         _lhsOself = rule1907 _self
         _exportsOconsInScope = rule1908 _lhsIconsInScope
         _exportsOmodulesInScope = rule1909 _lhsImodulesInScope
         _exportsOnamesInScop = rule1910 _lhsInamesInScop
         _exportsOtyconsInScope = rule1911 _lhsItyconsInScope
         __result_ = T_MaybeExports_vOut91 _lhsOexportErrors _lhsOself
         in __result_ )
     in C_MaybeExports_s92 v91
   {-# INLINE rule1905 #-}
   rule1905 = \ ((_exportsIexportErrors) :: [Error]) ->
     _exportsIexportErrors
   {-# INLINE rule1906 #-}
   rule1906 = \ ((_exportsIself) :: Exports) ->
     MaybeExports_Just _exportsIself
   {-# INLINE rule1907 #-}
   rule1907 = \ _self ->
     _self
   {-# INLINE rule1908 #-}
   rule1908 = \ ((_lhsIconsInScope) :: Names) ->
     _lhsIconsInScope
   {-# INLINE rule1909 #-}
   rule1909 = \ ((_lhsImodulesInScope) :: Names) ->
     _lhsImodulesInScope
   {-# INLINE rule1910 #-}
   rule1910 = \ ((_lhsInamesInScop) :: Names) ->
     _lhsInamesInScop
   {-# INLINE rule1911 #-}
   rule1911 = \ ((_lhsItyconsInScope) :: Names) ->
     _lhsItyconsInScope

-- MaybeExpression ---------------------------------------------
-- wrapper
data Inh_MaybeExpression  = Inh_MaybeExpression { allTypeConstructors_Inh_MaybeExpression :: (Names), allValueConstructors_Inh_MaybeExpression :: (Names), classEnvironment_Inh_MaybeExpression :: (ClassEnvironment), collectScopeInfos_Inh_MaybeExpression :: ([(ScopeInfo, Entity)]), counter_Inh_MaybeExpression :: (Int), kindErrors_Inh_MaybeExpression :: ([Error]), miscerrors_Inh_MaybeExpression :: ([Error]), namesInScope_Inh_MaybeExpression :: (Names), options_Inh_MaybeExpression :: ([Option]), orderedTypeSynonyms_Inh_MaybeExpression :: (OrderedTypeSynonyms), typeConstructors_Inh_MaybeExpression :: (M.Map Name Int), valueConstructors_Inh_MaybeExpression :: (M.Map Name TpScheme), warnings_Inh_MaybeExpression :: ([Warning]) }
data Syn_MaybeExpression  = Syn_MaybeExpression { collectInstances_Syn_MaybeExpression :: ([(Name, Instance)]), collectScopeInfos_Syn_MaybeExpression :: ([(ScopeInfo, Entity)]), counter_Syn_MaybeExpression :: (Int), kindErrors_Syn_MaybeExpression :: ([Error]), miscerrors_Syn_MaybeExpression :: ([Error]), self_Syn_MaybeExpression :: (MaybeExpression), unboundNames_Syn_MaybeExpression :: (Names), warnings_Syn_MaybeExpression :: ([Warning]) }
{-# INLINABLE wrap_MaybeExpression #-}
wrap_MaybeExpression :: T_MaybeExpression  -> Inh_MaybeExpression  -> (Syn_MaybeExpression )
wrap_MaybeExpression (T_MaybeExpression act) (Inh_MaybeExpression _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeExpression_vIn94 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_MaybeExpression_vOut94 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_MaybeExpression_s95 sem arg)
        return (Syn_MaybeExpression _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_MaybeExpression #-}
sem_MaybeExpression :: MaybeExpression  -> T_MaybeExpression 
sem_MaybeExpression ( MaybeExpression_Nothing  ) = sem_MaybeExpression_Nothing 
sem_MaybeExpression ( MaybeExpression_Just expression_ ) = sem_MaybeExpression_Just ( sem_Expression expression_ )

-- semantic domain
newtype T_MaybeExpression  = T_MaybeExpression {
                                               attach_T_MaybeExpression :: Identity (T_MaybeExpression_s95 )
                                               }
newtype T_MaybeExpression_s95  = C_MaybeExpression_s95 {
                                                       inv_MaybeExpression_s95 :: (T_MaybeExpression_v94 )
                                                       }
data T_MaybeExpression_s96  = C_MaybeExpression_s96
type T_MaybeExpression_v94  = (T_MaybeExpression_vIn94 ) -> (T_MaybeExpression_vOut94 )
data T_MaybeExpression_vIn94  = T_MaybeExpression_vIn94 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_MaybeExpression_vOut94  = T_MaybeExpression_vOut94 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (MaybeExpression) (Names) ([Warning])
{-# NOINLINE sem_MaybeExpression_Nothing #-}
sem_MaybeExpression_Nothing ::  T_MaybeExpression 
sem_MaybeExpression_Nothing  = T_MaybeExpression (return st95) where
   {-# NOINLINE st95 #-}
   st95 = let
      v94 :: T_MaybeExpression_v94 
      v94 = \ (T_MaybeExpression_vIn94 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1912  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1913  ()
         _self = rule1914  ()
         _lhsOself :: MaybeExpression
         _lhsOself = rule1915 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1916 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1917 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1918 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1919 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1920 _lhsIwarnings
         __result_ = T_MaybeExpression_vOut94 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_MaybeExpression_s95 v94
   {-# INLINE rule1912 #-}
   rule1912 = \  (_ :: ()) ->
     []
   {-# INLINE rule1913 #-}
   rule1913 = \  (_ :: ()) ->
     []
   {-# INLINE rule1914 #-}
   rule1914 = \  (_ :: ()) ->
     MaybeExpression_Nothing
   {-# INLINE rule1915 #-}
   rule1915 = \ _self ->
     _self
   {-# INLINE rule1916 #-}
   rule1916 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1917 #-}
   rule1917 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1918 #-}
   rule1918 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1919 #-}
   rule1919 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1920 #-}
   rule1920 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_MaybeExpression_Just #-}
sem_MaybeExpression_Just :: T_Expression  -> T_MaybeExpression 
sem_MaybeExpression_Just arg_expression_ = T_MaybeExpression (return st95) where
   {-# NOINLINE st95 #-}
   st95 = let
      v94 :: T_MaybeExpression_v94 
      v94 = \ (T_MaybeExpression_vIn94 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule1921 _expressionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule1922 _expressionIunboundNames
         _self = rule1923 _expressionIself
         _lhsOself :: MaybeExpression
         _lhsOself = rule1924 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule1925 _expressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule1926 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule1927 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule1928 _expressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule1929 _expressionIwarnings
         _expressionOallTypeConstructors = rule1930 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule1931 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule1932 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule1933 _lhsIcollectScopeInfos
         _expressionOcounter = rule1934 _lhsIcounter
         _expressionOkindErrors = rule1935 _lhsIkindErrors
         _expressionOmiscerrors = rule1936 _lhsImiscerrors
         _expressionOnamesInScope = rule1937 _lhsInamesInScope
         _expressionOoptions = rule1938 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule1939 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule1940 _lhsItypeConstructors
         _expressionOvalueConstructors = rule1941 _lhsIvalueConstructors
         _expressionOwarnings = rule1942 _lhsIwarnings
         __result_ = T_MaybeExpression_vOut94 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_MaybeExpression_s95 v94
   {-# INLINE rule1921 #-}
   rule1921 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule1922 #-}
   rule1922 = \ ((_expressionIunboundNames) :: Names) ->
     _expressionIunboundNames
   {-# INLINE rule1923 #-}
   rule1923 = \ ((_expressionIself) :: Expression) ->
     MaybeExpression_Just _expressionIself
   {-# INLINE rule1924 #-}
   rule1924 = \ _self ->
     _self
   {-# INLINE rule1925 #-}
   rule1925 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule1926 #-}
   rule1926 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule1927 #-}
   rule1927 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule1928 #-}
   rule1928 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule1929 #-}
   rule1929 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule1930 #-}
   rule1930 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule1931 #-}
   rule1931 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule1932 #-}
   rule1932 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule1933 #-}
   rule1933 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule1934 #-}
   rule1934 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule1935 #-}
   rule1935 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule1936 #-}
   rule1936 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule1937 #-}
   rule1937 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule1938 #-}
   rule1938 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule1939 #-}
   rule1939 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule1940 #-}
   rule1940 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule1941 #-}
   rule1941 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule1942 #-}
   rule1942 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- MaybeImportSpecification ------------------------------------
-- wrapper
data Inh_MaybeImportSpecification  = Inh_MaybeImportSpecification {  }
data Syn_MaybeImportSpecification  = Syn_MaybeImportSpecification { self_Syn_MaybeImportSpecification :: (MaybeImportSpecification) }
{-# INLINABLE wrap_MaybeImportSpecification #-}
wrap_MaybeImportSpecification :: T_MaybeImportSpecification  -> Inh_MaybeImportSpecification  -> (Syn_MaybeImportSpecification )
wrap_MaybeImportSpecification (T_MaybeImportSpecification act) (Inh_MaybeImportSpecification ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeImportSpecification_vIn97 
        (T_MaybeImportSpecification_vOut97 _lhsOself) <- return (inv_MaybeImportSpecification_s98 sem arg)
        return (Syn_MaybeImportSpecification _lhsOself)
   )

-- cata
{-# NOINLINE sem_MaybeImportSpecification #-}
sem_MaybeImportSpecification :: MaybeImportSpecification  -> T_MaybeImportSpecification 
sem_MaybeImportSpecification ( MaybeImportSpecification_Nothing  ) = sem_MaybeImportSpecification_Nothing 
sem_MaybeImportSpecification ( MaybeImportSpecification_Just importspecification_ ) = sem_MaybeImportSpecification_Just ( sem_ImportSpecification importspecification_ )

-- semantic domain
newtype T_MaybeImportSpecification  = T_MaybeImportSpecification {
                                                                 attach_T_MaybeImportSpecification :: Identity (T_MaybeImportSpecification_s98 )
                                                                 }
newtype T_MaybeImportSpecification_s98  = C_MaybeImportSpecification_s98 {
                                                                         inv_MaybeImportSpecification_s98 :: (T_MaybeImportSpecification_v97 )
                                                                         }
data T_MaybeImportSpecification_s99  = C_MaybeImportSpecification_s99
type T_MaybeImportSpecification_v97  = (T_MaybeImportSpecification_vIn97 ) -> (T_MaybeImportSpecification_vOut97 )
data T_MaybeImportSpecification_vIn97  = T_MaybeImportSpecification_vIn97 
data T_MaybeImportSpecification_vOut97  = T_MaybeImportSpecification_vOut97 (MaybeImportSpecification)
{-# NOINLINE sem_MaybeImportSpecification_Nothing #-}
sem_MaybeImportSpecification_Nothing ::  T_MaybeImportSpecification 
sem_MaybeImportSpecification_Nothing  = T_MaybeImportSpecification (return st98) where
   {-# NOINLINE st98 #-}
   st98 = let
      v97 :: T_MaybeImportSpecification_v97 
      v97 = \ (T_MaybeImportSpecification_vIn97 ) -> ( let
         _self = rule1943  ()
         _lhsOself :: MaybeImportSpecification
         _lhsOself = rule1944 _self
         __result_ = T_MaybeImportSpecification_vOut97 _lhsOself
         in __result_ )
     in C_MaybeImportSpecification_s98 v97
   {-# INLINE rule1943 #-}
   rule1943 = \  (_ :: ()) ->
     MaybeImportSpecification_Nothing
   {-# INLINE rule1944 #-}
   rule1944 = \ _self ->
     _self
{-# NOINLINE sem_MaybeImportSpecification_Just #-}
sem_MaybeImportSpecification_Just :: T_ImportSpecification  -> T_MaybeImportSpecification 
sem_MaybeImportSpecification_Just arg_importspecification_ = T_MaybeImportSpecification (return st98) where
   {-# NOINLINE st98 #-}
   st98 = let
      v97 :: T_MaybeImportSpecification_v97 
      v97 = \ (T_MaybeImportSpecification_vIn97 ) -> ( let
         _importspecificationX77 = Control.Monad.Identity.runIdentity (attach_T_ImportSpecification (arg_importspecification_))
         (T_ImportSpecification_vOut76 _importspecificationIself) = inv_ImportSpecification_s77 _importspecificationX77 (T_ImportSpecification_vIn76 )
         _self = rule1945 _importspecificationIself
         _lhsOself :: MaybeImportSpecification
         _lhsOself = rule1946 _self
         __result_ = T_MaybeImportSpecification_vOut97 _lhsOself
         in __result_ )
     in C_MaybeImportSpecification_s98 v97
   {-# INLINE rule1945 #-}
   rule1945 = \ ((_importspecificationIself) :: ImportSpecification) ->
     MaybeImportSpecification_Just _importspecificationIself
   {-# INLINE rule1946 #-}
   rule1946 = \ _self ->
     _self

-- MaybeInt ----------------------------------------------------
-- wrapper
data Inh_MaybeInt  = Inh_MaybeInt {  }
data Syn_MaybeInt  = Syn_MaybeInt { self_Syn_MaybeInt :: (MaybeInt) }
{-# INLINABLE wrap_MaybeInt #-}
wrap_MaybeInt :: T_MaybeInt  -> Inh_MaybeInt  -> (Syn_MaybeInt )
wrap_MaybeInt (T_MaybeInt act) (Inh_MaybeInt ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeInt_vIn100 
        (T_MaybeInt_vOut100 _lhsOself) <- return (inv_MaybeInt_s101 sem arg)
        return (Syn_MaybeInt _lhsOself)
   )

-- cata
{-# NOINLINE sem_MaybeInt #-}
sem_MaybeInt :: MaybeInt  -> T_MaybeInt 
sem_MaybeInt ( MaybeInt_Nothing  ) = sem_MaybeInt_Nothing 
sem_MaybeInt ( MaybeInt_Just int_ ) = sem_MaybeInt_Just int_

-- semantic domain
newtype T_MaybeInt  = T_MaybeInt {
                                 attach_T_MaybeInt :: Identity (T_MaybeInt_s101 )
                                 }
newtype T_MaybeInt_s101  = C_MaybeInt_s101 {
                                           inv_MaybeInt_s101 :: (T_MaybeInt_v100 )
                                           }
data T_MaybeInt_s102  = C_MaybeInt_s102
type T_MaybeInt_v100  = (T_MaybeInt_vIn100 ) -> (T_MaybeInt_vOut100 )
data T_MaybeInt_vIn100  = T_MaybeInt_vIn100 
data T_MaybeInt_vOut100  = T_MaybeInt_vOut100 (MaybeInt)
{-# NOINLINE sem_MaybeInt_Nothing #-}
sem_MaybeInt_Nothing ::  T_MaybeInt 
sem_MaybeInt_Nothing  = T_MaybeInt (return st101) where
   {-# NOINLINE st101 #-}
   st101 = let
      v100 :: T_MaybeInt_v100 
      v100 = \ (T_MaybeInt_vIn100 ) -> ( let
         _self = rule1947  ()
         _lhsOself :: MaybeInt
         _lhsOself = rule1948 _self
         __result_ = T_MaybeInt_vOut100 _lhsOself
         in __result_ )
     in C_MaybeInt_s101 v100
   {-# INLINE rule1947 #-}
   rule1947 = \  (_ :: ()) ->
     MaybeInt_Nothing
   {-# INLINE rule1948 #-}
   rule1948 = \ _self ->
     _self
{-# NOINLINE sem_MaybeInt_Just #-}
sem_MaybeInt_Just :: (Int) -> T_MaybeInt 
sem_MaybeInt_Just arg_int_ = T_MaybeInt (return st101) where
   {-# NOINLINE st101 #-}
   st101 = let
      v100 :: T_MaybeInt_v100 
      v100 = \ (T_MaybeInt_vIn100 ) -> ( let
         _self = rule1949 arg_int_
         _lhsOself :: MaybeInt
         _lhsOself = rule1950 _self
         __result_ = T_MaybeInt_vOut100 _lhsOself
         in __result_ )
     in C_MaybeInt_s101 v100
   {-# INLINE rule1949 #-}
   rule1949 = \ int_ ->
     MaybeInt_Just int_
   {-# INLINE rule1950 #-}
   rule1950 = \ _self ->
     _self

-- MaybeName ---------------------------------------------------
-- wrapper
data Inh_MaybeName  = Inh_MaybeName {  }
data Syn_MaybeName  = Syn_MaybeName { self_Syn_MaybeName :: (MaybeName) }
{-# INLINABLE wrap_MaybeName #-}
wrap_MaybeName :: T_MaybeName  -> Inh_MaybeName  -> (Syn_MaybeName )
wrap_MaybeName (T_MaybeName act) (Inh_MaybeName ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeName_vIn103 
        (T_MaybeName_vOut103 _lhsOself) <- return (inv_MaybeName_s104 sem arg)
        return (Syn_MaybeName _lhsOself)
   )

-- cata
{-# NOINLINE sem_MaybeName #-}
sem_MaybeName :: MaybeName  -> T_MaybeName 
sem_MaybeName ( MaybeName_Nothing  ) = sem_MaybeName_Nothing 
sem_MaybeName ( MaybeName_Just name_ ) = sem_MaybeName_Just ( sem_Name name_ )

-- semantic domain
newtype T_MaybeName  = T_MaybeName {
                                   attach_T_MaybeName :: Identity (T_MaybeName_s104 )
                                   }
newtype T_MaybeName_s104  = C_MaybeName_s104 {
                                             inv_MaybeName_s104 :: (T_MaybeName_v103 )
                                             }
data T_MaybeName_s105  = C_MaybeName_s105
type T_MaybeName_v103  = (T_MaybeName_vIn103 ) -> (T_MaybeName_vOut103 )
data T_MaybeName_vIn103  = T_MaybeName_vIn103 
data T_MaybeName_vOut103  = T_MaybeName_vOut103 (MaybeName)
{-# NOINLINE sem_MaybeName_Nothing #-}
sem_MaybeName_Nothing ::  T_MaybeName 
sem_MaybeName_Nothing  = T_MaybeName (return st104) where
   {-# NOINLINE st104 #-}
   st104 = let
      v103 :: T_MaybeName_v103 
      v103 = \ (T_MaybeName_vIn103 ) -> ( let
         _self = rule1951  ()
         _lhsOself :: MaybeName
         _lhsOself = rule1952 _self
         __result_ = T_MaybeName_vOut103 _lhsOself
         in __result_ )
     in C_MaybeName_s104 v103
   {-# INLINE rule1951 #-}
   rule1951 = \  (_ :: ()) ->
     MaybeName_Nothing
   {-# INLINE rule1952 #-}
   rule1952 = \ _self ->
     _self
{-# NOINLINE sem_MaybeName_Just #-}
sem_MaybeName_Just :: T_Name  -> T_MaybeName 
sem_MaybeName_Just arg_name_ = T_MaybeName (return st104) where
   {-# NOINLINE st104 #-}
   st104 = let
      v103 :: T_MaybeName_v103 
      v103 = \ (T_MaybeName_vIn103 ) -> ( let
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _self = rule1953 _nameIself
         _lhsOself :: MaybeName
         _lhsOself = rule1954 _self
         __result_ = T_MaybeName_vOut103 _lhsOself
         in __result_ )
     in C_MaybeName_s104 v103
   {-# INLINE rule1953 #-}
   rule1953 = \ ((_nameIself) :: Name) ->
     MaybeName_Just _nameIself
   {-# INLINE rule1954 #-}
   rule1954 = \ _self ->
     _self

-- MaybeNames --------------------------------------------------
-- wrapper
data Inh_MaybeNames  = Inh_MaybeNames {  }
data Syn_MaybeNames  = Syn_MaybeNames { self_Syn_MaybeNames :: (MaybeNames) }
{-# INLINABLE wrap_MaybeNames #-}
wrap_MaybeNames :: T_MaybeNames  -> Inh_MaybeNames  -> (Syn_MaybeNames )
wrap_MaybeNames (T_MaybeNames act) (Inh_MaybeNames ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeNames_vIn106 
        (T_MaybeNames_vOut106 _lhsOself) <- return (inv_MaybeNames_s107 sem arg)
        return (Syn_MaybeNames _lhsOself)
   )

-- cata
{-# NOINLINE sem_MaybeNames #-}
sem_MaybeNames :: MaybeNames  -> T_MaybeNames 
sem_MaybeNames ( MaybeNames_Nothing  ) = sem_MaybeNames_Nothing 
sem_MaybeNames ( MaybeNames_Just names_ ) = sem_MaybeNames_Just ( sem_Names names_ )

-- semantic domain
newtype T_MaybeNames  = T_MaybeNames {
                                     attach_T_MaybeNames :: Identity (T_MaybeNames_s107 )
                                     }
newtype T_MaybeNames_s107  = C_MaybeNames_s107 {
                                               inv_MaybeNames_s107 :: (T_MaybeNames_v106 )
                                               }
data T_MaybeNames_s108  = C_MaybeNames_s108
type T_MaybeNames_v106  = (T_MaybeNames_vIn106 ) -> (T_MaybeNames_vOut106 )
data T_MaybeNames_vIn106  = T_MaybeNames_vIn106 
data T_MaybeNames_vOut106  = T_MaybeNames_vOut106 (MaybeNames)
{-# NOINLINE sem_MaybeNames_Nothing #-}
sem_MaybeNames_Nothing ::  T_MaybeNames 
sem_MaybeNames_Nothing  = T_MaybeNames (return st107) where
   {-# NOINLINE st107 #-}
   st107 = let
      v106 :: T_MaybeNames_v106 
      v106 = \ (T_MaybeNames_vIn106 ) -> ( let
         _self = rule1955  ()
         _lhsOself :: MaybeNames
         _lhsOself = rule1956 _self
         __result_ = T_MaybeNames_vOut106 _lhsOself
         in __result_ )
     in C_MaybeNames_s107 v106
   {-# INLINE rule1955 #-}
   rule1955 = \  (_ :: ()) ->
     MaybeNames_Nothing
   {-# INLINE rule1956 #-}
   rule1956 = \ _self ->
     _self
{-# NOINLINE sem_MaybeNames_Just #-}
sem_MaybeNames_Just :: T_Names  -> T_MaybeNames 
sem_MaybeNames_Just arg_names_ = T_MaybeNames (return st107) where
   {-# NOINLINE st107 #-}
   st107 = let
      v106 :: T_MaybeNames_v106 
      v106 = \ (T_MaybeNames_vIn106 ) -> ( let
         _namesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_names_))
         (T_Names_vOut115 _namesIself) = inv_Names_s116 _namesX116 (T_Names_vIn115 )
         _self = rule1957 _namesIself
         _lhsOself :: MaybeNames
         _lhsOself = rule1958 _self
         __result_ = T_MaybeNames_vOut106 _lhsOself
         in __result_ )
     in C_MaybeNames_s107 v106
   {-# INLINE rule1957 #-}
   rule1957 = \ ((_namesIself) :: Names) ->
     MaybeNames_Just _namesIself
   {-# INLINE rule1958 #-}
   rule1958 = \ _self ->
     _self

-- Module ------------------------------------------------------
-- wrapper
data Inh_Module  = Inh_Module { baseName_Inh_Module :: (String), importEnvironments_Inh_Module :: (ImportEnvironments), options_Inh_Module :: ([Option]) }
data Syn_Module  = Syn_Module { collectEnvironment_Syn_Module :: (ImportEnvironment), errors_Syn_Module :: (Errors), self_Syn_Module :: (Module), typeSignatures_Syn_Module :: ([(Name,TpScheme)]), warnings_Syn_Module :: (Warnings) }
{-# INLINABLE wrap_Module #-}
wrap_Module :: T_Module  -> Inh_Module  -> (Syn_Module )
wrap_Module (T_Module act) (Inh_Module _lhsIbaseName _lhsIimportEnvironments _lhsIoptions) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Module_vIn109 _lhsIbaseName _lhsIimportEnvironments _lhsIoptions
        (T_Module_vOut109 _lhsOcollectEnvironment _lhsOerrors _lhsOself _lhsOtypeSignatures _lhsOwarnings) <- return (inv_Module_s110 sem arg)
        return (Syn_Module _lhsOcollectEnvironment _lhsOerrors _lhsOself _lhsOtypeSignatures _lhsOwarnings)
   )

-- cata
{-# INLINE sem_Module #-}
sem_Module :: Module  -> T_Module 
sem_Module ( Module_Module range_ name_ exports_ body_ ) = sem_Module_Module ( sem_Range range_ ) ( sem_MaybeName name_ ) ( sem_MaybeExports exports_ ) ( sem_Body body_ )

-- semantic domain
newtype T_Module  = T_Module {
                             attach_T_Module :: Identity (T_Module_s110 )
                             }
newtype T_Module_s110  = C_Module_s110 {
                                       inv_Module_s110 :: (T_Module_v109 )
                                       }
data T_Module_s111  = C_Module_s111
type T_Module_v109  = (T_Module_vIn109 ) -> (T_Module_vOut109 )
data T_Module_vIn109  = T_Module_vIn109 (String) (ImportEnvironments) ([Option])
data T_Module_vOut109  = T_Module_vOut109 (ImportEnvironment) (Errors) (Module) ([(Name,TpScheme)]) (Warnings)
{-# NOINLINE sem_Module_Module #-}
sem_Module_Module :: T_Range  -> T_MaybeName  -> T_MaybeExports  -> T_Body  -> T_Module 
sem_Module_Module arg_range_ arg_name_ arg_exports_ arg_body_ = T_Module (return st110) where
   {-# NOINLINE st110 #-}
   st110 = let
      v109 :: T_Module_v109 
      v109 = \ (T_Module_vIn109 _lhsIbaseName _lhsIimportEnvironments _lhsIoptions) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX104 = Control.Monad.Identity.runIdentity (attach_T_MaybeName (arg_name_))
         _exportsX92 = Control.Monad.Identity.runIdentity (attach_T_MaybeExports (arg_exports_))
         _bodyX14 = Control.Monad.Identity.runIdentity (attach_T_Body (arg_body_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_MaybeName_vOut103 _nameIself) = inv_MaybeName_s104 _nameX104 (T_MaybeName_vIn103 )
         (T_MaybeExports_vOut91 _exportsIexportErrors _exportsIself) = inv_MaybeExports_s92 _exportsX92 (T_MaybeExports_vIn91 _exportsOconsInScope _exportsOmodulesInScope _exportsOnamesInScop _exportsOtyconsInScope)
         (T_Body_vOut13 _bodyIcollectInstances _bodyIcollectScopeInfos _bodyIcollectTypeConstructors _bodyIcollectTypeSynonyms _bodyIcollectValueConstructors _bodyIcounter _bodyIdeclVarNames _bodyIimportedModules _bodyIkindErrors _bodyImiscerrors _bodyIoperatorFixities _bodyIself _bodyItypeSignatures _bodyIunboundNames _bodyIwarnings) = inv_Body_s14 _bodyX14 (T_Body_vIn13 _bodyOallTypeConstructors _bodyOallValueConstructors _bodyOclassEnvironment _bodyOcollectScopeInfos _bodyOcollectTypeConstructors _bodyOcollectTypeSynonyms _bodyOcollectValueConstructors _bodyOcounter _bodyOkindErrors _bodyOmiscerrors _bodyOnamesInScope _bodyOoperatorFixities _bodyOoptions _bodyOorderedTypeSynonyms _bodyOtypeConstructors _bodyOvalueConstructors _bodyOwarnings)
         _lhsOerrors :: Errors
         _lhsOerrors = rule1959 _allErrors _derivedRanges _removedEntities
         _lhsOwarnings :: Warnings
         _lhsOwarnings = rule1960 _scopeWarnings _warnings
         _allErrors = rule1961 _exportErrors _kindErrors _lhsIoptions _miscerrors _scopeErrors _topLevelErrors
         _removedEntities = rule1962 _duplicatedTypeConstructors _duplicatedValueConstructors
         _derivedRanges = rule1963 _derivedFunctions
         _initialScope = rule1964 _derivedFunctions _lhsIimportEnvironments
         _collectEnvironment = rule1965 _bodyIcollectTypeConstructors _bodyIcollectTypeSynonyms _bodyIcollectValueConstructors _bodyIoperatorFixities _derivedFunctions
         _derivedFunctions = rule1966 _bodyIcollectTypeConstructors _bodyIcollectTypeSynonyms
         _bodyOcollectTypeConstructors = rule1967  ()
         _bodyOcollectValueConstructors = rule1968  ()
         _bodyOcollectTypeSynonyms = rule1969  ()
         _bodyOoperatorFixities = rule1970  ()
         (_uniqueValueConstructors,_duplicatedValueConstructors) = rule1971 _bodyIcollectValueConstructors _lhsIimportEnvironments
         _allValueConstructors = rule1972 _duplicatedValueConstructors _uniqueValueConstructors
         _valueConstructors = rule1973 _uniqueValueConstructors
         (_uniqueTypeConstructors,_duplicatedTypeConstructors) = rule1974 _bodyIcollectTypeConstructors _bodyIcollectTypeSynonyms _lhsIimportEnvironments
         _allTypeConstructors = rule1975 _duplicatedTypeConstructors _uniqueTypeConstructors
         _typeConstructors = rule1976 _uniqueTypeConstructors
         _bodyOorderedTypeSynonyms = rule1977 _bodyIcollectTypeSynonyms _lhsIimportEnvironments
         _bodyOclassEnvironment = rule1978 _bodyIcollectInstances _lhsIimportEnvironments
         (_namesInScope,_unboundNames,_scopeInfo) = rule1979 _bodyIdeclVarNames _bodyIunboundNames _initialScope
         _bodyOcounter = rule1980  ()
         _bodyOkindErrors = rule1981  ()
         _kindErrors = rule1982 _bodyIkindErrors
         _bodyOwarnings = rule1983  ()
         _warnings = rule1984 _bodyIwarnings
         _topLevelErrors = rule1985 _fixityButNoFunDefErrors _fixityErrors _recursiveTypeSynonymErrors _typeConstructorErrors _valueConstructorErrors _wrongFileNameErrors _wrongFlagErrors
         _typeConstructorErrors = rule1986 _duplicatedTypeConstructors
         _valueConstructorErrors = rule1987 _duplicatedValueConstructors
         _fixityErrors = rule1988 _duplicatedFixities
         (_duplicatedFixities,_correctFixities) = rule1989 _bodyIoperatorFixities
         _fixityButNoFunDefErrors = rule1990 _allValueConstructors _bodyIdeclVarNames _correctFixities
         _wrongFlagErrors = rule1991 _lhsIimportEnvironments _lhsIoptions
         _recursiveTypeSynonymErrors = rule1992 _bodyIcollectTypeSynonyms
         _wrongFileNameErrors = rule1993 _lhsIbaseName _moduleName
         _moduleName = rule1994 _nameIself
         _fileName = rule1995 _lhsIbaseName
         _bodyOmiscerrors = rule1996  ()
         _miscerrors = rule1997 _bodyImiscerrors
         _exportsOnamesInScop = rule1998 _bodyIdeclVarNames _derivedFunctions _lhsIimportEnvironments
         _exportsOmodulesInScope = rule1999 _bodyIimportedModules _fileName _moduleName
         _exportsOtyconsInScope = rule2000 _allTypeConstructors
         _exportsOconsInScope = rule2001 _allValueConstructors
         _exportErrors = rule2002 _exportsIexportErrors
         _bodyOcollectScopeInfos = rule2003  ()
         _scopeErrors = rule2004 _collectScopeInfos
         _scopeWarnings = rule2005 _collectScopeInfos
         _collectScopeInfos = rule2006 _bodyIcollectScopeInfos _scopeInfo
         _self = rule2007 _bodyIself _exportsIself _nameIself _rangeIself
         _lhsOself :: Module
         _lhsOself = rule2008 _self
         _lhsOcollectEnvironment :: ImportEnvironment
         _lhsOcollectEnvironment = rule2009 _collectEnvironment
         _lhsOtypeSignatures :: [(Name,TpScheme)]
         _lhsOtypeSignatures = rule2010 _bodyItypeSignatures
         _bodyOallTypeConstructors = rule2011 _allTypeConstructors
         _bodyOallValueConstructors = rule2012 _allValueConstructors
         _bodyOnamesInScope = rule2013 _namesInScope
         _bodyOoptions = rule2014 _lhsIoptions
         _bodyOtypeConstructors = rule2015 _typeConstructors
         _bodyOvalueConstructors = rule2016 _valueConstructors
         __result_ = T_Module_vOut109 _lhsOcollectEnvironment _lhsOerrors _lhsOself _lhsOtypeSignatures _lhsOwarnings
         in __result_ )
     in C_Module_s110 v109
   {-# INLINE rule1959 #-}
   rule1959 = \ _allErrors _derivedRanges _removedEntities ->
                              filter (\err -> filterRemovedNames _removedEntities err
                                           && filterDerivedNames _derivedRanges err) _allErrors
   {-# INLINE rule1960 #-}
   rule1960 = \ _scopeWarnings _warnings ->
                                 _scopeWarnings ++ _warnings
   {-# INLINE rule1961 #-}
   rule1961 = \ _exportErrors _kindErrors ((_lhsIoptions) :: [Option]) _miscerrors _scopeErrors _topLevelErrors ->
                                 concat [ _exportErrors
                                        , _scopeErrors
                                        , _miscerrors
                                        , if KindInferencing `elem` _lhsIoptions then [] else _kindErrors
                                        , _topLevelErrors
                                        ]
   {-# INLINE rule1962 #-}
   rule1962 = \ _duplicatedTypeConstructors _duplicatedValueConstructors ->
                                       [ (name,TypeConstructor) | name:_ <- _duplicatedTypeConstructors  ] ++
                                       [ (name,Constructor    ) | name:_ <- _duplicatedValueConstructors ]
   {-# INLINE rule1963 #-}
   rule1963 = \ _derivedFunctions ->
                                       map getNameRange (map fst _derivedFunctions)
   {-# INLINE rule1964 #-}
   rule1964 = \ _derivedFunctions ((_lhsIimportEnvironments) :: ImportEnvironments) ->
                                       map fst _derivedFunctions ++
                                       concatMap (M.keys . typeEnvironment) _lhsIimportEnvironments
   {-# INLINE rule1965 #-}
   rule1965 = \ ((_bodyIcollectTypeConstructors) :: [(Name,Int)]) ((_bodyIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ((_bodyIcollectValueConstructors) :: [(Name,TpScheme)]) ((_bodyIoperatorFixities) :: [(Name,(Int,Assoc))]) _derivedFunctions ->
                                          setValueConstructors   (M.fromList _bodyIcollectValueConstructors)
                                          . setTypeConstructors  (M.fromList _bodyIcollectTypeConstructors)
                                          . setTypeSynonyms      (M.fromList _bodyIcollectTypeSynonyms)
                                          . setOperatorTable     (M.fromList _bodyIoperatorFixities)
                                          . addToTypeEnvironment (M.fromList _derivedFunctions)
                                          $ emptyEnvironment
   {-# INLINE rule1966 #-}
   rule1966 = \ ((_bodyIcollectTypeConstructors) :: [(Name,Int)]) ((_bodyIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
                                        let f (n,i) = ( nameOfShowFunction n
                                                      , typeOfShowFunction n (take i [ nameFromString s | s <- variableList])
                                                      )
                                            g (n,(i,_)) = f (n,i)
                                        in map f _bodyIcollectTypeConstructors ++
                                           map g _bodyIcollectTypeSynonyms
   {-# INLINE rule1967 #-}
   rule1967 = \  (_ :: ()) ->
                                                         []
   {-# INLINE rule1968 #-}
   rule1968 = \  (_ :: ()) ->
                                                          []
   {-# INLINE rule1969 #-}
   rule1969 = \  (_ :: ()) ->
                                                     []
   {-# INLINE rule1970 #-}
   rule1970 = \  (_ :: ()) ->
                                                  []
   {-# INLINE rule1971 #-}
   rule1971 = \ ((_bodyIcollectValueConstructors) :: [(Name,TpScheme)]) ((_lhsIimportEnvironments) :: ImportEnvironments) ->
                        uniqueKeys (  _bodyIcollectValueConstructors
                                   ++ concatMap (M.assocs . valueConstructors) _lhsIimportEnvironments
                                   )
   {-# INLINE rule1972 #-}
   rule1972 = \ _duplicatedValueConstructors _uniqueValueConstructors ->
                                            map fst _uniqueValueConstructors ++ map head _duplicatedValueConstructors
   {-# INLINE rule1973 #-}
   rule1973 = \ _uniqueValueConstructors ->
                                            M.fromList _uniqueValueConstructors
   {-# INLINE rule1974 #-}
   rule1974 = \ ((_bodyIcollectTypeConstructors) :: [(Name,Int)]) ((_bodyIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ((_lhsIimportEnvironments) :: ImportEnvironments) ->
                      uniqueKeys (  _bodyIcollectTypeConstructors
                                 ++ concatMap (M.assocs . typeConstructors) _lhsIimportEnvironments
                                 ++ [ (n,i) | (n,(i,_)) <- _bodyIcollectTypeSynonyms ]
                                 )
   {-# INLINE rule1975 #-}
   rule1975 = \ _duplicatedTypeConstructors _uniqueTypeConstructors ->
                                         map fst _uniqueTypeConstructors ++ map head _duplicatedTypeConstructors
   {-# INLINE rule1976 #-}
   rule1976 = \ _uniqueTypeConstructors ->
                                         M.fromList _uniqueTypeConstructors
   {-# INLINE rule1977 #-}
   rule1977 = \ ((_bodyIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ((_lhsIimportEnvironments) :: ImportEnvironments) ->
                        let list     = concatMap (M.assocs . typeSynonyms) _lhsIimportEnvironments ++
                                       _bodyIcollectTypeSynonyms
                            newmap   = M.fromList [ (show name, t) | (name, t) <- list ]
                            ordering = fst (getTypeSynonymOrdering newmap)
                        in (ordering, newmap)
   {-# INLINE rule1978 #-}
   rule1978 = \ ((_bodyIcollectInstances) :: [(Name, Instance)]) ((_lhsIimportEnvironments) :: ImportEnvironments) ->
            let importEnv = foldr combineImportEnvironments emptyEnvironment _lhsIimportEnvironments
            in foldr (\(n, i) -> insertInstance (show n) i)
                     (createClassEnvironment importEnv)
                     _bodyIcollectInstances
   {-# INLINE rule1979 #-}
   rule1979 = \ ((_bodyIdeclVarNames) :: Names) ((_bodyIunboundNames) :: Names) _initialScope ->
                                                               changeOfScope (_initialScope ++ _bodyIdeclVarNames) _bodyIunboundNames []
   {-# INLINE rule1980 #-}
   rule1980 = \  (_ :: ()) ->
                                0
   {-# INLINE rule1981 #-}
   rule1981 = \  (_ :: ()) ->
                                         []
   {-# INLINE rule1982 #-}
   rule1982 = \ ((_bodyIkindErrors) :: [Error]) ->
                                         _bodyIkindErrors
   {-# INLINE rule1983 #-}
   rule1983 = \  (_ :: ()) ->
                                  []
   {-# INLINE rule1984 #-}
   rule1984 = \ ((_bodyIwarnings) :: [Warning]) ->
                                  _bodyIwarnings
   {-# INLINE rule1985 #-}
   rule1985 = \ _fixityButNoFunDefErrors _fixityErrors _recursiveTypeSynonymErrors _typeConstructorErrors _valueConstructorErrors _wrongFileNameErrors _wrongFlagErrors ->
                                      concat [ _typeConstructorErrors
                                             , _valueConstructorErrors
                                             , _fixityErrors
                                             , _fixityButNoFunDefErrors
                                             , _wrongFlagErrors
                                             , _recursiveTypeSynonymErrors
                                             , _wrongFileNameErrors
                                             ]
   {-# INLINE rule1986 #-}
   rule1986 = \ _duplicatedTypeConstructors ->
                                             makeDuplicated TypeConstructor _duplicatedTypeConstructors
   {-# INLINE rule1987 #-}
   rule1987 = \ _duplicatedValueConstructors ->
                                              makeDuplicated Constructor _duplicatedValueConstructors
   {-# INLINE rule1988 #-}
   rule1988 = \ _duplicatedFixities ->
                                    makeDuplicated Fixity _duplicatedFixities
   {-# INLINE rule1989 #-}
   rule1989 = \ ((_bodyIoperatorFixities) :: [(Name,(Int,Assoc))]) ->
                                                            let (xs,ys) = partition ((>1) . length) . group . sort $ (map fst _bodyIoperatorFixities)
                                                            in (xs,map head ys)
   {-# INLINE rule1990 #-}
   rule1990 = \ _allValueConstructors ((_bodyIdeclVarNames) :: Names) _correctFixities ->
                                               let list = nub (_bodyIdeclVarNames ++ _allValueConstructors)
                                               in makeNoFunDef Fixity (filter (`notElem` list) _correctFixities) list
   {-# INLINE rule1991 #-}
   rule1991 = \ ((_lhsIimportEnvironments) :: ImportEnvironments) ((_lhsIoptions) :: [Option]) ->
         [ WrongOverloadingFlag flag
         | let flag = Overloading `elem` _lhsIoptions
               imp  = any isOverloaded (concatMap (M.elems . typeEnvironment) _lhsIimportEnvironments)
         , flag /= imp
         ]
   {-# INLINE rule1992 #-}
   rule1992 = \ ((_bodyIcollectTypeSynonyms) :: [(Name,(Int,Tps -> Tp))]) ->
                        let converted  = map (\(name, tuple) -> (show name, tuple)) _bodyIcollectTypeSynonyms
                            recursives = snd . getTypeSynonymOrdering . M.fromList $ converted
                            makeError = let f = foldr add (Just [])
                                            add s ml = case (g s, ml) of
                                                          ([n], Just ns) -> Just (n:ns)
                                                          _              -> Nothing
                                            g s = [ n | n <- map fst _bodyIcollectTypeSynonyms, show n == s ]
                                        in maybe [] (\x -> [RecursiveTypeSynonyms x]) . f
                        in concatMap makeError recursives
   {-# INLINE rule1993 #-}
   rule1993 = \ ((_lhsIbaseName) :: String) _moduleName ->
                                          let moduleString = getNameName  _moduleName
                                              moduleRange  = getNameRange _moduleName
                                          in if moduleString == "" || _lhsIbaseName == moduleString
                                            then []
                                            else [ WrongFileName _lhsIbaseName moduleString moduleRange ]
   {-# INLINE rule1994 #-}
   rule1994 = \ ((_nameIself) :: MaybeName) ->
                                     case _nameIself of
                                        MaybeName_Just name -> name
                                        MaybeName_Nothing   -> Name_Identifier noRange [] ""
   {-# INLINE rule1995 #-}
   rule1995 = \ ((_lhsIbaseName) :: String) ->
                                     Name_Identifier noRange [] _lhsIbaseName
   {-# INLINE rule1996 #-}
   rule1996 = \  (_ :: ()) ->
                                  []
   {-# INLINE rule1997 #-}
   rule1997 = \ ((_bodyImiscerrors) :: [Error]) ->
                                  _bodyImiscerrors
   {-# INLINE rule1998 #-}
   rule1998 = \ ((_bodyIdeclVarNames) :: Names) _derivedFunctions ((_lhsIimportEnvironments) :: ImportEnvironments) ->
                                        concat [ _bodyIdeclVarNames
                                                , concatMap (M.keys . typeEnvironment) _lhsIimportEnvironments
                                                , map fst _derivedFunctions
                                                ]
   {-# INLINE rule1999 #-}
   rule1999 = \ ((_bodyIimportedModules) :: Names) _fileName _moduleName ->
                                         (_moduleName : _fileName : _bodyIimportedModules)
   {-# INLINE rule2000 #-}
   rule2000 = \ _allTypeConstructors ->
                                         _allTypeConstructors
   {-# INLINE rule2001 #-}
   rule2001 = \ _allValueConstructors ->
                                         _allValueConstructors
   {-# INLINE rule2002 #-}
   rule2002 = \ ((_exportsIexportErrors) :: [Error]) ->
                                     _exportsIexportErrors
   {-# INLINE rule2003 #-}
   rule2003 = \  (_ :: ()) ->
                                         []
   {-# INLINE rule2004 #-}
   rule2004 = \ _collectScopeInfos ->
                                         makeErrors   _collectScopeInfos
   {-# INLINE rule2005 #-}
   rule2005 = \ _collectScopeInfos ->
                                         makeWarnings _collectScopeInfos
   {-# INLINE rule2006 #-}
   rule2006 = \ ((_bodyIcollectScopeInfos) :: [(ScopeInfo, Entity)]) _scopeInfo ->
                                       (topLevelScopeInfo _scopeInfo, Definition) : _bodyIcollectScopeInfos
   {-# INLINE rule2007 #-}
   rule2007 = \ ((_bodyIself) :: Body) ((_exportsIself) :: MaybeExports) ((_nameIself) :: MaybeName) ((_rangeIself) :: Range) ->
     Module_Module _rangeIself _nameIself _exportsIself _bodyIself
   {-# INLINE rule2008 #-}
   rule2008 = \ _self ->
     _self
   {-# INLINE rule2009 #-}
   rule2009 = \ _collectEnvironment ->
     _collectEnvironment
   {-# INLINE rule2010 #-}
   rule2010 = \ ((_bodyItypeSignatures) :: [(Name,TpScheme)]) ->
     _bodyItypeSignatures
   {-# INLINE rule2011 #-}
   rule2011 = \ _allTypeConstructors ->
     _allTypeConstructors
   {-# INLINE rule2012 #-}
   rule2012 = \ _allValueConstructors ->
     _allValueConstructors
   {-# INLINE rule2013 #-}
   rule2013 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule2014 #-}
   rule2014 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2015 #-}
   rule2015 = \ _typeConstructors ->
     _typeConstructors
   {-# INLINE rule2016 #-}
   rule2016 = \ _valueConstructors ->
     _valueConstructors

-- Name --------------------------------------------------------
-- wrapper
data Inh_Name  = Inh_Name {  }
data Syn_Name  = Syn_Name { self_Syn_Name :: (Name) }
{-# INLINABLE wrap_Name #-}
wrap_Name :: T_Name  -> Inh_Name  -> (Syn_Name )
wrap_Name (T_Name act) (Inh_Name ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Name_vIn112 
        (T_Name_vOut112 _lhsOself) <- return (inv_Name_s113 sem arg)
        return (Syn_Name _lhsOself)
   )

-- cata
{-# NOINLINE sem_Name #-}
sem_Name :: Name  -> T_Name 
sem_Name ( Name_Identifier range_ module_ name_ ) = sem_Name_Identifier ( sem_Range range_ ) ( sem_Strings module_ ) name_
sem_Name ( Name_Operator range_ module_ name_ ) = sem_Name_Operator ( sem_Range range_ ) ( sem_Strings module_ ) name_
sem_Name ( Name_Special range_ module_ name_ ) = sem_Name_Special ( sem_Range range_ ) ( sem_Strings module_ ) name_

-- semantic domain
newtype T_Name  = T_Name {
                         attach_T_Name :: Identity (T_Name_s113 )
                         }
newtype T_Name_s113  = C_Name_s113 {
                                   inv_Name_s113 :: (T_Name_v112 )
                                   }
data T_Name_s114  = C_Name_s114
type T_Name_v112  = (T_Name_vIn112 ) -> (T_Name_vOut112 )
data T_Name_vIn112  = T_Name_vIn112 
data T_Name_vOut112  = T_Name_vOut112 (Name)
{-# NOINLINE sem_Name_Identifier #-}
sem_Name_Identifier :: T_Range  -> T_Strings  -> (String) -> T_Name 
sem_Name_Identifier arg_range_ arg_module_ arg_name_ = T_Name (return st113) where
   {-# NOINLINE st113 #-}
   st113 = let
      v112 :: T_Name_v112 
      v112 = \ (T_Name_vIn112 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _moduleX161 = Control.Monad.Identity.runIdentity (attach_T_Strings (arg_module_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Strings_vOut160 _moduleIself) = inv_Strings_s161 _moduleX161 (T_Strings_vIn160 )
         _self = rule2017 _moduleIself _rangeIself arg_name_
         _lhsOself :: Name
         _lhsOself = rule2018 _self
         __result_ = T_Name_vOut112 _lhsOself
         in __result_ )
     in C_Name_s113 v112
   {-# INLINE rule2017 #-}
   rule2017 = \ ((_moduleIself) :: Strings) ((_rangeIself) :: Range) name_ ->
     Name_Identifier _rangeIself _moduleIself name_
   {-# INLINE rule2018 #-}
   rule2018 = \ _self ->
     _self
{-# NOINLINE sem_Name_Operator #-}
sem_Name_Operator :: T_Range  -> T_Strings  -> (String) -> T_Name 
sem_Name_Operator arg_range_ arg_module_ arg_name_ = T_Name (return st113) where
   {-# NOINLINE st113 #-}
   st113 = let
      v112 :: T_Name_v112 
      v112 = \ (T_Name_vIn112 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _moduleX161 = Control.Monad.Identity.runIdentity (attach_T_Strings (arg_module_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Strings_vOut160 _moduleIself) = inv_Strings_s161 _moduleX161 (T_Strings_vIn160 )
         _self = rule2019 _moduleIself _rangeIself arg_name_
         _lhsOself :: Name
         _lhsOself = rule2020 _self
         __result_ = T_Name_vOut112 _lhsOself
         in __result_ )
     in C_Name_s113 v112
   {-# INLINE rule2019 #-}
   rule2019 = \ ((_moduleIself) :: Strings) ((_rangeIself) :: Range) name_ ->
     Name_Operator _rangeIself _moduleIself name_
   {-# INLINE rule2020 #-}
   rule2020 = \ _self ->
     _self
{-# NOINLINE sem_Name_Special #-}
sem_Name_Special :: T_Range  -> T_Strings  -> (String) -> T_Name 
sem_Name_Special arg_range_ arg_module_ arg_name_ = T_Name (return st113) where
   {-# NOINLINE st113 #-}
   st113 = let
      v112 :: T_Name_v112 
      v112 = \ (T_Name_vIn112 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _moduleX161 = Control.Monad.Identity.runIdentity (attach_T_Strings (arg_module_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Strings_vOut160 _moduleIself) = inv_Strings_s161 _moduleX161 (T_Strings_vIn160 )
         _self = rule2021 _moduleIself _rangeIself arg_name_
         _lhsOself :: Name
         _lhsOself = rule2022 _self
         __result_ = T_Name_vOut112 _lhsOself
         in __result_ )
     in C_Name_s113 v112
   {-# INLINE rule2021 #-}
   rule2021 = \ ((_moduleIself) :: Strings) ((_rangeIself) :: Range) name_ ->
     Name_Special _rangeIself _moduleIself name_
   {-# INLINE rule2022 #-}
   rule2022 = \ _self ->
     _self

-- Names -------------------------------------------------------
-- wrapper
data Inh_Names  = Inh_Names {  }
data Syn_Names  = Syn_Names { self_Syn_Names :: (Names) }
{-# INLINABLE wrap_Names #-}
wrap_Names :: T_Names  -> Inh_Names  -> (Syn_Names )
wrap_Names (T_Names act) (Inh_Names ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Names_vIn115 
        (T_Names_vOut115 _lhsOself) <- return (inv_Names_s116 sem arg)
        return (Syn_Names _lhsOself)
   )

-- cata
{-# NOINLINE sem_Names #-}
sem_Names :: Names  -> T_Names 
sem_Names list = Prelude.foldr sem_Names_Cons sem_Names_Nil (Prelude.map sem_Name list)

-- semantic domain
newtype T_Names  = T_Names {
                           attach_T_Names :: Identity (T_Names_s116 )
                           }
newtype T_Names_s116  = C_Names_s116 {
                                     inv_Names_s116 :: (T_Names_v115 )
                                     }
data T_Names_s117  = C_Names_s117
type T_Names_v115  = (T_Names_vIn115 ) -> (T_Names_vOut115 )
data T_Names_vIn115  = T_Names_vIn115 
data T_Names_vOut115  = T_Names_vOut115 (Names)
{-# NOINLINE sem_Names_Cons #-}
sem_Names_Cons :: T_Name  -> T_Names  -> T_Names 
sem_Names_Cons arg_hd_ arg_tl_ = T_Names (return st116) where
   {-# NOINLINE st116 #-}
   st116 = let
      v115 :: T_Names_v115 
      v115 = \ (T_Names_vIn115 ) -> ( let
         _hdX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_hd_))
         _tlX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_tl_))
         (T_Name_vOut112 _hdIself) = inv_Name_s113 _hdX113 (T_Name_vIn112 )
         (T_Names_vOut115 _tlIself) = inv_Names_s116 _tlX116 (T_Names_vIn115 )
         _self = rule2023 _hdIself _tlIself
         _lhsOself :: Names
         _lhsOself = rule2024 _self
         __result_ = T_Names_vOut115 _lhsOself
         in __result_ )
     in C_Names_s116 v115
   {-# INLINE rule2023 #-}
   rule2023 = \ ((_hdIself) :: Name) ((_tlIself) :: Names) ->
     (:) _hdIself _tlIself
   {-# INLINE rule2024 #-}
   rule2024 = \ _self ->
     _self
{-# NOINLINE sem_Names_Nil #-}
sem_Names_Nil ::  T_Names 
sem_Names_Nil  = T_Names (return st116) where
   {-# NOINLINE st116 #-}
   st116 = let
      v115 :: T_Names_v115 
      v115 = \ (T_Names_vIn115 ) -> ( let
         _self = rule2025  ()
         _lhsOself :: Names
         _lhsOself = rule2026 _self
         __result_ = T_Names_vOut115 _lhsOself
         in __result_ )
     in C_Names_s116 v115
   {-# INLINE rule2025 #-}
   rule2025 = \  (_ :: ()) ->
     []
   {-# INLINE rule2026 #-}
   rule2026 = \ _self ->
     _self

-- Pattern -----------------------------------------------------
-- wrapper
data Inh_Pattern  = Inh_Pattern { allTypeConstructors_Inh_Pattern :: (Names), allValueConstructors_Inh_Pattern :: (Names), collectScopeInfos_Inh_Pattern :: ([(ScopeInfo, Entity)]), counter_Inh_Pattern :: (Int), lhsPattern_Inh_Pattern :: (Bool), miscerrors_Inh_Pattern :: ([Error]), namesInScope_Inh_Pattern :: (Names), typeConstructors_Inh_Pattern :: (M.Map Name Int), valueConstructors_Inh_Pattern :: (M.Map Name TpScheme), warnings_Inh_Pattern :: ([Warning]) }
data Syn_Pattern  = Syn_Pattern { collectScopeInfos_Syn_Pattern :: ([(ScopeInfo, Entity)]), counter_Syn_Pattern :: (Int), miscerrors_Syn_Pattern :: ([Error]), patVarNames_Syn_Pattern :: (Names), self_Syn_Pattern :: (Pattern), unboundNames_Syn_Pattern :: (Names), warnings_Syn_Pattern :: ([Warning]) }
{-# INLINABLE wrap_Pattern #-}
wrap_Pattern :: T_Pattern  -> Inh_Pattern  -> (Syn_Pattern )
wrap_Pattern (T_Pattern act) (Inh_Pattern _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_Pattern_s119 sem arg)
        return (Syn_Pattern _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Pattern #-}
sem_Pattern :: Pattern  -> T_Pattern 
sem_Pattern ( Pattern_Hole range_ id_ ) = sem_Pattern_Hole ( sem_Range range_ ) id_
sem_Pattern ( Pattern_Literal range_ literal_ ) = sem_Pattern_Literal ( sem_Range range_ ) ( sem_Literal literal_ )
sem_Pattern ( Pattern_Variable range_ name_ ) = sem_Pattern_Variable ( sem_Range range_ ) ( sem_Name name_ )
sem_Pattern ( Pattern_Constructor range_ name_ patterns_ ) = sem_Pattern_Constructor ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Patterns patterns_ )
sem_Pattern ( Pattern_Parenthesized range_ pattern_ ) = sem_Pattern_Parenthesized ( sem_Range range_ ) ( sem_Pattern pattern_ )
sem_Pattern ( Pattern_InfixConstructor range_ leftPattern_ constructorOperator_ rightPattern_ ) = sem_Pattern_InfixConstructor ( sem_Range range_ ) ( sem_Pattern leftPattern_ ) ( sem_Name constructorOperator_ ) ( sem_Pattern rightPattern_ )
sem_Pattern ( Pattern_List range_ patterns_ ) = sem_Pattern_List ( sem_Range range_ ) ( sem_Patterns patterns_ )
sem_Pattern ( Pattern_Tuple range_ patterns_ ) = sem_Pattern_Tuple ( sem_Range range_ ) ( sem_Patterns patterns_ )
sem_Pattern ( Pattern_Record range_ name_ recordPatternBindings_ ) = sem_Pattern_Record ( sem_Range range_ ) ( sem_Name name_ ) ( sem_RecordPatternBindings recordPatternBindings_ )
sem_Pattern ( Pattern_Negate range_ literal_ ) = sem_Pattern_Negate ( sem_Range range_ ) ( sem_Literal literal_ )
sem_Pattern ( Pattern_As range_ name_ pattern_ ) = sem_Pattern_As ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Pattern pattern_ )
sem_Pattern ( Pattern_Wildcard range_ ) = sem_Pattern_Wildcard ( sem_Range range_ )
sem_Pattern ( Pattern_Irrefutable range_ pattern_ ) = sem_Pattern_Irrefutable ( sem_Range range_ ) ( sem_Pattern pattern_ )
sem_Pattern ( Pattern_Successor range_ name_ literal_ ) = sem_Pattern_Successor ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Literal literal_ )
sem_Pattern ( Pattern_NegateFloat range_ literal_ ) = sem_Pattern_NegateFloat ( sem_Range range_ ) ( sem_Literal literal_ )

-- semantic domain
newtype T_Pattern  = T_Pattern {
                               attach_T_Pattern :: Identity (T_Pattern_s119 )
                               }
newtype T_Pattern_s119  = C_Pattern_s119 {
                                         inv_Pattern_s119 :: (T_Pattern_v118 )
                                         }
data T_Pattern_s120  = C_Pattern_s120
type T_Pattern_v118  = (T_Pattern_vIn118 ) -> (T_Pattern_vOut118 )
data T_Pattern_vIn118  = T_Pattern_vIn118 (Names) (Names) ([(ScopeInfo, Entity)]) (Int) (Bool) ([Error]) (Names) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_Pattern_vOut118  = T_Pattern_vOut118 ([(ScopeInfo, Entity)]) (Int) ([Error]) (Names) (Pattern) (Names) ([Warning])
{-# NOINLINE sem_Pattern_Hole #-}
sem_Pattern_Hole :: T_Range  -> (Integer) -> T_Pattern 
sem_Pattern_Hole arg_range_ arg_id_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2027 _i
         _lhsOcounter :: Int
         _i :: Int
         (_lhsOcounter,_i) = rule2028 _lhsIcounter
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2029  ()
         _self = rule2030 _rangeIself arg_id_
         _lhsOself :: Pattern
         _lhsOself = rule2031 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2032 _lhsIcollectScopeInfos
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2033 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2034 _lhsIwarnings
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2027 #-}
   rule2027 = \ ((_i) :: Int) ->
                                     [ Name_Special noRange [] ("hole" ++ show _i    ) ]
   {-# INLINE rule2028 #-}
   rule2028 = \ ((_lhsIcounter) :: Int) ->
     let __cont = _lhsIcounter in seq __cont ( case nextUnique __cont of { (__cont, i) -> (__cont,i)} )
   {-# INLINE rule2029 #-}
   rule2029 = \  (_ :: ()) ->
     []
   {-# INLINE rule2030 #-}
   rule2030 = \ ((_rangeIself) :: Range) id_ ->
     Pattern_Hole _rangeIself id_
   {-# INLINE rule2031 #-}
   rule2031 = \ _self ->
     _self
   {-# INLINE rule2032 #-}
   rule2032 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2033 #-}
   rule2033 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2034 #-}
   rule2034 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Pattern_Literal #-}
sem_Pattern_Literal :: T_Range  -> T_Literal  -> T_Pattern 
sem_Pattern_Literal arg_range_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalIcollectScopeInfos _literalImiscerrors _literalIself) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 _literalOcollectScopeInfos _literalOmiscerrors)
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2035  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2036  ()
         _self = rule2037 _literalIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2038 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2039 _literalIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2040 _lhsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2041 _literalImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2042 _lhsIwarnings
         _literalOcollectScopeInfos = rule2043 _lhsIcollectScopeInfos
         _literalOmiscerrors = rule2044 _lhsImiscerrors
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2035 #-}
   rule2035 = \  (_ :: ()) ->
     []
   {-# INLINE rule2036 #-}
   rule2036 = \  (_ :: ()) ->
     []
   {-# INLINE rule2037 #-}
   rule2037 = \ ((_literalIself) :: Literal) ((_rangeIself) :: Range) ->
     Pattern_Literal _rangeIself _literalIself
   {-# INLINE rule2038 #-}
   rule2038 = \ _self ->
     _self
   {-# INLINE rule2039 #-}
   rule2039 = \ ((_literalIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _literalIcollectScopeInfos
   {-# INLINE rule2040 #-}
   rule2040 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2041 #-}
   rule2041 = \ ((_literalImiscerrors) :: [Error]) ->
     _literalImiscerrors
   {-# INLINE rule2042 #-}
   rule2042 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2043 #-}
   rule2043 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2044 #-}
   rule2044 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
{-# NOINLINE sem_Pattern_Variable #-}
sem_Pattern_Variable :: T_Range  -> T_Name  -> T_Pattern 
sem_Pattern_Variable arg_range_ arg_name_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2045 _nameIself
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2046  ()
         _self = rule2047 _nameIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2048 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2049 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2050 _lhsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2051 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2052 _lhsIwarnings
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2045 #-}
   rule2045 = \ ((_nameIself) :: Name) ->
                                     [ _nameIself ]
   {-# INLINE rule2046 #-}
   rule2046 = \  (_ :: ()) ->
     []
   {-# INLINE rule2047 #-}
   rule2047 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Pattern_Variable _rangeIself _nameIself
   {-# INLINE rule2048 #-}
   rule2048 = \ _self ->
     _self
   {-# INLINE rule2049 #-}
   rule2049 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2050 #-}
   rule2050 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2051 #-}
   rule2051 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2052 #-}
   rule2052 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Pattern_Constructor #-}
sem_Pattern_Constructor :: T_Range  -> T_Name  -> T_Patterns  -> T_Pattern 
sem_Pattern_Constructor arg_range_ arg_name_ arg_patterns_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Patterns_vOut121 _patternsIcollectScopeInfos _patternsIcounter _patternsImiscerrors _patternsInumberOfPatterns _patternsIpatVarNames _patternsIself _patternsIunboundNames _patternsIwarnings) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOcounter _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings)
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2053 _patConstructorErrors _patternsImiscerrors
         _patConstructorErrors = rule2054 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIlhsPattern _maybetp _nameIself _patternsInumberOfPatterns
         _maybetp = rule2055 _lhsIvalueConstructors _nameIself
         _patternsOlhsPattern = rule2056  ()
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2057 _patternsIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2058 _patternsIunboundNames
         _self = rule2059 _nameIself _patternsIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2060 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2061 _patternsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2062 _patternsIcounter
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2063 _patternsIwarnings
         _patternsOallTypeConstructors = rule2064 _lhsIallTypeConstructors
         _patternsOallValueConstructors = rule2065 _lhsIallValueConstructors
         _patternsOcollectScopeInfos = rule2066 _lhsIcollectScopeInfos
         _patternsOcounter = rule2067 _lhsIcounter
         _patternsOmiscerrors = rule2068 _lhsImiscerrors
         _patternsOnamesInScope = rule2069 _lhsInamesInScope
         _patternsOtypeConstructors = rule2070 _lhsItypeConstructors
         _patternsOvalueConstructors = rule2071 _lhsIvalueConstructors
         _patternsOwarnings = rule2072 _lhsIwarnings
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2053 #-}
   rule2053 = \ _patConstructorErrors ((_patternsImiscerrors) :: [Error]) ->
                                              _patConstructorErrors ++ _patternsImiscerrors
   {-# INLINE rule2054 #-}
   rule2054 = \ ((_lhsIallTypeConstructors) :: Names) ((_lhsIallValueConstructors) :: Names) ((_lhsIlhsPattern) :: Bool) _maybetp ((_nameIself) :: Name) ((_patternsInumberOfPatterns) :: Int) ->
                                                        patternConstructorErrors _maybetp _nameIself _lhsIallValueConstructors _patternsInumberOfPatterns _lhsIlhsPattern _lhsIallTypeConstructors
   {-# INLINE rule2055 #-}
   rule2055 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ((_nameIself) :: Name) ->
                                              M.lookup _nameIself _lhsIvalueConstructors
   {-# INLINE rule2056 #-}
   rule2056 = \  (_ :: ()) ->
                                                                False
   {-# INLINE rule2057 #-}
   rule2057 = \ ((_patternsIpatVarNames) :: Names) ->
     _patternsIpatVarNames
   {-# INLINE rule2058 #-}
   rule2058 = \ ((_patternsIunboundNames) :: Names) ->
     _patternsIunboundNames
   {-# INLINE rule2059 #-}
   rule2059 = \ ((_nameIself) :: Name) ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     Pattern_Constructor _rangeIself _nameIself _patternsIself
   {-# INLINE rule2060 #-}
   rule2060 = \ _self ->
     _self
   {-# INLINE rule2061 #-}
   rule2061 = \ ((_patternsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternsIcollectScopeInfos
   {-# INLINE rule2062 #-}
   rule2062 = \ ((_patternsIcounter) :: Int) ->
     _patternsIcounter
   {-# INLINE rule2063 #-}
   rule2063 = \ ((_patternsIwarnings) :: [Warning]) ->
     _patternsIwarnings
   {-# INLINE rule2064 #-}
   rule2064 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2065 #-}
   rule2065 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2066 #-}
   rule2066 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2067 #-}
   rule2067 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2068 #-}
   rule2068 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2069 #-}
   rule2069 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2070 #-}
   rule2070 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2071 #-}
   rule2071 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2072 #-}
   rule2072 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Pattern_Parenthesized #-}
sem_Pattern_Parenthesized :: T_Range  -> T_Pattern  -> T_Pattern 
sem_Pattern_Parenthesized arg_range_ arg_pattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIcollectScopeInfos _patternIcounter _patternImiscerrors _patternIpatVarNames _patternIself _patternIunboundNames _patternIwarnings) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOcounter _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings)
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2073 _patternIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2074 _patternIunboundNames
         _self = rule2075 _patternIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2076 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2077 _patternIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2078 _patternIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2079 _patternImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2080 _patternIwarnings
         _patternOallTypeConstructors = rule2081 _lhsIallTypeConstructors
         _patternOallValueConstructors = rule2082 _lhsIallValueConstructors
         _patternOcollectScopeInfos = rule2083 _lhsIcollectScopeInfos
         _patternOcounter = rule2084 _lhsIcounter
         _patternOlhsPattern = rule2085 _lhsIlhsPattern
         _patternOmiscerrors = rule2086 _lhsImiscerrors
         _patternOnamesInScope = rule2087 _lhsInamesInScope
         _patternOtypeConstructors = rule2088 _lhsItypeConstructors
         _patternOvalueConstructors = rule2089 _lhsIvalueConstructors
         _patternOwarnings = rule2090 _lhsIwarnings
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2073 #-}
   rule2073 = \ ((_patternIpatVarNames) :: Names) ->
     _patternIpatVarNames
   {-# INLINE rule2074 #-}
   rule2074 = \ ((_patternIunboundNames) :: Names) ->
     _patternIunboundNames
   {-# INLINE rule2075 #-}
   rule2075 = \ ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     Pattern_Parenthesized _rangeIself _patternIself
   {-# INLINE rule2076 #-}
   rule2076 = \ _self ->
     _self
   {-# INLINE rule2077 #-}
   rule2077 = \ ((_patternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternIcollectScopeInfos
   {-# INLINE rule2078 #-}
   rule2078 = \ ((_patternIcounter) :: Int) ->
     _patternIcounter
   {-# INLINE rule2079 #-}
   rule2079 = \ ((_patternImiscerrors) :: [Error]) ->
     _patternImiscerrors
   {-# INLINE rule2080 #-}
   rule2080 = \ ((_patternIwarnings) :: [Warning]) ->
     _patternIwarnings
   {-# INLINE rule2081 #-}
   rule2081 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2082 #-}
   rule2082 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2083 #-}
   rule2083 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2084 #-}
   rule2084 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2085 #-}
   rule2085 = \ ((_lhsIlhsPattern) :: Bool) ->
     _lhsIlhsPattern
   {-# INLINE rule2086 #-}
   rule2086 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2087 #-}
   rule2087 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2088 #-}
   rule2088 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2089 #-}
   rule2089 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2090 #-}
   rule2090 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Pattern_InfixConstructor #-}
sem_Pattern_InfixConstructor :: T_Range  -> T_Pattern  -> T_Name  -> T_Pattern  -> T_Pattern 
sem_Pattern_InfixConstructor arg_range_ arg_leftPattern_ arg_constructorOperator_ arg_rightPattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_leftPattern_))
         _constructorOperatorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructorOperator_))
         _rightPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_rightPattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _leftPatternIcollectScopeInfos _leftPatternIcounter _leftPatternImiscerrors _leftPatternIpatVarNames _leftPatternIself _leftPatternIunboundNames _leftPatternIwarnings) = inv_Pattern_s119 _leftPatternX119 (T_Pattern_vIn118 _leftPatternOallTypeConstructors _leftPatternOallValueConstructors _leftPatternOcollectScopeInfos _leftPatternOcounter _leftPatternOlhsPattern _leftPatternOmiscerrors _leftPatternOnamesInScope _leftPatternOtypeConstructors _leftPatternOvalueConstructors _leftPatternOwarnings)
         (T_Name_vOut112 _constructorOperatorIself) = inv_Name_s113 _constructorOperatorX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _rightPatternIcollectScopeInfos _rightPatternIcounter _rightPatternImiscerrors _rightPatternIpatVarNames _rightPatternIself _rightPatternIunboundNames _rightPatternIwarnings) = inv_Pattern_s119 _rightPatternX119 (T_Pattern_vIn118 _rightPatternOallTypeConstructors _rightPatternOallValueConstructors _rightPatternOcollectScopeInfos _rightPatternOcounter _rightPatternOlhsPattern _rightPatternOmiscerrors _rightPatternOnamesInScope _rightPatternOtypeConstructors _rightPatternOvalueConstructors _rightPatternOwarnings)
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2091 _patConstructorErrors _rightPatternImiscerrors
         _patConstructorErrors = rule2092 _constructorOperatorIself _lhsIallTypeConstructors _lhsIallValueConstructors _maybetp
         _maybetp = rule2093 _constructorOperatorIself _lhsIvalueConstructors
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2094 _leftPatternIpatVarNames _rightPatternIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2095 _leftPatternIunboundNames _rightPatternIunboundNames
         _self = rule2096 _constructorOperatorIself _leftPatternIself _rangeIself _rightPatternIself
         _lhsOself :: Pattern
         _lhsOself = rule2097 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2098 _rightPatternIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2099 _rightPatternIcounter
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2100 _rightPatternIwarnings
         _leftPatternOallTypeConstructors = rule2101 _lhsIallTypeConstructors
         _leftPatternOallValueConstructors = rule2102 _lhsIallValueConstructors
         _leftPatternOcollectScopeInfos = rule2103 _lhsIcollectScopeInfos
         _leftPatternOcounter = rule2104 _lhsIcounter
         _leftPatternOlhsPattern = rule2105 _lhsIlhsPattern
         _leftPatternOmiscerrors = rule2106 _lhsImiscerrors
         _leftPatternOnamesInScope = rule2107 _lhsInamesInScope
         _leftPatternOtypeConstructors = rule2108 _lhsItypeConstructors
         _leftPatternOvalueConstructors = rule2109 _lhsIvalueConstructors
         _leftPatternOwarnings = rule2110 _lhsIwarnings
         _rightPatternOallTypeConstructors = rule2111 _lhsIallTypeConstructors
         _rightPatternOallValueConstructors = rule2112 _lhsIallValueConstructors
         _rightPatternOcollectScopeInfos = rule2113 _leftPatternIcollectScopeInfos
         _rightPatternOcounter = rule2114 _leftPatternIcounter
         _rightPatternOlhsPattern = rule2115 _lhsIlhsPattern
         _rightPatternOmiscerrors = rule2116 _leftPatternImiscerrors
         _rightPatternOnamesInScope = rule2117 _lhsInamesInScope
         _rightPatternOtypeConstructors = rule2118 _lhsItypeConstructors
         _rightPatternOvalueConstructors = rule2119 _lhsIvalueConstructors
         _rightPatternOwarnings = rule2120 _leftPatternIwarnings
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2091 #-}
   rule2091 = \ _patConstructorErrors ((_rightPatternImiscerrors) :: [Error]) ->
                                              _patConstructorErrors ++ _rightPatternImiscerrors
   {-# INLINE rule2092 #-}
   rule2092 = \ ((_constructorOperatorIself) :: Name) ((_lhsIallTypeConstructors) :: Names) ((_lhsIallValueConstructors) :: Names) _maybetp ->
                                                        patternConstructorErrors _maybetp _constructorOperatorIself _lhsIallValueConstructors 2 False _lhsIallTypeConstructors
   {-# INLINE rule2093 #-}
   rule2093 = \ ((_constructorOperatorIself) :: Name) ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
                                              M.lookup _constructorOperatorIself _lhsIvalueConstructors
   {-# INLINE rule2094 #-}
   rule2094 = \ ((_leftPatternIpatVarNames) :: Names) ((_rightPatternIpatVarNames) :: Names) ->
     _leftPatternIpatVarNames ++ _rightPatternIpatVarNames
   {-# INLINE rule2095 #-}
   rule2095 = \ ((_leftPatternIunboundNames) :: Names) ((_rightPatternIunboundNames) :: Names) ->
     _leftPatternIunboundNames ++ _rightPatternIunboundNames
   {-# INLINE rule2096 #-}
   rule2096 = \ ((_constructorOperatorIself) :: Name) ((_leftPatternIself) :: Pattern) ((_rangeIself) :: Range) ((_rightPatternIself) :: Pattern) ->
     Pattern_InfixConstructor _rangeIself _leftPatternIself _constructorOperatorIself _rightPatternIself
   {-# INLINE rule2097 #-}
   rule2097 = \ _self ->
     _self
   {-# INLINE rule2098 #-}
   rule2098 = \ ((_rightPatternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _rightPatternIcollectScopeInfos
   {-# INLINE rule2099 #-}
   rule2099 = \ ((_rightPatternIcounter) :: Int) ->
     _rightPatternIcounter
   {-# INLINE rule2100 #-}
   rule2100 = \ ((_rightPatternIwarnings) :: [Warning]) ->
     _rightPatternIwarnings
   {-# INLINE rule2101 #-}
   rule2101 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2102 #-}
   rule2102 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2103 #-}
   rule2103 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2104 #-}
   rule2104 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2105 #-}
   rule2105 = \ ((_lhsIlhsPattern) :: Bool) ->
     _lhsIlhsPattern
   {-# INLINE rule2106 #-}
   rule2106 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2107 #-}
   rule2107 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2108 #-}
   rule2108 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2109 #-}
   rule2109 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2110 #-}
   rule2110 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2111 #-}
   rule2111 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2112 #-}
   rule2112 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2113 #-}
   rule2113 = \ ((_leftPatternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _leftPatternIcollectScopeInfos
   {-# INLINE rule2114 #-}
   rule2114 = \ ((_leftPatternIcounter) :: Int) ->
     _leftPatternIcounter
   {-# INLINE rule2115 #-}
   rule2115 = \ ((_lhsIlhsPattern) :: Bool) ->
     _lhsIlhsPattern
   {-# INLINE rule2116 #-}
   rule2116 = \ ((_leftPatternImiscerrors) :: [Error]) ->
     _leftPatternImiscerrors
   {-# INLINE rule2117 #-}
   rule2117 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2118 #-}
   rule2118 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2119 #-}
   rule2119 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2120 #-}
   rule2120 = \ ((_leftPatternIwarnings) :: [Warning]) ->
     _leftPatternIwarnings
{-# NOINLINE sem_Pattern_List #-}
sem_Pattern_List :: T_Range  -> T_Patterns  -> T_Pattern 
sem_Pattern_List arg_range_ arg_patterns_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Patterns_vOut121 _patternsIcollectScopeInfos _patternsIcounter _patternsImiscerrors _patternsInumberOfPatterns _patternsIpatVarNames _patternsIself _patternsIunboundNames _patternsIwarnings) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOcounter _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings)
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2121 _patternsIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2122 _patternsIunboundNames
         _self = rule2123 _patternsIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2124 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2125 _patternsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2126 _patternsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2127 _patternsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2128 _patternsIwarnings
         _patternsOallTypeConstructors = rule2129 _lhsIallTypeConstructors
         _patternsOallValueConstructors = rule2130 _lhsIallValueConstructors
         _patternsOcollectScopeInfos = rule2131 _lhsIcollectScopeInfos
         _patternsOcounter = rule2132 _lhsIcounter
         _patternsOlhsPattern = rule2133 _lhsIlhsPattern
         _patternsOmiscerrors = rule2134 _lhsImiscerrors
         _patternsOnamesInScope = rule2135 _lhsInamesInScope
         _patternsOtypeConstructors = rule2136 _lhsItypeConstructors
         _patternsOvalueConstructors = rule2137 _lhsIvalueConstructors
         _patternsOwarnings = rule2138 _lhsIwarnings
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2121 #-}
   rule2121 = \ ((_patternsIpatVarNames) :: Names) ->
     _patternsIpatVarNames
   {-# INLINE rule2122 #-}
   rule2122 = \ ((_patternsIunboundNames) :: Names) ->
     _patternsIunboundNames
   {-# INLINE rule2123 #-}
   rule2123 = \ ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     Pattern_List _rangeIself _patternsIself
   {-# INLINE rule2124 #-}
   rule2124 = \ _self ->
     _self
   {-# INLINE rule2125 #-}
   rule2125 = \ ((_patternsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternsIcollectScopeInfos
   {-# INLINE rule2126 #-}
   rule2126 = \ ((_patternsIcounter) :: Int) ->
     _patternsIcounter
   {-# INLINE rule2127 #-}
   rule2127 = \ ((_patternsImiscerrors) :: [Error]) ->
     _patternsImiscerrors
   {-# INLINE rule2128 #-}
   rule2128 = \ ((_patternsIwarnings) :: [Warning]) ->
     _patternsIwarnings
   {-# INLINE rule2129 #-}
   rule2129 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2130 #-}
   rule2130 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2131 #-}
   rule2131 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2132 #-}
   rule2132 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2133 #-}
   rule2133 = \ ((_lhsIlhsPattern) :: Bool) ->
     _lhsIlhsPattern
   {-# INLINE rule2134 #-}
   rule2134 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2135 #-}
   rule2135 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2136 #-}
   rule2136 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2137 #-}
   rule2137 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2138 #-}
   rule2138 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Pattern_Tuple #-}
sem_Pattern_Tuple :: T_Range  -> T_Patterns  -> T_Pattern 
sem_Pattern_Tuple arg_range_ arg_patterns_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Patterns_vOut121 _patternsIcollectScopeInfos _patternsIcounter _patternsImiscerrors _patternsInumberOfPatterns _patternsIpatVarNames _patternsIself _patternsIunboundNames _patternsIwarnings) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 _patternsOallTypeConstructors _patternsOallValueConstructors _patternsOcollectScopeInfos _patternsOcounter _patternsOlhsPattern _patternsOmiscerrors _patternsOnamesInScope _patternsOtypeConstructors _patternsOvalueConstructors _patternsOwarnings)
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2139 _patternsIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2140 _patternsIunboundNames
         _self = rule2141 _patternsIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2142 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2143 _patternsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2144 _patternsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2145 _patternsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2146 _patternsIwarnings
         _patternsOallTypeConstructors = rule2147 _lhsIallTypeConstructors
         _patternsOallValueConstructors = rule2148 _lhsIallValueConstructors
         _patternsOcollectScopeInfos = rule2149 _lhsIcollectScopeInfos
         _patternsOcounter = rule2150 _lhsIcounter
         _patternsOlhsPattern = rule2151 _lhsIlhsPattern
         _patternsOmiscerrors = rule2152 _lhsImiscerrors
         _patternsOnamesInScope = rule2153 _lhsInamesInScope
         _patternsOtypeConstructors = rule2154 _lhsItypeConstructors
         _patternsOvalueConstructors = rule2155 _lhsIvalueConstructors
         _patternsOwarnings = rule2156 _lhsIwarnings
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2139 #-}
   rule2139 = \ ((_patternsIpatVarNames) :: Names) ->
     _patternsIpatVarNames
   {-# INLINE rule2140 #-}
   rule2140 = \ ((_patternsIunboundNames) :: Names) ->
     _patternsIunboundNames
   {-# INLINE rule2141 #-}
   rule2141 = \ ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     Pattern_Tuple _rangeIself _patternsIself
   {-# INLINE rule2142 #-}
   rule2142 = \ _self ->
     _self
   {-# INLINE rule2143 #-}
   rule2143 = \ ((_patternsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternsIcollectScopeInfos
   {-# INLINE rule2144 #-}
   rule2144 = \ ((_patternsIcounter) :: Int) ->
     _patternsIcounter
   {-# INLINE rule2145 #-}
   rule2145 = \ ((_patternsImiscerrors) :: [Error]) ->
     _patternsImiscerrors
   {-# INLINE rule2146 #-}
   rule2146 = \ ((_patternsIwarnings) :: [Warning]) ->
     _patternsIwarnings
   {-# INLINE rule2147 #-}
   rule2147 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2148 #-}
   rule2148 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2149 #-}
   rule2149 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2150 #-}
   rule2150 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2151 #-}
   rule2151 = \ ((_lhsIlhsPattern) :: Bool) ->
     _lhsIlhsPattern
   {-# INLINE rule2152 #-}
   rule2152 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2153 #-}
   rule2153 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2154 #-}
   rule2154 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2155 #-}
   rule2155 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2156 #-}
   rule2156 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Pattern_Record #-}
sem_Pattern_Record :: T_Range  -> T_Name  -> T_RecordPatternBindings  -> T_Pattern 
sem_Pattern_Record arg_range_ arg_name_ arg_recordPatternBindings_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _recordPatternBindingsX146 = Control.Monad.Identity.runIdentity (attach_T_RecordPatternBindings (arg_recordPatternBindings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_RecordPatternBindings_vOut145 _recordPatternBindingsIcollectScopeInfos _recordPatternBindingsIcounter _recordPatternBindingsIself _recordPatternBindingsIunboundNames) = inv_RecordPatternBindings_s146 _recordPatternBindingsX146 (T_RecordPatternBindings_vIn145 _recordPatternBindingsOcollectScopeInfos _recordPatternBindingsOcounter _recordPatternBindingsOnamesInScope)
         (_beta,_constraints,_environment) = rule2157  ()
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2158  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2159 _recordPatternBindingsIunboundNames
         _self = rule2160 _nameIself _rangeIself _recordPatternBindingsIself
         _lhsOself :: Pattern
         _lhsOself = rule2161 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2162 _recordPatternBindingsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2163 _recordPatternBindingsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2164 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2165 _lhsIwarnings
         _recordPatternBindingsOcollectScopeInfos = rule2166 _lhsIcollectScopeInfos
         _recordPatternBindingsOcounter = rule2167 _lhsIcounter
         _recordPatternBindingsOnamesInScope = rule2168 _lhsInamesInScope
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2157 #-}
   rule2157 = \  (_ :: ()) ->
                                                       internalError "PartialSyntax.ag" "n/a" "Pattern.Record"
   {-# INLINE rule2158 #-}
   rule2158 = \  (_ :: ()) ->
     []
   {-# INLINE rule2159 #-}
   rule2159 = \ ((_recordPatternBindingsIunboundNames) :: Names) ->
     _recordPatternBindingsIunboundNames
   {-# INLINE rule2160 #-}
   rule2160 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ((_recordPatternBindingsIself) :: RecordPatternBindings) ->
     Pattern_Record _rangeIself _nameIself _recordPatternBindingsIself
   {-# INLINE rule2161 #-}
   rule2161 = \ _self ->
     _self
   {-# INLINE rule2162 #-}
   rule2162 = \ ((_recordPatternBindingsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _recordPatternBindingsIcollectScopeInfos
   {-# INLINE rule2163 #-}
   rule2163 = \ ((_recordPatternBindingsIcounter) :: Int) ->
     _recordPatternBindingsIcounter
   {-# INLINE rule2164 #-}
   rule2164 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2165 #-}
   rule2165 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2166 #-}
   rule2166 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2167 #-}
   rule2167 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2168 #-}
   rule2168 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
{-# NOINLINE sem_Pattern_Negate #-}
sem_Pattern_Negate :: T_Range  -> T_Literal  -> T_Pattern 
sem_Pattern_Negate arg_range_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalIcollectScopeInfos _literalImiscerrors _literalIself) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 _literalOcollectScopeInfos _literalOmiscerrors)
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2169  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2170  ()
         _self = rule2171 _literalIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2172 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2173 _literalIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2174 _lhsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2175 _literalImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2176 _lhsIwarnings
         _literalOcollectScopeInfos = rule2177 _lhsIcollectScopeInfos
         _literalOmiscerrors = rule2178 _lhsImiscerrors
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2169 #-}
   rule2169 = \  (_ :: ()) ->
     []
   {-# INLINE rule2170 #-}
   rule2170 = \  (_ :: ()) ->
     []
   {-# INLINE rule2171 #-}
   rule2171 = \ ((_literalIself) :: Literal) ((_rangeIself) :: Range) ->
     Pattern_Negate _rangeIself _literalIself
   {-# INLINE rule2172 #-}
   rule2172 = \ _self ->
     _self
   {-# INLINE rule2173 #-}
   rule2173 = \ ((_literalIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _literalIcollectScopeInfos
   {-# INLINE rule2174 #-}
   rule2174 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2175 #-}
   rule2175 = \ ((_literalImiscerrors) :: [Error]) ->
     _literalImiscerrors
   {-# INLINE rule2176 #-}
   rule2176 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2177 #-}
   rule2177 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2178 #-}
   rule2178 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
{-# NOINLINE sem_Pattern_As #-}
sem_Pattern_As :: T_Range  -> T_Name  -> T_Pattern  -> T_Pattern 
sem_Pattern_As arg_range_ arg_name_ arg_pattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _patternIcollectScopeInfos _patternIcounter _patternImiscerrors _patternIpatVarNames _patternIself _patternIunboundNames _patternIwarnings) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOcounter _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings)
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2179 _nameIself _patternIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2180 _patternIunboundNames
         _self = rule2181 _nameIself _patternIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2182 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2183 _patternIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2184 _patternIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2185 _patternImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2186 _patternIwarnings
         _patternOallTypeConstructors = rule2187 _lhsIallTypeConstructors
         _patternOallValueConstructors = rule2188 _lhsIallValueConstructors
         _patternOcollectScopeInfos = rule2189 _lhsIcollectScopeInfos
         _patternOcounter = rule2190 _lhsIcounter
         _patternOlhsPattern = rule2191 _lhsIlhsPattern
         _patternOmiscerrors = rule2192 _lhsImiscerrors
         _patternOnamesInScope = rule2193 _lhsInamesInScope
         _patternOtypeConstructors = rule2194 _lhsItypeConstructors
         _patternOvalueConstructors = rule2195 _lhsIvalueConstructors
         _patternOwarnings = rule2196 _lhsIwarnings
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2179 #-}
   rule2179 = \ ((_nameIself) :: Name) ((_patternIpatVarNames) :: Names) ->
                                     _nameIself : _patternIpatVarNames
   {-# INLINE rule2180 #-}
   rule2180 = \ ((_patternIunboundNames) :: Names) ->
     _patternIunboundNames
   {-# INLINE rule2181 #-}
   rule2181 = \ ((_nameIself) :: Name) ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     Pattern_As _rangeIself _nameIself _patternIself
   {-# INLINE rule2182 #-}
   rule2182 = \ _self ->
     _self
   {-# INLINE rule2183 #-}
   rule2183 = \ ((_patternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternIcollectScopeInfos
   {-# INLINE rule2184 #-}
   rule2184 = \ ((_patternIcounter) :: Int) ->
     _patternIcounter
   {-# INLINE rule2185 #-}
   rule2185 = \ ((_patternImiscerrors) :: [Error]) ->
     _patternImiscerrors
   {-# INLINE rule2186 #-}
   rule2186 = \ ((_patternIwarnings) :: [Warning]) ->
     _patternIwarnings
   {-# INLINE rule2187 #-}
   rule2187 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2188 #-}
   rule2188 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2189 #-}
   rule2189 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2190 #-}
   rule2190 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2191 #-}
   rule2191 = \ ((_lhsIlhsPattern) :: Bool) ->
     _lhsIlhsPattern
   {-# INLINE rule2192 #-}
   rule2192 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2193 #-}
   rule2193 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2194 #-}
   rule2194 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2195 #-}
   rule2195 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2196 #-}
   rule2196 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Pattern_Wildcard #-}
sem_Pattern_Wildcard :: T_Range  -> T_Pattern 
sem_Pattern_Wildcard arg_range_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2197  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2198  ()
         _self = rule2199 _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2200 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2201 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2202 _lhsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2203 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2204 _lhsIwarnings
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2197 #-}
   rule2197 = \  (_ :: ()) ->
     []
   {-# INLINE rule2198 #-}
   rule2198 = \  (_ :: ()) ->
     []
   {-# INLINE rule2199 #-}
   rule2199 = \ ((_rangeIself) :: Range) ->
     Pattern_Wildcard _rangeIself
   {-# INLINE rule2200 #-}
   rule2200 = \ _self ->
     _self
   {-# INLINE rule2201 #-}
   rule2201 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2202 #-}
   rule2202 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2203 #-}
   rule2203 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2204 #-}
   rule2204 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Pattern_Irrefutable #-}
sem_Pattern_Irrefutable :: T_Range  -> T_Pattern  -> T_Pattern 
sem_Pattern_Irrefutable arg_range_ arg_pattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIcollectScopeInfos _patternIcounter _patternImiscerrors _patternIpatVarNames _patternIself _patternIunboundNames _patternIwarnings) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOcounter _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings)
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2205 _patternIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2206 _patternIunboundNames
         _self = rule2207 _patternIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2208 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2209 _patternIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2210 _patternIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2211 _patternImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2212 _patternIwarnings
         _patternOallTypeConstructors = rule2213 _lhsIallTypeConstructors
         _patternOallValueConstructors = rule2214 _lhsIallValueConstructors
         _patternOcollectScopeInfos = rule2215 _lhsIcollectScopeInfos
         _patternOcounter = rule2216 _lhsIcounter
         _patternOlhsPattern = rule2217 _lhsIlhsPattern
         _patternOmiscerrors = rule2218 _lhsImiscerrors
         _patternOnamesInScope = rule2219 _lhsInamesInScope
         _patternOtypeConstructors = rule2220 _lhsItypeConstructors
         _patternOvalueConstructors = rule2221 _lhsIvalueConstructors
         _patternOwarnings = rule2222 _lhsIwarnings
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2205 #-}
   rule2205 = \ ((_patternIpatVarNames) :: Names) ->
     _patternIpatVarNames
   {-# INLINE rule2206 #-}
   rule2206 = \ ((_patternIunboundNames) :: Names) ->
     _patternIunboundNames
   {-# INLINE rule2207 #-}
   rule2207 = \ ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     Pattern_Irrefutable _rangeIself _patternIself
   {-# INLINE rule2208 #-}
   rule2208 = \ _self ->
     _self
   {-# INLINE rule2209 #-}
   rule2209 = \ ((_patternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternIcollectScopeInfos
   {-# INLINE rule2210 #-}
   rule2210 = \ ((_patternIcounter) :: Int) ->
     _patternIcounter
   {-# INLINE rule2211 #-}
   rule2211 = \ ((_patternImiscerrors) :: [Error]) ->
     _patternImiscerrors
   {-# INLINE rule2212 #-}
   rule2212 = \ ((_patternIwarnings) :: [Warning]) ->
     _patternIwarnings
   {-# INLINE rule2213 #-}
   rule2213 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2214 #-}
   rule2214 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2215 #-}
   rule2215 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2216 #-}
   rule2216 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2217 #-}
   rule2217 = \ ((_lhsIlhsPattern) :: Bool) ->
     _lhsIlhsPattern
   {-# INLINE rule2218 #-}
   rule2218 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2219 #-}
   rule2219 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2220 #-}
   rule2220 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2221 #-}
   rule2221 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2222 #-}
   rule2222 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Pattern_Successor #-}
sem_Pattern_Successor :: T_Range  -> T_Name  -> T_Literal  -> T_Pattern 
sem_Pattern_Successor arg_range_ arg_name_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Literal_vOut85 _literalIcollectScopeInfos _literalImiscerrors _literalIself) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 _literalOcollectScopeInfos _literalOmiscerrors)
         (_beta,_constraints,_environment) = rule2223  ()
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2224  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2225  ()
         _self = rule2226 _literalIself _nameIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2227 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2228 _literalIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2229 _lhsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2230 _literalImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2231 _lhsIwarnings
         _literalOcollectScopeInfos = rule2232 _lhsIcollectScopeInfos
         _literalOmiscerrors = rule2233 _lhsImiscerrors
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2223 #-}
   rule2223 = \  (_ :: ()) ->
                                                       internalError "PartialSyntax.ag" "n/a" "Pattern.Successor"
   {-# INLINE rule2224 #-}
   rule2224 = \  (_ :: ()) ->
     []
   {-# INLINE rule2225 #-}
   rule2225 = \  (_ :: ()) ->
     []
   {-# INLINE rule2226 #-}
   rule2226 = \ ((_literalIself) :: Literal) ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Pattern_Successor _rangeIself _nameIself _literalIself
   {-# INLINE rule2227 #-}
   rule2227 = \ _self ->
     _self
   {-# INLINE rule2228 #-}
   rule2228 = \ ((_literalIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _literalIcollectScopeInfos
   {-# INLINE rule2229 #-}
   rule2229 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2230 #-}
   rule2230 = \ ((_literalImiscerrors) :: [Error]) ->
     _literalImiscerrors
   {-# INLINE rule2231 #-}
   rule2231 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2232 #-}
   rule2232 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2233 #-}
   rule2233 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
{-# NOINLINE sem_Pattern_NegateFloat #-}
sem_Pattern_NegateFloat :: T_Range  -> T_Literal  -> T_Pattern 
sem_Pattern_NegateFloat arg_range_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalIcollectScopeInfos _literalImiscerrors _literalIself) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 _literalOcollectScopeInfos _literalOmiscerrors)
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2234  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2235  ()
         _self = rule2236 _literalIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule2237 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2238 _literalIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2239 _lhsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2240 _literalImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2241 _lhsIwarnings
         _literalOcollectScopeInfos = rule2242 _lhsIcollectScopeInfos
         _literalOmiscerrors = rule2243 _lhsImiscerrors
         __result_ = T_Pattern_vOut118 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule2234 #-}
   rule2234 = \  (_ :: ()) ->
     []
   {-# INLINE rule2235 #-}
   rule2235 = \  (_ :: ()) ->
     []
   {-# INLINE rule2236 #-}
   rule2236 = \ ((_literalIself) :: Literal) ((_rangeIself) :: Range) ->
     Pattern_NegateFloat _rangeIself _literalIself
   {-# INLINE rule2237 #-}
   rule2237 = \ _self ->
     _self
   {-# INLINE rule2238 #-}
   rule2238 = \ ((_literalIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _literalIcollectScopeInfos
   {-# INLINE rule2239 #-}
   rule2239 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2240 #-}
   rule2240 = \ ((_literalImiscerrors) :: [Error]) ->
     _literalImiscerrors
   {-# INLINE rule2241 #-}
   rule2241 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2242 #-}
   rule2242 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2243 #-}
   rule2243 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors

-- Patterns ----------------------------------------------------
-- wrapper
data Inh_Patterns  = Inh_Patterns { allTypeConstructors_Inh_Patterns :: (Names), allValueConstructors_Inh_Patterns :: (Names), collectScopeInfos_Inh_Patterns :: ([(ScopeInfo, Entity)]), counter_Inh_Patterns :: (Int), lhsPattern_Inh_Patterns :: (Bool), miscerrors_Inh_Patterns :: ([Error]), namesInScope_Inh_Patterns :: (Names), typeConstructors_Inh_Patterns :: (M.Map Name Int), valueConstructors_Inh_Patterns :: (M.Map Name TpScheme), warnings_Inh_Patterns :: ([Warning]) }
data Syn_Patterns  = Syn_Patterns { collectScopeInfos_Syn_Patterns :: ([(ScopeInfo, Entity)]), counter_Syn_Patterns :: (Int), miscerrors_Syn_Patterns :: ([Error]), numberOfPatterns_Syn_Patterns :: (Int), patVarNames_Syn_Patterns :: (Names), self_Syn_Patterns :: (Patterns), unboundNames_Syn_Patterns :: (Names), warnings_Syn_Patterns :: ([Warning]) }
{-# INLINABLE wrap_Patterns #-}
wrap_Patterns :: T_Patterns  -> Inh_Patterns  -> (Syn_Patterns )
wrap_Patterns (T_Patterns act) (Inh_Patterns _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Patterns_vIn121 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_Patterns_vOut121 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOnumberOfPatterns _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_Patterns_s122 sem arg)
        return (Syn_Patterns _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOnumberOfPatterns _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Patterns #-}
sem_Patterns :: Patterns  -> T_Patterns 
sem_Patterns list = Prelude.foldr sem_Patterns_Cons sem_Patterns_Nil (Prelude.map sem_Pattern list)

-- semantic domain
newtype T_Patterns  = T_Patterns {
                                 attach_T_Patterns :: Identity (T_Patterns_s122 )
                                 }
newtype T_Patterns_s122  = C_Patterns_s122 {
                                           inv_Patterns_s122 :: (T_Patterns_v121 )
                                           }
data T_Patterns_s123  = C_Patterns_s123
type T_Patterns_v121  = (T_Patterns_vIn121 ) -> (T_Patterns_vOut121 )
data T_Patterns_vIn121  = T_Patterns_vIn121 (Names) (Names) ([(ScopeInfo, Entity)]) (Int) (Bool) ([Error]) (Names) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_Patterns_vOut121  = T_Patterns_vOut121 ([(ScopeInfo, Entity)]) (Int) ([Error]) (Int) (Names) (Patterns) (Names) ([Warning])
{-# NOINLINE sem_Patterns_Cons #-}
sem_Patterns_Cons :: T_Pattern  -> T_Patterns  -> T_Patterns 
sem_Patterns_Cons arg_hd_ arg_tl_ = T_Patterns (return st122) where
   {-# NOINLINE st122 #-}
   st122 = let
      v121 :: T_Patterns_v121 
      v121 = \ (T_Patterns_vIn121 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _hdX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_hd_))
         _tlX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_tl_))
         (T_Pattern_vOut118 _hdIcollectScopeInfos _hdIcounter _hdImiscerrors _hdIpatVarNames _hdIself _hdIunboundNames _hdIwarnings) = inv_Pattern_s119 _hdX119 (T_Pattern_vIn118 _hdOallTypeConstructors _hdOallValueConstructors _hdOcollectScopeInfos _hdOcounter _hdOlhsPattern _hdOmiscerrors _hdOnamesInScope _hdOtypeConstructors _hdOvalueConstructors _hdOwarnings)
         (T_Patterns_vOut121 _tlIcollectScopeInfos _tlIcounter _tlImiscerrors _tlInumberOfPatterns _tlIpatVarNames _tlIself _tlIunboundNames _tlIwarnings) = inv_Patterns_s122 _tlX122 (T_Patterns_vIn121 _tlOallTypeConstructors _tlOallValueConstructors _tlOcollectScopeInfos _tlOcounter _tlOlhsPattern _tlOmiscerrors _tlOnamesInScope _tlOtypeConstructors _tlOvalueConstructors _tlOwarnings)
         _lhsOnumberOfPatterns :: Int
         _lhsOnumberOfPatterns = rule2244 _tlInumberOfPatterns
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2245 _hdIpatVarNames _tlIpatVarNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2246 _hdIunboundNames _tlIunboundNames
         _self = rule2247 _hdIself _tlIself
         _lhsOself :: Patterns
         _lhsOself = rule2248 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2249 _tlIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2250 _tlIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2251 _tlImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2252 _tlIwarnings
         _hdOallTypeConstructors = rule2253 _lhsIallTypeConstructors
         _hdOallValueConstructors = rule2254 _lhsIallValueConstructors
         _hdOcollectScopeInfos = rule2255 _lhsIcollectScopeInfos
         _hdOcounter = rule2256 _lhsIcounter
         _hdOlhsPattern = rule2257 _lhsIlhsPattern
         _hdOmiscerrors = rule2258 _lhsImiscerrors
         _hdOnamesInScope = rule2259 _lhsInamesInScope
         _hdOtypeConstructors = rule2260 _lhsItypeConstructors
         _hdOvalueConstructors = rule2261 _lhsIvalueConstructors
         _hdOwarnings = rule2262 _lhsIwarnings
         _tlOallTypeConstructors = rule2263 _lhsIallTypeConstructors
         _tlOallValueConstructors = rule2264 _lhsIallValueConstructors
         _tlOcollectScopeInfos = rule2265 _hdIcollectScopeInfos
         _tlOcounter = rule2266 _hdIcounter
         _tlOlhsPattern = rule2267 _lhsIlhsPattern
         _tlOmiscerrors = rule2268 _hdImiscerrors
         _tlOnamesInScope = rule2269 _lhsInamesInScope
         _tlOtypeConstructors = rule2270 _lhsItypeConstructors
         _tlOvalueConstructors = rule2271 _lhsIvalueConstructors
         _tlOwarnings = rule2272 _hdIwarnings
         __result_ = T_Patterns_vOut121 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOnumberOfPatterns _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Patterns_s122 v121
   {-# INLINE rule2244 #-}
   rule2244 = \ ((_tlInumberOfPatterns) :: Int) ->
                                     1 + _tlInumberOfPatterns
   {-# INLINE rule2245 #-}
   rule2245 = \ ((_hdIpatVarNames) :: Names) ((_tlIpatVarNames) :: Names) ->
     _hdIpatVarNames ++ _tlIpatVarNames
   {-# INLINE rule2246 #-}
   rule2246 = \ ((_hdIunboundNames) :: Names) ((_tlIunboundNames) :: Names) ->
     _hdIunboundNames ++ _tlIunboundNames
   {-# INLINE rule2247 #-}
   rule2247 = \ ((_hdIself) :: Pattern) ((_tlIself) :: Patterns) ->
     (:) _hdIself _tlIself
   {-# INLINE rule2248 #-}
   rule2248 = \ _self ->
     _self
   {-# INLINE rule2249 #-}
   rule2249 = \ ((_tlIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _tlIcollectScopeInfos
   {-# INLINE rule2250 #-}
   rule2250 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule2251 #-}
   rule2251 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule2252 #-}
   rule2252 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule2253 #-}
   rule2253 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2254 #-}
   rule2254 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2255 #-}
   rule2255 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2256 #-}
   rule2256 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2257 #-}
   rule2257 = \ ((_lhsIlhsPattern) :: Bool) ->
     _lhsIlhsPattern
   {-# INLINE rule2258 #-}
   rule2258 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2259 #-}
   rule2259 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2260 #-}
   rule2260 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2261 #-}
   rule2261 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2262 #-}
   rule2262 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2263 #-}
   rule2263 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2264 #-}
   rule2264 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2265 #-}
   rule2265 = \ ((_hdIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _hdIcollectScopeInfos
   {-# INLINE rule2266 #-}
   rule2266 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule2267 #-}
   rule2267 = \ ((_lhsIlhsPattern) :: Bool) ->
     _lhsIlhsPattern
   {-# INLINE rule2268 #-}
   rule2268 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule2269 #-}
   rule2269 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2270 #-}
   rule2270 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2271 #-}
   rule2271 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2272 #-}
   rule2272 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_Patterns_Nil #-}
sem_Patterns_Nil ::  T_Patterns 
sem_Patterns_Nil  = T_Patterns (return st122) where
   {-# NOINLINE st122 #-}
   st122 = let
      v121 :: T_Patterns_v121 
      v121 = \ (T_Patterns_vIn121 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIcollectScopeInfos _lhsIcounter _lhsIlhsPattern _lhsImiscerrors _lhsInamesInScope _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOnumberOfPatterns :: Int
         _lhsOnumberOfPatterns = rule2273  ()
         _lhsOpatVarNames :: Names
         _lhsOpatVarNames = rule2274  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2275  ()
         _self = rule2276  ()
         _lhsOself :: Patterns
         _lhsOself = rule2277 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2278 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2279 _lhsIcounter
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2280 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2281 _lhsIwarnings
         __result_ = T_Patterns_vOut121 _lhsOcollectScopeInfos _lhsOcounter _lhsOmiscerrors _lhsOnumberOfPatterns _lhsOpatVarNames _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Patterns_s122 v121
   {-# INLINE rule2273 #-}
   rule2273 = \  (_ :: ()) ->
                                     0
   {-# INLINE rule2274 #-}
   rule2274 = \  (_ :: ()) ->
     []
   {-# INLINE rule2275 #-}
   rule2275 = \  (_ :: ()) ->
     []
   {-# INLINE rule2276 #-}
   rule2276 = \  (_ :: ()) ->
     []
   {-# INLINE rule2277 #-}
   rule2277 = \ _self ->
     _self
   {-# INLINE rule2278 #-}
   rule2278 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2279 #-}
   rule2279 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2280 #-}
   rule2280 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2281 #-}
   rule2281 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Position ----------------------------------------------------
-- wrapper
data Inh_Position  = Inh_Position {  }
data Syn_Position  = Syn_Position { self_Syn_Position :: (Position) }
{-# INLINABLE wrap_Position #-}
wrap_Position :: T_Position  -> Inh_Position  -> (Syn_Position )
wrap_Position (T_Position act) (Inh_Position ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Position_vIn124 
        (T_Position_vOut124 _lhsOself) <- return (inv_Position_s125 sem arg)
        return (Syn_Position _lhsOself)
   )

-- cata
{-# NOINLINE sem_Position #-}
sem_Position :: Position  -> T_Position 
sem_Position ( Position_Position filename_ line_ column_ ) = sem_Position_Position filename_ line_ column_
sem_Position ( Position_Unknown  ) = sem_Position_Unknown 

-- semantic domain
newtype T_Position  = T_Position {
                                 attach_T_Position :: Identity (T_Position_s125 )
                                 }
newtype T_Position_s125  = C_Position_s125 {
                                           inv_Position_s125 :: (T_Position_v124 )
                                           }
data T_Position_s126  = C_Position_s126
type T_Position_v124  = (T_Position_vIn124 ) -> (T_Position_vOut124 )
data T_Position_vIn124  = T_Position_vIn124 
data T_Position_vOut124  = T_Position_vOut124 (Position)
{-# NOINLINE sem_Position_Position #-}
sem_Position_Position :: (String) -> (Int) -> (Int) -> T_Position 
sem_Position_Position arg_filename_ arg_line_ arg_column_ = T_Position (return st125) where
   {-# NOINLINE st125 #-}
   st125 = let
      v124 :: T_Position_v124 
      v124 = \ (T_Position_vIn124 ) -> ( let
         _self = rule2282 arg_column_ arg_filename_ arg_line_
         _lhsOself :: Position
         _lhsOself = rule2283 _self
         __result_ = T_Position_vOut124 _lhsOself
         in __result_ )
     in C_Position_s125 v124
   {-# INLINE rule2282 #-}
   rule2282 = \ column_ filename_ line_ ->
     Position_Position filename_ line_ column_
   {-# INLINE rule2283 #-}
   rule2283 = \ _self ->
     _self
{-# NOINLINE sem_Position_Unknown #-}
sem_Position_Unknown ::  T_Position 
sem_Position_Unknown  = T_Position (return st125) where
   {-# NOINLINE st125 #-}
   st125 = let
      v124 :: T_Position_v124 
      v124 = \ (T_Position_vIn124 ) -> ( let
         _self = rule2284  ()
         _lhsOself :: Position
         _lhsOself = rule2285 _self
         __result_ = T_Position_vOut124 _lhsOself
         in __result_ )
     in C_Position_s125 v124
   {-# INLINE rule2284 #-}
   rule2284 = \  (_ :: ()) ->
     Position_Unknown
   {-# INLINE rule2285 #-}
   rule2285 = \ _self ->
     _self

-- Qualifier ---------------------------------------------------
-- wrapper
data Inh_Qualifier  = Inh_Qualifier { allTypeConstructors_Inh_Qualifier :: (Names), allValueConstructors_Inh_Qualifier :: (Names), classEnvironment_Inh_Qualifier :: (ClassEnvironment), collectScopeInfos_Inh_Qualifier :: ([(ScopeInfo, Entity)]), counter_Inh_Qualifier :: (Int), kindErrors_Inh_Qualifier :: ([Error]), miscerrors_Inh_Qualifier :: ([Error]), namesInScope_Inh_Qualifier :: (Names), options_Inh_Qualifier :: ([Option]), orderedTypeSynonyms_Inh_Qualifier :: (OrderedTypeSynonyms), typeConstructors_Inh_Qualifier :: (M.Map Name Int), unboundNames_Inh_Qualifier :: (Names), valueConstructors_Inh_Qualifier :: (M.Map Name TpScheme), warnings_Inh_Qualifier :: ([Warning]) }
data Syn_Qualifier  = Syn_Qualifier { collectInstances_Syn_Qualifier :: ([(Name, Instance)]), collectScopeInfos_Syn_Qualifier :: ([(ScopeInfo, Entity)]), counter_Syn_Qualifier :: (Int), kindErrors_Syn_Qualifier :: ([Error]), miscerrors_Syn_Qualifier :: ([Error]), namesInScope_Syn_Qualifier :: (Names), self_Syn_Qualifier :: (Qualifier), unboundNames_Syn_Qualifier :: (Names), warnings_Syn_Qualifier :: ([Warning]) }
{-# INLINABLE wrap_Qualifier #-}
wrap_Qualifier :: T_Qualifier  -> Inh_Qualifier  -> (Syn_Qualifier )
wrap_Qualifier (T_Qualifier act) (Inh_Qualifier _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Qualifier_vIn127 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings
        (T_Qualifier_vOut127 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_Qualifier_s128 sem arg)
        return (Syn_Qualifier _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Qualifier #-}
sem_Qualifier :: Qualifier  -> T_Qualifier 
sem_Qualifier ( Qualifier_Guard range_ guard_ ) = sem_Qualifier_Guard ( sem_Range range_ ) ( sem_Expression guard_ )
sem_Qualifier ( Qualifier_Let range_ declarations_ ) = sem_Qualifier_Let ( sem_Range range_ ) ( sem_Declarations declarations_ )
sem_Qualifier ( Qualifier_Generator range_ pattern_ expression_ ) = sem_Qualifier_Generator ( sem_Range range_ ) ( sem_Pattern pattern_ ) ( sem_Expression expression_ )
sem_Qualifier ( Qualifier_Empty range_ ) = sem_Qualifier_Empty ( sem_Range range_ )

-- semantic domain
newtype T_Qualifier  = T_Qualifier {
                                   attach_T_Qualifier :: Identity (T_Qualifier_s128 )
                                   }
newtype T_Qualifier_s128  = C_Qualifier_s128 {
                                             inv_Qualifier_s128 :: (T_Qualifier_v127 )
                                             }
data T_Qualifier_s129  = C_Qualifier_s129
type T_Qualifier_v127  = (T_Qualifier_vIn127 ) -> (T_Qualifier_vOut127 )
data T_Qualifier_vIn127  = T_Qualifier_vIn127 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (Names) (M.Map Name TpScheme) ([Warning])
data T_Qualifier_vOut127  = T_Qualifier_vOut127 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) (Qualifier) (Names) ([Warning])
{-# NOINLINE sem_Qualifier_Guard #-}
sem_Qualifier_Guard :: T_Range  -> T_Expression  -> T_Qualifier 
sem_Qualifier_Guard arg_range_ arg_guard_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_guard_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _guardIcollectInstances _guardIcollectScopeInfos _guardIcounter _guardIkindErrors _guardImiscerrors _guardIself _guardIunboundNames _guardIwarnings) = inv_Expression_s41 _guardX41 (T_Expression_vIn40 _guardOallTypeConstructors _guardOallValueConstructors _guardOclassEnvironment _guardOcollectScopeInfos _guardOcounter _guardOkindErrors _guardOmiscerrors _guardOnamesInScope _guardOoptions _guardOorderedTypeSynonyms _guardOtypeConstructors _guardOvalueConstructors _guardOwarnings)
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2286 _guardIunboundNames _lhsIunboundNames
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2287 _guardIcollectInstances
         _self = rule2288 _guardIself _rangeIself
         _lhsOself :: Qualifier
         _lhsOself = rule2289 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2290 _guardIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2291 _guardIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2292 _guardIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2293 _guardImiscerrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2294 _lhsInamesInScope
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2295 _guardIwarnings
         _guardOallTypeConstructors = rule2296 _lhsIallTypeConstructors
         _guardOallValueConstructors = rule2297 _lhsIallValueConstructors
         _guardOclassEnvironment = rule2298 _lhsIclassEnvironment
         _guardOcollectScopeInfos = rule2299 _lhsIcollectScopeInfos
         _guardOcounter = rule2300 _lhsIcounter
         _guardOkindErrors = rule2301 _lhsIkindErrors
         _guardOmiscerrors = rule2302 _lhsImiscerrors
         _guardOnamesInScope = rule2303 _lhsInamesInScope
         _guardOoptions = rule2304 _lhsIoptions
         _guardOorderedTypeSynonyms = rule2305 _lhsIorderedTypeSynonyms
         _guardOtypeConstructors = rule2306 _lhsItypeConstructors
         _guardOvalueConstructors = rule2307 _lhsIvalueConstructors
         _guardOwarnings = rule2308 _lhsIwarnings
         __result_ = T_Qualifier_vOut127 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule2286 #-}
   rule2286 = \ ((_guardIunboundNames) :: Names) ((_lhsIunboundNames) :: Names) ->
                                              _guardIunboundNames ++ _lhsIunboundNames
   {-# INLINE rule2287 #-}
   rule2287 = \ ((_guardIcollectInstances) :: [(Name, Instance)]) ->
     _guardIcollectInstances
   {-# INLINE rule2288 #-}
   rule2288 = \ ((_guardIself) :: Expression) ((_rangeIself) :: Range) ->
     Qualifier_Guard _rangeIself _guardIself
   {-# INLINE rule2289 #-}
   rule2289 = \ _self ->
     _self
   {-# INLINE rule2290 #-}
   rule2290 = \ ((_guardIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _guardIcollectScopeInfos
   {-# INLINE rule2291 #-}
   rule2291 = \ ((_guardIcounter) :: Int) ->
     _guardIcounter
   {-# INLINE rule2292 #-}
   rule2292 = \ ((_guardIkindErrors) :: [Error]) ->
     _guardIkindErrors
   {-# INLINE rule2293 #-}
   rule2293 = \ ((_guardImiscerrors) :: [Error]) ->
     _guardImiscerrors
   {-# INLINE rule2294 #-}
   rule2294 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2295 #-}
   rule2295 = \ ((_guardIwarnings) :: [Warning]) ->
     _guardIwarnings
   {-# INLINE rule2296 #-}
   rule2296 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2297 #-}
   rule2297 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2298 #-}
   rule2298 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2299 #-}
   rule2299 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2300 #-}
   rule2300 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2301 #-}
   rule2301 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2302 #-}
   rule2302 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2303 #-}
   rule2303 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2304 #-}
   rule2304 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2305 #-}
   rule2305 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2306 #-}
   rule2306 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2307 #-}
   rule2307 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2308 #-}
   rule2308 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Qualifier_Let #-}
sem_Qualifier_Let :: T_Range  -> T_Declarations  -> T_Qualifier 
sem_Qualifier_Let arg_range_ arg_declarations_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Declarations_vOut31 _declarationsIcollectInstances _declarationsIcollectScopeInfos _declarationsIcollectTypeConstructors _declarationsIcollectTypeSynonyms _declarationsIcollectValueConstructors _declarationsIcounter _declarationsIdeclVarNames _declarationsIkindErrors _declarationsImiscerrors _declarationsIoperatorFixities _declarationsIpreviousWasAlsoFB _declarationsIrestrictedNames _declarationsIself _declarationsIsuspiciousFBs _declarationsItypeSignatures _declarationsIunboundNames _declarationsIwarnings) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 _declarationsOallTypeConstructors _declarationsOallValueConstructors _declarationsOclassEnvironment _declarationsOcollectScopeInfos _declarationsOcollectTypeConstructors _declarationsOcollectTypeSynonyms _declarationsOcollectValueConstructors _declarationsOcounter _declarationsOkindErrors _declarationsOmiscerrors _declarationsOnamesInScope _declarationsOoperatorFixities _declarationsOoptions _declarationsOorderedTypeSynonyms _declarationsOpreviousWasAlsoFB _declarationsOsuspiciousFBs _declarationsOtypeConstructors _declarationsOtypeSignatures _declarationsOvalueConstructors _declarationsOwarnings)
         _declarationsOtypeSignatures = rule2309  ()
         (_namesInScope,_unboundNames,_scopeInfo) = rule2310 _declarationsIdeclVarNames _declarationsIunboundNames _lhsInamesInScope _lhsIunboundNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2311 _unboundNames
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2312 _declarationsIwarnings _suspiciousErrors
         _declarationsOpreviousWasAlsoFB = rule2313  ()
         _declarationsOsuspiciousFBs = rule2314  ()
         _suspiciousErrors = rule2315 _declarationsIsuspiciousFBs _declarationsItypeSignatures
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2316 _declarationsImiscerrors _typeSignatureErrors
         (_,_doubles) = rule2317 _declarationsItypeSignatures
         _typeSignatureErrors = rule2318 _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
         (_collectTypeConstructors,_collectValueConstructors,_collectTypeSynonyms,_collectConstructorEnv,_derivedFunctions,_operatorFixities) = rule2319  ()
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2320 _declarationsIcollectScopeInfos _scopeInfo
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2321 _declarationsIcollectInstances
         _self = rule2322 _declarationsIself _rangeIself
         _lhsOself :: Qualifier
         _lhsOself = rule2323 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule2324 _declarationsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2325 _declarationsIkindErrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2326 _namesInScope
         _declarationsOallTypeConstructors = rule2327 _lhsIallTypeConstructors
         _declarationsOallValueConstructors = rule2328 _lhsIallValueConstructors
         _declarationsOclassEnvironment = rule2329 _lhsIclassEnvironment
         _declarationsOcollectScopeInfos = rule2330 _lhsIcollectScopeInfos
         _declarationsOcollectTypeConstructors = rule2331 _collectTypeConstructors
         _declarationsOcollectTypeSynonyms = rule2332 _collectTypeSynonyms
         _declarationsOcollectValueConstructors = rule2333 _collectValueConstructors
         _declarationsOcounter = rule2334 _lhsIcounter
         _declarationsOkindErrors = rule2335 _lhsIkindErrors
         _declarationsOmiscerrors = rule2336 _lhsImiscerrors
         _declarationsOnamesInScope = rule2337 _namesInScope
         _declarationsOoperatorFixities = rule2338 _operatorFixities
         _declarationsOoptions = rule2339 _lhsIoptions
         _declarationsOorderedTypeSynonyms = rule2340 _lhsIorderedTypeSynonyms
         _declarationsOtypeConstructors = rule2341 _lhsItypeConstructors
         _declarationsOvalueConstructors = rule2342 _lhsIvalueConstructors
         _declarationsOwarnings = rule2343 _lhsIwarnings
         __result_ = T_Qualifier_vOut127 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule2309 #-}
   rule2309 = \  (_ :: ()) ->
                                                                  []
   {-# INLINE rule2310 #-}
   rule2310 = \ ((_declarationsIdeclVarNames) :: Names) ((_declarationsIunboundNames) :: Names) ((_lhsInamesInScope) :: Names) ((_lhsIunboundNames) :: Names) ->
                                                             changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
   {-# INLINE rule2311 #-}
   rule2311 = \ _unboundNames ->
                                              _unboundNames
   {-# INLINE rule2312 #-}
   rule2312 = \ ((_declarationsIwarnings) :: [Warning]) _suspiciousErrors ->
                            _declarationsIwarnings ++
                            _suspiciousErrors
   {-# INLINE rule2313 #-}
   rule2313 = \  (_ :: ()) ->
                                                Nothing
   {-# INLINE rule2314 #-}
   rule2314 = \  (_ :: ()) ->
                                                []
   {-# INLINE rule2315 #-}
   rule2315 = \ ((_declarationsIsuspiciousFBs) :: [(Name,Name)]) ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                                findSimilarFunctionBindings _declarationsItypeSignatures _declarationsIsuspiciousFBs
   {-# INLINE rule2316 #-}
   rule2316 = \ ((_declarationsImiscerrors) :: [Error]) _typeSignatureErrors ->
                                   _typeSignatureErrors ++ _declarationsImiscerrors
   {-# INLINE rule2317 #-}
   rule2317 = \ ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                    uniqueAppearance (map fst _declarationsItypeSignatures)
   {-# INLINE rule2318 #-}
   rule2318 = \ ((_declarationsIdeclVarNames) :: Names) ((_declarationsIrestrictedNames) :: Names) ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                            checkTypeSignatures _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
   {-# INLINE rule2319 #-}
   rule2319 = \  (_ :: ()) ->
                                                                                                                                                   internalError "PartialSyntax.ag" "n/a" "toplevel Qualifier"
   {-# INLINE rule2320 #-}
   rule2320 = \ ((_declarationsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) _scopeInfo ->
                                                 (_scopeInfo, Definition) : _declarationsIcollectScopeInfos
   {-# INLINE rule2321 #-}
   rule2321 = \ ((_declarationsIcollectInstances) :: [(Name, Instance)]) ->
     _declarationsIcollectInstances
   {-# INLINE rule2322 #-}
   rule2322 = \ ((_declarationsIself) :: Declarations) ((_rangeIself) :: Range) ->
     Qualifier_Let _rangeIself _declarationsIself
   {-# INLINE rule2323 #-}
   rule2323 = \ _self ->
     _self
   {-# INLINE rule2324 #-}
   rule2324 = \ ((_declarationsIcounter) :: Int) ->
     _declarationsIcounter
   {-# INLINE rule2325 #-}
   rule2325 = \ ((_declarationsIkindErrors) :: [Error]) ->
     _declarationsIkindErrors
   {-# INLINE rule2326 #-}
   rule2326 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule2327 #-}
   rule2327 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2328 #-}
   rule2328 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2329 #-}
   rule2329 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2330 #-}
   rule2330 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2331 #-}
   rule2331 = \ _collectTypeConstructors ->
     _collectTypeConstructors
   {-# INLINE rule2332 #-}
   rule2332 = \ _collectTypeSynonyms ->
     _collectTypeSynonyms
   {-# INLINE rule2333 #-}
   rule2333 = \ _collectValueConstructors ->
     _collectValueConstructors
   {-# INLINE rule2334 #-}
   rule2334 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2335 #-}
   rule2335 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2336 #-}
   rule2336 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2337 #-}
   rule2337 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule2338 #-}
   rule2338 = \ _operatorFixities ->
     _operatorFixities
   {-# INLINE rule2339 #-}
   rule2339 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2340 #-}
   rule2340 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2341 #-}
   rule2341 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2342 #-}
   rule2342 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2343 #-}
   rule2343 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Qualifier_Generator #-}
sem_Qualifier_Generator :: T_Range  -> T_Pattern  -> T_Expression  -> T_Qualifier 
sem_Qualifier_Generator arg_range_ arg_pattern_ arg_expression_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIcollectScopeInfos _patternIcounter _patternImiscerrors _patternIpatVarNames _patternIself _patternIunboundNames _patternIwarnings) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOcounter _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings)
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         (_namesInScope,_unboundNames,_scopeInfo) = rule2344 _expressionIunboundNames _lhsInamesInScope _lhsIunboundNames _patternIpatVarNames
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2345 _namesInScope
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2346 _unboundNames
         _expressionOnamesInScope = rule2347 _lhsInamesInScope
         _patternOlhsPattern = rule2348  ()
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2349 _expressionIcollectScopeInfos _scopeInfo
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2350 _expressionIcollectInstances
         _self = rule2351 _expressionIself _patternIself _rangeIself
         _lhsOself :: Qualifier
         _lhsOself = rule2352 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule2353 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2354 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2355 _expressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2356 _expressionIwarnings
         _patternOallTypeConstructors = rule2357 _lhsIallTypeConstructors
         _patternOallValueConstructors = rule2358 _lhsIallValueConstructors
         _patternOcollectScopeInfos = rule2359 _lhsIcollectScopeInfos
         _patternOcounter = rule2360 _lhsIcounter
         _patternOmiscerrors = rule2361 _lhsImiscerrors
         _patternOnamesInScope = rule2362 _namesInScope
         _patternOtypeConstructors = rule2363 _lhsItypeConstructors
         _patternOvalueConstructors = rule2364 _lhsIvalueConstructors
         _patternOwarnings = rule2365 _lhsIwarnings
         _expressionOallTypeConstructors = rule2366 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule2367 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule2368 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule2369 _patternIcollectScopeInfos
         _expressionOcounter = rule2370 _patternIcounter
         _expressionOkindErrors = rule2371 _lhsIkindErrors
         _expressionOmiscerrors = rule2372 _patternImiscerrors
         _expressionOoptions = rule2373 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule2374 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule2375 _lhsItypeConstructors
         _expressionOvalueConstructors = rule2376 _lhsIvalueConstructors
         _expressionOwarnings = rule2377 _patternIwarnings
         __result_ = T_Qualifier_vOut127 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule2344 #-}
   rule2344 = \ ((_expressionIunboundNames) :: Names) ((_lhsInamesInScope) :: Names) ((_lhsIunboundNames) :: Names) ((_patternIpatVarNames) :: Names) ->
                                                                        changeOfScope _patternIpatVarNames (_expressionIunboundNames  ++ _lhsIunboundNames)  _lhsInamesInScope
   {-# INLINE rule2345 #-}
   rule2345 = \ _namesInScope ->
                                              _namesInScope
   {-# INLINE rule2346 #-}
   rule2346 = \ _unboundNames ->
                                              _unboundNames
   {-# INLINE rule2347 #-}
   rule2347 = \ ((_lhsInamesInScope) :: Names) ->
                                              _lhsInamesInScope
   {-# INLINE rule2348 #-}
   rule2348 = \  (_ :: ()) ->
                                                                False
   {-# INLINE rule2349 #-}
   rule2349 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) _scopeInfo ->
                                                 (_scopeInfo, Variable)   : _expressionIcollectScopeInfos
   {-# INLINE rule2350 #-}
   rule2350 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule2351 #-}
   rule2351 = \ ((_expressionIself) :: Expression) ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     Qualifier_Generator _rangeIself _patternIself _expressionIself
   {-# INLINE rule2352 #-}
   rule2352 = \ _self ->
     _self
   {-# INLINE rule2353 #-}
   rule2353 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule2354 #-}
   rule2354 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule2355 #-}
   rule2355 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule2356 #-}
   rule2356 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule2357 #-}
   rule2357 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2358 #-}
   rule2358 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2359 #-}
   rule2359 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2360 #-}
   rule2360 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2361 #-}
   rule2361 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2362 #-}
   rule2362 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule2363 #-}
   rule2363 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2364 #-}
   rule2364 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2365 #-}
   rule2365 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2366 #-}
   rule2366 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2367 #-}
   rule2367 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2368 #-}
   rule2368 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2369 #-}
   rule2369 = \ ((_patternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternIcollectScopeInfos
   {-# INLINE rule2370 #-}
   rule2370 = \ ((_patternIcounter) :: Int) ->
     _patternIcounter
   {-# INLINE rule2371 #-}
   rule2371 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2372 #-}
   rule2372 = \ ((_patternImiscerrors) :: [Error]) ->
     _patternImiscerrors
   {-# INLINE rule2373 #-}
   rule2373 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2374 #-}
   rule2374 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2375 #-}
   rule2375 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2376 #-}
   rule2376 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2377 #-}
   rule2377 = \ ((_patternIwarnings) :: [Warning]) ->
     _patternIwarnings
{-# NOINLINE sem_Qualifier_Empty #-}
sem_Qualifier_Empty :: T_Range  -> T_Qualifier 
sem_Qualifier_Empty arg_range_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2378  ()
         _self = rule2379 _rangeIself
         _lhsOself :: Qualifier
         _lhsOself = rule2380 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2381 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2382 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2383 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2384 _lhsImiscerrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2385 _lhsInamesInScope
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2386 _lhsIunboundNames
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2387 _lhsIwarnings
         __result_ = T_Qualifier_vOut127 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule2378 #-}
   rule2378 = \  (_ :: ()) ->
     []
   {-# INLINE rule2379 #-}
   rule2379 = \ ((_rangeIself) :: Range) ->
     Qualifier_Empty _rangeIself
   {-# INLINE rule2380 #-}
   rule2380 = \ _self ->
     _self
   {-# INLINE rule2381 #-}
   rule2381 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2382 #-}
   rule2382 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2383 #-}
   rule2383 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2384 #-}
   rule2384 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2385 #-}
   rule2385 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2386 #-}
   rule2386 = \ ((_lhsIunboundNames) :: Names) ->
     _lhsIunboundNames
   {-# INLINE rule2387 #-}
   rule2387 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Qualifiers --------------------------------------------------
-- wrapper
data Inh_Qualifiers  = Inh_Qualifiers { allTypeConstructors_Inh_Qualifiers :: (Names), allValueConstructors_Inh_Qualifiers :: (Names), classEnvironment_Inh_Qualifiers :: (ClassEnvironment), collectScopeInfos_Inh_Qualifiers :: ([(ScopeInfo, Entity)]), counter_Inh_Qualifiers :: (Int), kindErrors_Inh_Qualifiers :: ([Error]), miscerrors_Inh_Qualifiers :: ([Error]), namesInScope_Inh_Qualifiers :: (Names), options_Inh_Qualifiers :: ([Option]), orderedTypeSynonyms_Inh_Qualifiers :: (OrderedTypeSynonyms), typeConstructors_Inh_Qualifiers :: (M.Map Name Int), unboundNames_Inh_Qualifiers :: (Names), valueConstructors_Inh_Qualifiers :: (M.Map Name TpScheme), warnings_Inh_Qualifiers :: ([Warning]) }
data Syn_Qualifiers  = Syn_Qualifiers { collectInstances_Syn_Qualifiers :: ([(Name, Instance)]), collectScopeInfos_Syn_Qualifiers :: ([(ScopeInfo, Entity)]), counter_Syn_Qualifiers :: (Int), kindErrors_Syn_Qualifiers :: ([Error]), miscerrors_Syn_Qualifiers :: ([Error]), namesInScope_Syn_Qualifiers :: (Names), self_Syn_Qualifiers :: (Qualifiers), unboundNames_Syn_Qualifiers :: (Names), warnings_Syn_Qualifiers :: ([Warning]) }
{-# INLINABLE wrap_Qualifiers #-}
wrap_Qualifiers :: T_Qualifiers  -> Inh_Qualifiers  -> (Syn_Qualifiers )
wrap_Qualifiers (T_Qualifiers act) (Inh_Qualifiers _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Qualifiers_vIn130 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings
        (T_Qualifiers_vOut130 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_Qualifiers_s131 sem arg)
        return (Syn_Qualifiers _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Qualifiers #-}
sem_Qualifiers :: Qualifiers  -> T_Qualifiers 
sem_Qualifiers list = Prelude.foldr sem_Qualifiers_Cons sem_Qualifiers_Nil (Prelude.map sem_Qualifier list)

-- semantic domain
newtype T_Qualifiers  = T_Qualifiers {
                                     attach_T_Qualifiers :: Identity (T_Qualifiers_s131 )
                                     }
newtype T_Qualifiers_s131  = C_Qualifiers_s131 {
                                               inv_Qualifiers_s131 :: (T_Qualifiers_v130 )
                                               }
data T_Qualifiers_s132  = C_Qualifiers_s132
type T_Qualifiers_v130  = (T_Qualifiers_vIn130 ) -> (T_Qualifiers_vOut130 )
data T_Qualifiers_vIn130  = T_Qualifiers_vIn130 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (Names) (M.Map Name TpScheme) ([Warning])
data T_Qualifiers_vOut130  = T_Qualifiers_vOut130 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) (Qualifiers) (Names) ([Warning])
{-# NOINLINE sem_Qualifiers_Cons #-}
sem_Qualifiers_Cons :: T_Qualifier  -> T_Qualifiers  -> T_Qualifiers 
sem_Qualifiers_Cons arg_hd_ arg_tl_ = T_Qualifiers (return st131) where
   {-# NOINLINE st131 #-}
   st131 = let
      v130 :: T_Qualifiers_v130 
      v130 = \ (T_Qualifiers_vIn130 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _hdX128 = Control.Monad.Identity.runIdentity (attach_T_Qualifier (arg_hd_))
         _tlX131 = Control.Monad.Identity.runIdentity (attach_T_Qualifiers (arg_tl_))
         (T_Qualifier_vOut127 _hdIcollectInstances _hdIcollectScopeInfos _hdIcounter _hdIkindErrors _hdImiscerrors _hdInamesInScope _hdIself _hdIunboundNames _hdIwarnings) = inv_Qualifier_s128 _hdX128 (T_Qualifier_vIn127 _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOcounter _hdOkindErrors _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOunboundNames _hdOvalueConstructors _hdOwarnings)
         (T_Qualifiers_vOut130 _tlIcollectInstances _tlIcollectScopeInfos _tlIcounter _tlIkindErrors _tlImiscerrors _tlInamesInScope _tlIself _tlIunboundNames _tlIwarnings) = inv_Qualifiers_s131 _tlX131 (T_Qualifiers_vIn130 _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOcounter _tlOkindErrors _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOunboundNames _tlOvalueConstructors _tlOwarnings)
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2388 _hdIunboundNames
         _tlOunboundNames = rule2389 _lhsIunboundNames
         _hdOunboundNames = rule2390 _tlIunboundNames
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2391 _hdIcollectInstances _tlIcollectInstances
         _self = rule2392 _hdIself _tlIself
         _lhsOself :: Qualifiers
         _lhsOself = rule2393 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2394 _tlIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2395 _tlIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2396 _tlIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2397 _tlImiscerrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2398 _tlInamesInScope
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2399 _tlIwarnings
         _hdOallTypeConstructors = rule2400 _lhsIallTypeConstructors
         _hdOallValueConstructors = rule2401 _lhsIallValueConstructors
         _hdOclassEnvironment = rule2402 _lhsIclassEnvironment
         _hdOcollectScopeInfos = rule2403 _lhsIcollectScopeInfos
         _hdOcounter = rule2404 _lhsIcounter
         _hdOkindErrors = rule2405 _lhsIkindErrors
         _hdOmiscerrors = rule2406 _lhsImiscerrors
         _hdOnamesInScope = rule2407 _lhsInamesInScope
         _hdOoptions = rule2408 _lhsIoptions
         _hdOorderedTypeSynonyms = rule2409 _lhsIorderedTypeSynonyms
         _hdOtypeConstructors = rule2410 _lhsItypeConstructors
         _hdOvalueConstructors = rule2411 _lhsIvalueConstructors
         _hdOwarnings = rule2412 _lhsIwarnings
         _tlOallTypeConstructors = rule2413 _lhsIallTypeConstructors
         _tlOallValueConstructors = rule2414 _lhsIallValueConstructors
         _tlOclassEnvironment = rule2415 _lhsIclassEnvironment
         _tlOcollectScopeInfos = rule2416 _hdIcollectScopeInfos
         _tlOcounter = rule2417 _hdIcounter
         _tlOkindErrors = rule2418 _hdIkindErrors
         _tlOmiscerrors = rule2419 _hdImiscerrors
         _tlOnamesInScope = rule2420 _hdInamesInScope
         _tlOoptions = rule2421 _lhsIoptions
         _tlOorderedTypeSynonyms = rule2422 _lhsIorderedTypeSynonyms
         _tlOtypeConstructors = rule2423 _lhsItypeConstructors
         _tlOvalueConstructors = rule2424 _lhsIvalueConstructors
         _tlOwarnings = rule2425 _hdIwarnings
         __result_ = T_Qualifiers_vOut130 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Qualifiers_s131 v130
   {-# INLINE rule2388 #-}
   rule2388 = \ ((_hdIunboundNames) :: Names) ->
                                  _hdIunboundNames
   {-# INLINE rule2389 #-}
   rule2389 = \ ((_lhsIunboundNames) :: Names) ->
                                  _lhsIunboundNames
   {-# INLINE rule2390 #-}
   rule2390 = \ ((_tlIunboundNames) :: Names) ->
                                  _tlIunboundNames
   {-# INLINE rule2391 #-}
   rule2391 = \ ((_hdIcollectInstances) :: [(Name, Instance)]) ((_tlIcollectInstances) :: [(Name, Instance)]) ->
     _hdIcollectInstances  ++  _tlIcollectInstances
   {-# INLINE rule2392 #-}
   rule2392 = \ ((_hdIself) :: Qualifier) ((_tlIself) :: Qualifiers) ->
     (:) _hdIself _tlIself
   {-# INLINE rule2393 #-}
   rule2393 = \ _self ->
     _self
   {-# INLINE rule2394 #-}
   rule2394 = \ ((_tlIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _tlIcollectScopeInfos
   {-# INLINE rule2395 #-}
   rule2395 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule2396 #-}
   rule2396 = \ ((_tlIkindErrors) :: [Error]) ->
     _tlIkindErrors
   {-# INLINE rule2397 #-}
   rule2397 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule2398 #-}
   rule2398 = \ ((_tlInamesInScope) :: Names) ->
     _tlInamesInScope
   {-# INLINE rule2399 #-}
   rule2399 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule2400 #-}
   rule2400 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2401 #-}
   rule2401 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2402 #-}
   rule2402 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2403 #-}
   rule2403 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2404 #-}
   rule2404 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2405 #-}
   rule2405 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2406 #-}
   rule2406 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2407 #-}
   rule2407 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2408 #-}
   rule2408 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2409 #-}
   rule2409 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2410 #-}
   rule2410 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2411 #-}
   rule2411 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2412 #-}
   rule2412 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2413 #-}
   rule2413 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2414 #-}
   rule2414 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2415 #-}
   rule2415 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2416 #-}
   rule2416 = \ ((_hdIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _hdIcollectScopeInfos
   {-# INLINE rule2417 #-}
   rule2417 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule2418 #-}
   rule2418 = \ ((_hdIkindErrors) :: [Error]) ->
     _hdIkindErrors
   {-# INLINE rule2419 #-}
   rule2419 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule2420 #-}
   rule2420 = \ ((_hdInamesInScope) :: Names) ->
     _hdInamesInScope
   {-# INLINE rule2421 #-}
   rule2421 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2422 #-}
   rule2422 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2423 #-}
   rule2423 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2424 #-}
   rule2424 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2425 #-}
   rule2425 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_Qualifiers_Nil #-}
sem_Qualifiers_Nil ::  T_Qualifiers 
sem_Qualifiers_Nil  = T_Qualifiers (return st131) where
   {-# NOINLINE st131 #-}
   st131 = let
      v130 :: T_Qualifiers_v130 
      v130 = \ (T_Qualifiers_vIn130 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2426 _lhsIunboundNames
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2427  ()
         _self = rule2428  ()
         _lhsOself :: Qualifiers
         _lhsOself = rule2429 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2430 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2431 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2432 _lhsIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2433 _lhsImiscerrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2434 _lhsInamesInScope
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2435 _lhsIwarnings
         __result_ = T_Qualifiers_vOut130 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Qualifiers_s131 v130
   {-# INLINE rule2426 #-}
   rule2426 = \ ((_lhsIunboundNames) :: Names) ->
                                  _lhsIunboundNames
   {-# INLINE rule2427 #-}
   rule2427 = \  (_ :: ()) ->
     []
   {-# INLINE rule2428 #-}
   rule2428 = \  (_ :: ()) ->
     []
   {-# INLINE rule2429 #-}
   rule2429 = \ _self ->
     _self
   {-# INLINE rule2430 #-}
   rule2430 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2431 #-}
   rule2431 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2432 #-}
   rule2432 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2433 #-}
   rule2433 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2434 #-}
   rule2434 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2435 #-}
   rule2435 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Range -------------------------------------------------------
-- wrapper
data Inh_Range  = Inh_Range {  }
data Syn_Range  = Syn_Range { self_Syn_Range :: (Range) }
{-# INLINABLE wrap_Range #-}
wrap_Range :: T_Range  -> Inh_Range  -> (Syn_Range )
wrap_Range (T_Range act) (Inh_Range ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Range_vIn133 
        (T_Range_vOut133 _lhsOself) <- return (inv_Range_s134 sem arg)
        return (Syn_Range _lhsOself)
   )

-- cata
{-# INLINE sem_Range #-}
sem_Range :: Range  -> T_Range 
sem_Range ( Range_Range start_ stop_ ) = sem_Range_Range ( sem_Position start_ ) ( sem_Position stop_ )

-- semantic domain
newtype T_Range  = T_Range {
                           attach_T_Range :: Identity (T_Range_s134 )
                           }
newtype T_Range_s134  = C_Range_s134 {
                                     inv_Range_s134 :: (T_Range_v133 )
                                     }
data T_Range_s135  = C_Range_s135
type T_Range_v133  = (T_Range_vIn133 ) -> (T_Range_vOut133 )
data T_Range_vIn133  = T_Range_vIn133 
data T_Range_vOut133  = T_Range_vOut133 (Range)
{-# NOINLINE sem_Range_Range #-}
sem_Range_Range :: T_Position  -> T_Position  -> T_Range 
sem_Range_Range arg_start_ arg_stop_ = T_Range (return st134) where
   {-# NOINLINE st134 #-}
   st134 = let
      v133 :: T_Range_v133 
      v133 = \ (T_Range_vIn133 ) -> ( let
         _startX125 = Control.Monad.Identity.runIdentity (attach_T_Position (arg_start_))
         _stopX125 = Control.Monad.Identity.runIdentity (attach_T_Position (arg_stop_))
         (T_Position_vOut124 _startIself) = inv_Position_s125 _startX125 (T_Position_vIn124 )
         (T_Position_vOut124 _stopIself) = inv_Position_s125 _stopX125 (T_Position_vIn124 )
         _self = rule2436 _startIself _stopIself
         _lhsOself :: Range
         _lhsOself = rule2437 _self
         __result_ = T_Range_vOut133 _lhsOself
         in __result_ )
     in C_Range_s134 v133
   {-# INLINE rule2436 #-}
   rule2436 = \ ((_startIself) :: Position) ((_stopIself) :: Position) ->
     Range_Range _startIself _stopIself
   {-# INLINE rule2437 #-}
   rule2437 = \ _self ->
     _self

-- RecordExpressionBinding -------------------------------------
-- wrapper
data Inh_RecordExpressionBinding  = Inh_RecordExpressionBinding { classEnvironment_Inh_RecordExpressionBinding :: (ClassEnvironment), collectScopeInfos_Inh_RecordExpressionBinding :: ([(ScopeInfo, Entity)]), counter_Inh_RecordExpressionBinding :: (Int), namesInScope_Inh_RecordExpressionBinding :: (Names), options_Inh_RecordExpressionBinding :: ([Option]), orderedTypeSynonyms_Inh_RecordExpressionBinding :: (OrderedTypeSynonyms) }
data Syn_RecordExpressionBinding  = Syn_RecordExpressionBinding { collectInstances_Syn_RecordExpressionBinding :: ([(Name, Instance)]), collectScopeInfos_Syn_RecordExpressionBinding :: ([(ScopeInfo, Entity)]), counter_Syn_RecordExpressionBinding :: (Int), self_Syn_RecordExpressionBinding :: (RecordExpressionBinding), unboundNames_Syn_RecordExpressionBinding :: (Names) }
{-# INLINABLE wrap_RecordExpressionBinding #-}
wrap_RecordExpressionBinding :: T_RecordExpressionBinding  -> Inh_RecordExpressionBinding  -> (Syn_RecordExpressionBinding )
wrap_RecordExpressionBinding (T_RecordExpressionBinding act) (Inh_RecordExpressionBinding _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_RecordExpressionBinding_vIn136 _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms
        (T_RecordExpressionBinding_vOut136 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames) <- return (inv_RecordExpressionBinding_s137 sem arg)
        return (Syn_RecordExpressionBinding _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames)
   )

-- cata
{-# NOINLINE sem_RecordExpressionBinding #-}
sem_RecordExpressionBinding :: RecordExpressionBinding  -> T_RecordExpressionBinding 
sem_RecordExpressionBinding ( RecordExpressionBinding_RecordExpressionBinding range_ name_ expression_ ) = sem_RecordExpressionBinding_RecordExpressionBinding ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Expression expression_ )

-- semantic domain
newtype T_RecordExpressionBinding  = T_RecordExpressionBinding {
                                                               attach_T_RecordExpressionBinding :: Identity (T_RecordExpressionBinding_s137 )
                                                               }
newtype T_RecordExpressionBinding_s137  = C_RecordExpressionBinding_s137 {
                                                                         inv_RecordExpressionBinding_s137 :: (T_RecordExpressionBinding_v136 )
                                                                         }
data T_RecordExpressionBinding_s138  = C_RecordExpressionBinding_s138
type T_RecordExpressionBinding_v136  = (T_RecordExpressionBinding_vIn136 ) -> (T_RecordExpressionBinding_vOut136 )
data T_RecordExpressionBinding_vIn136  = T_RecordExpressionBinding_vIn136 (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) (Names) ([Option]) (OrderedTypeSynonyms)
data T_RecordExpressionBinding_vOut136  = T_RecordExpressionBinding_vOut136 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) (RecordExpressionBinding) (Names)
{-# NOINLINE sem_RecordExpressionBinding_RecordExpressionBinding #-}
sem_RecordExpressionBinding_RecordExpressionBinding :: T_Range  -> T_Name  -> T_Expression  -> T_RecordExpressionBinding 
sem_RecordExpressionBinding_RecordExpressionBinding arg_range_ arg_name_ arg_expression_ = T_RecordExpressionBinding (return st137) where
   {-# NOINLINE st137 #-}
   st137 = let
      v136 :: T_RecordExpressionBinding_v136 
      v136 = \ (T_RecordExpressionBinding_vIn136 _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         (_monos,_constructorenv,_betaUnique,_miscerrors,_warnings,_kindErrors,_valueConstructors,_allValueConstructors,_typeConstructors,_allTypeConstructors,_importEnvironment) = rule2438  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2439 _expressionIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2440 _expressionIunboundNames
         _self = rule2441 _expressionIself _nameIself _rangeIself
         _lhsOself :: RecordExpressionBinding
         _lhsOself = rule2442 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2443 _expressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2444 _expressionIcounter
         _expressionOallTypeConstructors = rule2445 _allTypeConstructors
         _expressionOallValueConstructors = rule2446 _allValueConstructors
         _expressionOclassEnvironment = rule2447 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule2448 _lhsIcollectScopeInfos
         _expressionOcounter = rule2449 _lhsIcounter
         _expressionOkindErrors = rule2450 _kindErrors
         _expressionOmiscerrors = rule2451 _miscerrors
         _expressionOnamesInScope = rule2452 _lhsInamesInScope
         _expressionOoptions = rule2453 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule2454 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule2455 _typeConstructors
         _expressionOvalueConstructors = rule2456 _valueConstructors
         _expressionOwarnings = rule2457 _warnings
         __result_ = T_RecordExpressionBinding_vOut136 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames
         in __result_ )
     in C_RecordExpressionBinding_s137 v136
   {-# INLINE rule2438 #-}
   rule2438 = \  (_ :: ()) ->
                                                                                                                                                                                                      internalError "PartialSyntax.ag" "n/a" "RecordExpressionBinding.RecordExpressionBinding"
   {-# INLINE rule2439 #-}
   rule2439 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule2440 #-}
   rule2440 = \ ((_expressionIunboundNames) :: Names) ->
     _expressionIunboundNames
   {-# INLINE rule2441 #-}
   rule2441 = \ ((_expressionIself) :: Expression) ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     RecordExpressionBinding_RecordExpressionBinding _rangeIself _nameIself _expressionIself
   {-# INLINE rule2442 #-}
   rule2442 = \ _self ->
     _self
   {-# INLINE rule2443 #-}
   rule2443 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule2444 #-}
   rule2444 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule2445 #-}
   rule2445 = \ _allTypeConstructors ->
     _allTypeConstructors
   {-# INLINE rule2446 #-}
   rule2446 = \ _allValueConstructors ->
     _allValueConstructors
   {-# INLINE rule2447 #-}
   rule2447 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2448 #-}
   rule2448 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2449 #-}
   rule2449 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2450 #-}
   rule2450 = \ _kindErrors ->
     _kindErrors
   {-# INLINE rule2451 #-}
   rule2451 = \ _miscerrors ->
     _miscerrors
   {-# INLINE rule2452 #-}
   rule2452 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2453 #-}
   rule2453 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2454 #-}
   rule2454 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2455 #-}
   rule2455 = \ _typeConstructors ->
     _typeConstructors
   {-# INLINE rule2456 #-}
   rule2456 = \ _valueConstructors ->
     _valueConstructors
   {-# INLINE rule2457 #-}
   rule2457 = \ _warnings ->
     _warnings

-- RecordExpressionBindings ------------------------------------
-- wrapper
data Inh_RecordExpressionBindings  = Inh_RecordExpressionBindings { classEnvironment_Inh_RecordExpressionBindings :: (ClassEnvironment), collectScopeInfos_Inh_RecordExpressionBindings :: ([(ScopeInfo, Entity)]), counter_Inh_RecordExpressionBindings :: (Int), namesInScope_Inh_RecordExpressionBindings :: (Names), options_Inh_RecordExpressionBindings :: ([Option]), orderedTypeSynonyms_Inh_RecordExpressionBindings :: (OrderedTypeSynonyms) }
data Syn_RecordExpressionBindings  = Syn_RecordExpressionBindings { collectInstances_Syn_RecordExpressionBindings :: ([(Name, Instance)]), collectScopeInfos_Syn_RecordExpressionBindings :: ([(ScopeInfo, Entity)]), counter_Syn_RecordExpressionBindings :: (Int), self_Syn_RecordExpressionBindings :: (RecordExpressionBindings), unboundNames_Syn_RecordExpressionBindings :: (Names) }
{-# INLINABLE wrap_RecordExpressionBindings #-}
wrap_RecordExpressionBindings :: T_RecordExpressionBindings  -> Inh_RecordExpressionBindings  -> (Syn_RecordExpressionBindings )
wrap_RecordExpressionBindings (T_RecordExpressionBindings act) (Inh_RecordExpressionBindings _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_RecordExpressionBindings_vIn139 _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms
        (T_RecordExpressionBindings_vOut139 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames) <- return (inv_RecordExpressionBindings_s140 sem arg)
        return (Syn_RecordExpressionBindings _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames)
   )

-- cata
{-# NOINLINE sem_RecordExpressionBindings #-}
sem_RecordExpressionBindings :: RecordExpressionBindings  -> T_RecordExpressionBindings 
sem_RecordExpressionBindings list = Prelude.foldr sem_RecordExpressionBindings_Cons sem_RecordExpressionBindings_Nil (Prelude.map sem_RecordExpressionBinding list)

-- semantic domain
newtype T_RecordExpressionBindings  = T_RecordExpressionBindings {
                                                                 attach_T_RecordExpressionBindings :: Identity (T_RecordExpressionBindings_s140 )
                                                                 }
newtype T_RecordExpressionBindings_s140  = C_RecordExpressionBindings_s140 {
                                                                           inv_RecordExpressionBindings_s140 :: (T_RecordExpressionBindings_v139 )
                                                                           }
data T_RecordExpressionBindings_s141  = C_RecordExpressionBindings_s141
type T_RecordExpressionBindings_v139  = (T_RecordExpressionBindings_vIn139 ) -> (T_RecordExpressionBindings_vOut139 )
data T_RecordExpressionBindings_vIn139  = T_RecordExpressionBindings_vIn139 (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) (Names) ([Option]) (OrderedTypeSynonyms)
data T_RecordExpressionBindings_vOut139  = T_RecordExpressionBindings_vOut139 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) (RecordExpressionBindings) (Names)
{-# NOINLINE sem_RecordExpressionBindings_Cons #-}
sem_RecordExpressionBindings_Cons :: T_RecordExpressionBinding  -> T_RecordExpressionBindings  -> T_RecordExpressionBindings 
sem_RecordExpressionBindings_Cons arg_hd_ arg_tl_ = T_RecordExpressionBindings (return st140) where
   {-# NOINLINE st140 #-}
   st140 = let
      v139 :: T_RecordExpressionBindings_v139 
      v139 = \ (T_RecordExpressionBindings_vIn139 _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms) -> ( let
         _hdX137 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBinding (arg_hd_))
         _tlX140 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBindings (arg_tl_))
         (T_RecordExpressionBinding_vOut136 _hdIcollectInstances _hdIcollectScopeInfos _hdIcounter _hdIself _hdIunboundNames) = inv_RecordExpressionBinding_s137 _hdX137 (T_RecordExpressionBinding_vIn136 _hdOclassEnvironment _hdOcollectScopeInfos _hdOcounter _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms)
         (T_RecordExpressionBindings_vOut139 _tlIcollectInstances _tlIcollectScopeInfos _tlIcounter _tlIself _tlIunboundNames) = inv_RecordExpressionBindings_s140 _tlX140 (T_RecordExpressionBindings_vIn139 _tlOclassEnvironment _tlOcollectScopeInfos _tlOcounter _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms)
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2458 _hdIcollectInstances _tlIcollectInstances
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2459 _hdIunboundNames _tlIunboundNames
         _self = rule2460 _hdIself _tlIself
         _lhsOself :: RecordExpressionBindings
         _lhsOself = rule2461 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2462 _tlIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2463 _tlIcounter
         _hdOclassEnvironment = rule2464 _lhsIclassEnvironment
         _hdOcollectScopeInfos = rule2465 _lhsIcollectScopeInfos
         _hdOcounter = rule2466 _lhsIcounter
         _hdOnamesInScope = rule2467 _lhsInamesInScope
         _hdOoptions = rule2468 _lhsIoptions
         _hdOorderedTypeSynonyms = rule2469 _lhsIorderedTypeSynonyms
         _tlOclassEnvironment = rule2470 _lhsIclassEnvironment
         _tlOcollectScopeInfos = rule2471 _hdIcollectScopeInfos
         _tlOcounter = rule2472 _hdIcounter
         _tlOnamesInScope = rule2473 _lhsInamesInScope
         _tlOoptions = rule2474 _lhsIoptions
         _tlOorderedTypeSynonyms = rule2475 _lhsIorderedTypeSynonyms
         __result_ = T_RecordExpressionBindings_vOut139 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames
         in __result_ )
     in C_RecordExpressionBindings_s140 v139
   {-# INLINE rule2458 #-}
   rule2458 = \ ((_hdIcollectInstances) :: [(Name, Instance)]) ((_tlIcollectInstances) :: [(Name, Instance)]) ->
     _hdIcollectInstances  ++  _tlIcollectInstances
   {-# INLINE rule2459 #-}
   rule2459 = \ ((_hdIunboundNames) :: Names) ((_tlIunboundNames) :: Names) ->
     _hdIunboundNames ++ _tlIunboundNames
   {-# INLINE rule2460 #-}
   rule2460 = \ ((_hdIself) :: RecordExpressionBinding) ((_tlIself) :: RecordExpressionBindings) ->
     (:) _hdIself _tlIself
   {-# INLINE rule2461 #-}
   rule2461 = \ _self ->
     _self
   {-# INLINE rule2462 #-}
   rule2462 = \ ((_tlIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _tlIcollectScopeInfos
   {-# INLINE rule2463 #-}
   rule2463 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule2464 #-}
   rule2464 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2465 #-}
   rule2465 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2466 #-}
   rule2466 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2467 #-}
   rule2467 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2468 #-}
   rule2468 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2469 #-}
   rule2469 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2470 #-}
   rule2470 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2471 #-}
   rule2471 = \ ((_hdIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _hdIcollectScopeInfos
   {-# INLINE rule2472 #-}
   rule2472 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule2473 #-}
   rule2473 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2474 #-}
   rule2474 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2475 #-}
   rule2475 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
{-# NOINLINE sem_RecordExpressionBindings_Nil #-}
sem_RecordExpressionBindings_Nil ::  T_RecordExpressionBindings 
sem_RecordExpressionBindings_Nil  = T_RecordExpressionBindings (return st140) where
   {-# NOINLINE st140 #-}
   st140 = let
      v139 :: T_RecordExpressionBindings_v139 
      v139 = \ (T_RecordExpressionBindings_vIn139 _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms) -> ( let
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2476  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2477  ()
         _self = rule2478  ()
         _lhsOself :: RecordExpressionBindings
         _lhsOself = rule2479 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2480 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2481 _lhsIcounter
         __result_ = T_RecordExpressionBindings_vOut139 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames
         in __result_ )
     in C_RecordExpressionBindings_s140 v139
   {-# INLINE rule2476 #-}
   rule2476 = \  (_ :: ()) ->
     []
   {-# INLINE rule2477 #-}
   rule2477 = \  (_ :: ()) ->
     []
   {-# INLINE rule2478 #-}
   rule2478 = \  (_ :: ()) ->
     []
   {-# INLINE rule2479 #-}
   rule2479 = \ _self ->
     _self
   {-# INLINE rule2480 #-}
   rule2480 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2481 #-}
   rule2481 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter

-- RecordPatternBinding ----------------------------------------
-- wrapper
data Inh_RecordPatternBinding  = Inh_RecordPatternBinding { collectScopeInfos_Inh_RecordPatternBinding :: ([(ScopeInfo, Entity)]), counter_Inh_RecordPatternBinding :: (Int), namesInScope_Inh_RecordPatternBinding :: (Names) }
data Syn_RecordPatternBinding  = Syn_RecordPatternBinding { collectScopeInfos_Syn_RecordPatternBinding :: ([(ScopeInfo, Entity)]), counter_Syn_RecordPatternBinding :: (Int), self_Syn_RecordPatternBinding :: (RecordPatternBinding), unboundNames_Syn_RecordPatternBinding :: (Names) }
{-# INLINABLE wrap_RecordPatternBinding #-}
wrap_RecordPatternBinding :: T_RecordPatternBinding  -> Inh_RecordPatternBinding  -> (Syn_RecordPatternBinding )
wrap_RecordPatternBinding (T_RecordPatternBinding act) (Inh_RecordPatternBinding _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_RecordPatternBinding_vIn142 _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope
        (T_RecordPatternBinding_vOut142 _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames) <- return (inv_RecordPatternBinding_s143 sem arg)
        return (Syn_RecordPatternBinding _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames)
   )

-- cata
{-# NOINLINE sem_RecordPatternBinding #-}
sem_RecordPatternBinding :: RecordPatternBinding  -> T_RecordPatternBinding 
sem_RecordPatternBinding ( RecordPatternBinding_RecordPatternBinding range_ name_ pattern_ ) = sem_RecordPatternBinding_RecordPatternBinding ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Pattern pattern_ )

-- semantic domain
newtype T_RecordPatternBinding  = T_RecordPatternBinding {
                                                         attach_T_RecordPatternBinding :: Identity (T_RecordPatternBinding_s143 )
                                                         }
newtype T_RecordPatternBinding_s143  = C_RecordPatternBinding_s143 {
                                                                   inv_RecordPatternBinding_s143 :: (T_RecordPatternBinding_v142 )
                                                                   }
data T_RecordPatternBinding_s144  = C_RecordPatternBinding_s144
type T_RecordPatternBinding_v142  = (T_RecordPatternBinding_vIn142 ) -> (T_RecordPatternBinding_vOut142 )
data T_RecordPatternBinding_vIn142  = T_RecordPatternBinding_vIn142 ([(ScopeInfo, Entity)]) (Int) (Names)
data T_RecordPatternBinding_vOut142  = T_RecordPatternBinding_vOut142 ([(ScopeInfo, Entity)]) (Int) (RecordPatternBinding) (Names)
{-# NOINLINE sem_RecordPatternBinding_RecordPatternBinding #-}
sem_RecordPatternBinding_RecordPatternBinding :: T_Range  -> T_Name  -> T_Pattern  -> T_RecordPatternBinding 
sem_RecordPatternBinding_RecordPatternBinding arg_range_ arg_name_ arg_pattern_ = T_RecordPatternBinding (return st143) where
   {-# NOINLINE st143 #-}
   st143 = let
      v142 :: T_RecordPatternBinding_v142 
      v142 = \ (T_RecordPatternBinding_vIn142 _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _patternIcollectScopeInfos _patternIcounter _patternImiscerrors _patternIpatVarNames _patternIself _patternIunboundNames _patternIwarnings) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOcounter _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings)
         _patternOlhsPattern = rule2482  ()
         (_monos,_constructorenv,_betaUnique,_miscerrors,_warnings,_valueConstructors,_allValueConstructors,_typeConstructors,_allTypeConstructors,_importEnvironment) = rule2483  ()
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2484 _patternIunboundNames
         _self = rule2485 _nameIself _patternIself _rangeIself
         _lhsOself :: RecordPatternBinding
         _lhsOself = rule2486 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2487 _patternIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2488 _patternIcounter
         _patternOallTypeConstructors = rule2489 _allTypeConstructors
         _patternOallValueConstructors = rule2490 _allValueConstructors
         _patternOcollectScopeInfos = rule2491 _lhsIcollectScopeInfos
         _patternOcounter = rule2492 _lhsIcounter
         _patternOmiscerrors = rule2493 _miscerrors
         _patternOnamesInScope = rule2494 _lhsInamesInScope
         _patternOtypeConstructors = rule2495 _typeConstructors
         _patternOvalueConstructors = rule2496 _valueConstructors
         _patternOwarnings = rule2497 _warnings
         __result_ = T_RecordPatternBinding_vOut142 _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames
         in __result_ )
     in C_RecordPatternBinding_s143 v142
   {-# INLINE rule2482 #-}
   rule2482 = \  (_ :: ()) ->
                                                                           False
   {-# INLINE rule2483 #-}
   rule2483 = \  (_ :: ()) ->
                                                                                                                                                                                          internalError "PartialSyntax.ag" "n/a" "RecordPatternBinding.RecordPatternBinding"
   {-# INLINE rule2484 #-}
   rule2484 = \ ((_patternIunboundNames) :: Names) ->
     _patternIunboundNames
   {-# INLINE rule2485 #-}
   rule2485 = \ ((_nameIself) :: Name) ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     RecordPatternBinding_RecordPatternBinding _rangeIself _nameIself _patternIself
   {-# INLINE rule2486 #-}
   rule2486 = \ _self ->
     _self
   {-# INLINE rule2487 #-}
   rule2487 = \ ((_patternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternIcollectScopeInfos
   {-# INLINE rule2488 #-}
   rule2488 = \ ((_patternIcounter) :: Int) ->
     _patternIcounter
   {-# INLINE rule2489 #-}
   rule2489 = \ _allTypeConstructors ->
     _allTypeConstructors
   {-# INLINE rule2490 #-}
   rule2490 = \ _allValueConstructors ->
     _allValueConstructors
   {-# INLINE rule2491 #-}
   rule2491 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2492 #-}
   rule2492 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2493 #-}
   rule2493 = \ _miscerrors ->
     _miscerrors
   {-# INLINE rule2494 #-}
   rule2494 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2495 #-}
   rule2495 = \ _typeConstructors ->
     _typeConstructors
   {-# INLINE rule2496 #-}
   rule2496 = \ _valueConstructors ->
     _valueConstructors
   {-# INLINE rule2497 #-}
   rule2497 = \ _warnings ->
     _warnings

-- RecordPatternBindings ---------------------------------------
-- wrapper
data Inh_RecordPatternBindings  = Inh_RecordPatternBindings { collectScopeInfos_Inh_RecordPatternBindings :: ([(ScopeInfo, Entity)]), counter_Inh_RecordPatternBindings :: (Int), namesInScope_Inh_RecordPatternBindings :: (Names) }
data Syn_RecordPatternBindings  = Syn_RecordPatternBindings { collectScopeInfos_Syn_RecordPatternBindings :: ([(ScopeInfo, Entity)]), counter_Syn_RecordPatternBindings :: (Int), self_Syn_RecordPatternBindings :: (RecordPatternBindings), unboundNames_Syn_RecordPatternBindings :: (Names) }
{-# INLINABLE wrap_RecordPatternBindings #-}
wrap_RecordPatternBindings :: T_RecordPatternBindings  -> Inh_RecordPatternBindings  -> (Syn_RecordPatternBindings )
wrap_RecordPatternBindings (T_RecordPatternBindings act) (Inh_RecordPatternBindings _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_RecordPatternBindings_vIn145 _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope
        (T_RecordPatternBindings_vOut145 _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames) <- return (inv_RecordPatternBindings_s146 sem arg)
        return (Syn_RecordPatternBindings _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames)
   )

-- cata
{-# NOINLINE sem_RecordPatternBindings #-}
sem_RecordPatternBindings :: RecordPatternBindings  -> T_RecordPatternBindings 
sem_RecordPatternBindings list = Prelude.foldr sem_RecordPatternBindings_Cons sem_RecordPatternBindings_Nil (Prelude.map sem_RecordPatternBinding list)

-- semantic domain
newtype T_RecordPatternBindings  = T_RecordPatternBindings {
                                                           attach_T_RecordPatternBindings :: Identity (T_RecordPatternBindings_s146 )
                                                           }
newtype T_RecordPatternBindings_s146  = C_RecordPatternBindings_s146 {
                                                                     inv_RecordPatternBindings_s146 :: (T_RecordPatternBindings_v145 )
                                                                     }
data T_RecordPatternBindings_s147  = C_RecordPatternBindings_s147
type T_RecordPatternBindings_v145  = (T_RecordPatternBindings_vIn145 ) -> (T_RecordPatternBindings_vOut145 )
data T_RecordPatternBindings_vIn145  = T_RecordPatternBindings_vIn145 ([(ScopeInfo, Entity)]) (Int) (Names)
data T_RecordPatternBindings_vOut145  = T_RecordPatternBindings_vOut145 ([(ScopeInfo, Entity)]) (Int) (RecordPatternBindings) (Names)
{-# NOINLINE sem_RecordPatternBindings_Cons #-}
sem_RecordPatternBindings_Cons :: T_RecordPatternBinding  -> T_RecordPatternBindings  -> T_RecordPatternBindings 
sem_RecordPatternBindings_Cons arg_hd_ arg_tl_ = T_RecordPatternBindings (return st146) where
   {-# NOINLINE st146 #-}
   st146 = let
      v145 :: T_RecordPatternBindings_v145 
      v145 = \ (T_RecordPatternBindings_vIn145 _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope) -> ( let
         _hdX143 = Control.Monad.Identity.runIdentity (attach_T_RecordPatternBinding (arg_hd_))
         _tlX146 = Control.Monad.Identity.runIdentity (attach_T_RecordPatternBindings (arg_tl_))
         (T_RecordPatternBinding_vOut142 _hdIcollectScopeInfos _hdIcounter _hdIself _hdIunboundNames) = inv_RecordPatternBinding_s143 _hdX143 (T_RecordPatternBinding_vIn142 _hdOcollectScopeInfos _hdOcounter _hdOnamesInScope)
         (T_RecordPatternBindings_vOut145 _tlIcollectScopeInfos _tlIcounter _tlIself _tlIunboundNames) = inv_RecordPatternBindings_s146 _tlX146 (T_RecordPatternBindings_vIn145 _tlOcollectScopeInfos _tlOcounter _tlOnamesInScope)
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2498 _hdIunboundNames _tlIunboundNames
         _self = rule2499 _hdIself _tlIself
         _lhsOself :: RecordPatternBindings
         _lhsOself = rule2500 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2501 _tlIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2502 _tlIcounter
         _hdOcollectScopeInfos = rule2503 _lhsIcollectScopeInfos
         _hdOcounter = rule2504 _lhsIcounter
         _hdOnamesInScope = rule2505 _lhsInamesInScope
         _tlOcollectScopeInfos = rule2506 _hdIcollectScopeInfos
         _tlOcounter = rule2507 _hdIcounter
         _tlOnamesInScope = rule2508 _lhsInamesInScope
         __result_ = T_RecordPatternBindings_vOut145 _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames
         in __result_ )
     in C_RecordPatternBindings_s146 v145
   {-# INLINE rule2498 #-}
   rule2498 = \ ((_hdIunboundNames) :: Names) ((_tlIunboundNames) :: Names) ->
     _hdIunboundNames ++ _tlIunboundNames
   {-# INLINE rule2499 #-}
   rule2499 = \ ((_hdIself) :: RecordPatternBinding) ((_tlIself) :: RecordPatternBindings) ->
     (:) _hdIself _tlIself
   {-# INLINE rule2500 #-}
   rule2500 = \ _self ->
     _self
   {-# INLINE rule2501 #-}
   rule2501 = \ ((_tlIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _tlIcollectScopeInfos
   {-# INLINE rule2502 #-}
   rule2502 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule2503 #-}
   rule2503 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2504 #-}
   rule2504 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2505 #-}
   rule2505 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2506 #-}
   rule2506 = \ ((_hdIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _hdIcollectScopeInfos
   {-# INLINE rule2507 #-}
   rule2507 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule2508 #-}
   rule2508 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
{-# NOINLINE sem_RecordPatternBindings_Nil #-}
sem_RecordPatternBindings_Nil ::  T_RecordPatternBindings 
sem_RecordPatternBindings_Nil  = T_RecordPatternBindings (return st146) where
   {-# NOINLINE st146 #-}
   st146 = let
      v145 :: T_RecordPatternBindings_v145 
      v145 = \ (T_RecordPatternBindings_vIn145 _lhsIcollectScopeInfos _lhsIcounter _lhsInamesInScope) -> ( let
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2509  ()
         _self = rule2510  ()
         _lhsOself :: RecordPatternBindings
         _lhsOself = rule2511 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2512 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2513 _lhsIcounter
         __result_ = T_RecordPatternBindings_vOut145 _lhsOcollectScopeInfos _lhsOcounter _lhsOself _lhsOunboundNames
         in __result_ )
     in C_RecordPatternBindings_s146 v145
   {-# INLINE rule2509 #-}
   rule2509 = \  (_ :: ()) ->
     []
   {-# INLINE rule2510 #-}
   rule2510 = \  (_ :: ()) ->
     []
   {-# INLINE rule2511 #-}
   rule2511 = \ _self ->
     _self
   {-# INLINE rule2512 #-}
   rule2512 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2513 #-}
   rule2513 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter

-- RightHandSide -----------------------------------------------
-- wrapper
data Inh_RightHandSide  = Inh_RightHandSide { allTypeConstructors_Inh_RightHandSide :: (Names), allValueConstructors_Inh_RightHandSide :: (Names), classEnvironment_Inh_RightHandSide :: (ClassEnvironment), collectScopeInfos_Inh_RightHandSide :: ([(ScopeInfo, Entity)]), counter_Inh_RightHandSide :: (Int), kindErrors_Inh_RightHandSide :: ([Error]), miscerrors_Inh_RightHandSide :: ([Error]), namesInScope_Inh_RightHandSide :: (Names), options_Inh_RightHandSide :: ([Option]), orderedTypeSynonyms_Inh_RightHandSide :: (OrderedTypeSynonyms), typeConstructors_Inh_RightHandSide :: (M.Map Name Int), valueConstructors_Inh_RightHandSide :: (M.Map Name TpScheme), warnings_Inh_RightHandSide :: ([Warning]) }
data Syn_RightHandSide  = Syn_RightHandSide { collectInstances_Syn_RightHandSide :: ([(Name, Instance)]), collectScopeInfos_Syn_RightHandSide :: ([(ScopeInfo, Entity)]), counter_Syn_RightHandSide :: (Int), kindErrors_Syn_RightHandSide :: ([Error]), miscerrors_Syn_RightHandSide :: ([Error]), self_Syn_RightHandSide :: (RightHandSide), unboundNames_Syn_RightHandSide :: (Names), warnings_Syn_RightHandSide :: ([Warning]) }
{-# INLINABLE wrap_RightHandSide #-}
wrap_RightHandSide :: T_RightHandSide  -> Inh_RightHandSide  -> (Syn_RightHandSide )
wrap_RightHandSide (T_RightHandSide act) (Inh_RightHandSide _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_RightHandSide_vIn148 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings
        (T_RightHandSide_vOut148 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_RightHandSide_s149 sem arg)
        return (Syn_RightHandSide _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_RightHandSide #-}
sem_RightHandSide :: RightHandSide  -> T_RightHandSide 
sem_RightHandSide ( RightHandSide_Expression range_ expression_ where_ ) = sem_RightHandSide_Expression ( sem_Range range_ ) ( sem_Expression expression_ ) ( sem_MaybeDeclarations where_ )
sem_RightHandSide ( RightHandSide_Guarded range_ guardedexpressions_ where_ ) = sem_RightHandSide_Guarded ( sem_Range range_ ) ( sem_GuardedExpressions guardedexpressions_ ) ( sem_MaybeDeclarations where_ )

-- semantic domain
newtype T_RightHandSide  = T_RightHandSide {
                                           attach_T_RightHandSide :: Identity (T_RightHandSide_s149 )
                                           }
newtype T_RightHandSide_s149  = C_RightHandSide_s149 {
                                                     inv_RightHandSide_s149 :: (T_RightHandSide_v148 )
                                                     }
data T_RightHandSide_s150  = C_RightHandSide_s150
type T_RightHandSide_v148  = (T_RightHandSide_vIn148 ) -> (T_RightHandSide_vOut148 )
data T_RightHandSide_vIn148  = T_RightHandSide_vIn148 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (M.Map Name TpScheme) ([Warning])
data T_RightHandSide_vOut148  = T_RightHandSide_vOut148 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) ([Error]) (RightHandSide) (Names) ([Warning])
{-# NOINLINE sem_RightHandSide_Expression #-}
sem_RightHandSide_Expression :: T_Range  -> T_Expression  -> T_MaybeDeclarations  -> T_RightHandSide 
sem_RightHandSide_Expression arg_range_ arg_expression_ arg_where_ = T_RightHandSide (return st149) where
   {-# NOINLINE st149 #-}
   st149 = let
      v148 :: T_RightHandSide_v148 
      v148 = \ (T_RightHandSide_vIn148 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         (T_MaybeDeclarations_vOut88 _whereIcollectInstances _whereIcollectScopeInfos _whereIcounter _whereIkindErrors _whereImiscerrors _whereInamesInScope _whereIself _whereIunboundNames _whereIwarnings) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 _whereOallTypeConstructors _whereOallValueConstructors _whereOclassEnvironment _whereOcollectScopeInfos _whereOcounter _whereOkindErrors _whereOmiscerrors _whereOnamesInScope _whereOoptions _whereOorderedTypeSynonyms _whereOtypeConstructors _whereOunboundNames _whereOvalueConstructors _whereOwarnings)
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2514 _whereIunboundNames
         _expressionOnamesInScope = rule2515 _whereInamesInScope
         _whereOunboundNames = rule2516 _expressionIunboundNames
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2517 _expressionIcollectInstances _whereIcollectInstances
         _self = rule2518 _expressionIself _rangeIself _whereIself
         _lhsOself :: RightHandSide
         _lhsOself = rule2519 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2520 _whereIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2521 _whereIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2522 _whereIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2523 _whereImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2524 _whereIwarnings
         _expressionOallTypeConstructors = rule2525 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule2526 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule2527 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule2528 _lhsIcollectScopeInfos
         _expressionOcounter = rule2529 _lhsIcounter
         _expressionOkindErrors = rule2530 _lhsIkindErrors
         _expressionOmiscerrors = rule2531 _lhsImiscerrors
         _expressionOoptions = rule2532 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule2533 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule2534 _lhsItypeConstructors
         _expressionOvalueConstructors = rule2535 _lhsIvalueConstructors
         _expressionOwarnings = rule2536 _lhsIwarnings
         _whereOallTypeConstructors = rule2537 _lhsIallTypeConstructors
         _whereOallValueConstructors = rule2538 _lhsIallValueConstructors
         _whereOclassEnvironment = rule2539 _lhsIclassEnvironment
         _whereOcollectScopeInfos = rule2540 _expressionIcollectScopeInfos
         _whereOcounter = rule2541 _expressionIcounter
         _whereOkindErrors = rule2542 _expressionIkindErrors
         _whereOmiscerrors = rule2543 _expressionImiscerrors
         _whereOnamesInScope = rule2544 _lhsInamesInScope
         _whereOoptions = rule2545 _lhsIoptions
         _whereOorderedTypeSynonyms = rule2546 _lhsIorderedTypeSynonyms
         _whereOtypeConstructors = rule2547 _lhsItypeConstructors
         _whereOvalueConstructors = rule2548 _lhsIvalueConstructors
         _whereOwarnings = rule2549 _expressionIwarnings
         __result_ = T_RightHandSide_vOut148 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_RightHandSide_s149 v148
   {-# INLINE rule2514 #-}
   rule2514 = \ ((_whereIunboundNames) :: Names) ->
                                                       _whereIunboundNames
   {-# INLINE rule2515 #-}
   rule2515 = \ ((_whereInamesInScope) :: Names) ->
                                                       _whereInamesInScope
   {-# INLINE rule2516 #-}
   rule2516 = \ ((_expressionIunboundNames) :: Names) ->
                                                       _expressionIunboundNames
   {-# INLINE rule2517 #-}
   rule2517 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ((_whereIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances  ++  _whereIcollectInstances
   {-# INLINE rule2518 #-}
   rule2518 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ((_whereIself) :: MaybeDeclarations) ->
     RightHandSide_Expression _rangeIself _expressionIself _whereIself
   {-# INLINE rule2519 #-}
   rule2519 = \ _self ->
     _self
   {-# INLINE rule2520 #-}
   rule2520 = \ ((_whereIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _whereIcollectScopeInfos
   {-# INLINE rule2521 #-}
   rule2521 = \ ((_whereIcounter) :: Int) ->
     _whereIcounter
   {-# INLINE rule2522 #-}
   rule2522 = \ ((_whereIkindErrors) :: [Error]) ->
     _whereIkindErrors
   {-# INLINE rule2523 #-}
   rule2523 = \ ((_whereImiscerrors) :: [Error]) ->
     _whereImiscerrors
   {-# INLINE rule2524 #-}
   rule2524 = \ ((_whereIwarnings) :: [Warning]) ->
     _whereIwarnings
   {-# INLINE rule2525 #-}
   rule2525 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2526 #-}
   rule2526 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2527 #-}
   rule2527 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2528 #-}
   rule2528 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2529 #-}
   rule2529 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2530 #-}
   rule2530 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2531 #-}
   rule2531 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2532 #-}
   rule2532 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2533 #-}
   rule2533 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2534 #-}
   rule2534 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2535 #-}
   rule2535 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2536 #-}
   rule2536 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2537 #-}
   rule2537 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2538 #-}
   rule2538 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2539 #-}
   rule2539 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2540 #-}
   rule2540 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule2541 #-}
   rule2541 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule2542 #-}
   rule2542 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule2543 #-}
   rule2543 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule2544 #-}
   rule2544 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2545 #-}
   rule2545 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2546 #-}
   rule2546 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2547 #-}
   rule2547 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2548 #-}
   rule2548 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2549 #-}
   rule2549 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
{-# NOINLINE sem_RightHandSide_Guarded #-}
sem_RightHandSide_Guarded :: T_Range  -> T_GuardedExpressions  -> T_MaybeDeclarations  -> T_RightHandSide 
sem_RightHandSide_Guarded arg_range_ arg_guardedexpressions_ arg_where_ = T_RightHandSide (return st149) where
   {-# NOINLINE st149 #-}
   st149 = let
      v148 :: T_RightHandSide_v148 
      v148 = \ (T_RightHandSide_vIn148 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardedexpressionsX65 = Control.Monad.Identity.runIdentity (attach_T_GuardedExpressions (arg_guardedexpressions_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_GuardedExpressions_vOut64 _guardedexpressionsIcollectInstances _guardedexpressionsIcollectScopeInfos _guardedexpressionsIcounter _guardedexpressionsIkindErrors _guardedexpressionsImiscerrors _guardedexpressionsIself _guardedexpressionsIunboundNames _guardedexpressionsIwarnings) = inv_GuardedExpressions_s65 _guardedexpressionsX65 (T_GuardedExpressions_vIn64 _guardedexpressionsOallTypeConstructors _guardedexpressionsOallValueConstructors _guardedexpressionsOclassEnvironment _guardedexpressionsOcollectScopeInfos _guardedexpressionsOcounter _guardedexpressionsOkindErrors _guardedexpressionsOmiscerrors _guardedexpressionsOnamesInScope _guardedexpressionsOoptions _guardedexpressionsOorderedTypeSynonyms _guardedexpressionsOtypeConstructors _guardedexpressionsOvalueConstructors _guardedexpressionsOwarnings)
         (T_MaybeDeclarations_vOut88 _whereIcollectInstances _whereIcollectScopeInfos _whereIcounter _whereIkindErrors _whereImiscerrors _whereInamesInScope _whereIself _whereIunboundNames _whereIwarnings) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 _whereOallTypeConstructors _whereOallValueConstructors _whereOclassEnvironment _whereOcollectScopeInfos _whereOcounter _whereOkindErrors _whereOmiscerrors _whereOnamesInScope _whereOoptions _whereOorderedTypeSynonyms _whereOtypeConstructors _whereOunboundNames _whereOvalueConstructors _whereOwarnings)
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2550 _whereIunboundNames
         _guardedexpressionsOnamesInScope = rule2551 _whereInamesInScope
         _whereOunboundNames = rule2552 _guardedexpressionsIunboundNames
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2553 _guardedexpressionsIcollectInstances _whereIcollectInstances
         _self = rule2554 _guardedexpressionsIself _rangeIself _whereIself
         _lhsOself :: RightHandSide
         _lhsOself = rule2555 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2556 _whereIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2557 _whereIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2558 _whereIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2559 _whereImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2560 _whereIwarnings
         _guardedexpressionsOallTypeConstructors = rule2561 _lhsIallTypeConstructors
         _guardedexpressionsOallValueConstructors = rule2562 _lhsIallValueConstructors
         _guardedexpressionsOclassEnvironment = rule2563 _lhsIclassEnvironment
         _guardedexpressionsOcollectScopeInfos = rule2564 _lhsIcollectScopeInfos
         _guardedexpressionsOcounter = rule2565 _lhsIcounter
         _guardedexpressionsOkindErrors = rule2566 _lhsIkindErrors
         _guardedexpressionsOmiscerrors = rule2567 _lhsImiscerrors
         _guardedexpressionsOoptions = rule2568 _lhsIoptions
         _guardedexpressionsOorderedTypeSynonyms = rule2569 _lhsIorderedTypeSynonyms
         _guardedexpressionsOtypeConstructors = rule2570 _lhsItypeConstructors
         _guardedexpressionsOvalueConstructors = rule2571 _lhsIvalueConstructors
         _guardedexpressionsOwarnings = rule2572 _lhsIwarnings
         _whereOallTypeConstructors = rule2573 _lhsIallTypeConstructors
         _whereOallValueConstructors = rule2574 _lhsIallValueConstructors
         _whereOclassEnvironment = rule2575 _lhsIclassEnvironment
         _whereOcollectScopeInfos = rule2576 _guardedexpressionsIcollectScopeInfos
         _whereOcounter = rule2577 _guardedexpressionsIcounter
         _whereOkindErrors = rule2578 _guardedexpressionsIkindErrors
         _whereOmiscerrors = rule2579 _guardedexpressionsImiscerrors
         _whereOnamesInScope = rule2580 _lhsInamesInScope
         _whereOoptions = rule2581 _lhsIoptions
         _whereOorderedTypeSynonyms = rule2582 _lhsIorderedTypeSynonyms
         _whereOtypeConstructors = rule2583 _lhsItypeConstructors
         _whereOvalueConstructors = rule2584 _lhsIvalueConstructors
         _whereOwarnings = rule2585 _guardedexpressionsIwarnings
         __result_ = T_RightHandSide_vOut148 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOmiscerrors _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_RightHandSide_s149 v148
   {-# INLINE rule2550 #-}
   rule2550 = \ ((_whereIunboundNames) :: Names) ->
                                                       _whereIunboundNames
   {-# INLINE rule2551 #-}
   rule2551 = \ ((_whereInamesInScope) :: Names) ->
                                                       _whereInamesInScope
   {-# INLINE rule2552 #-}
   rule2552 = \ ((_guardedexpressionsIunboundNames) :: Names) ->
                                                       _guardedexpressionsIunboundNames
   {-# INLINE rule2553 #-}
   rule2553 = \ ((_guardedexpressionsIcollectInstances) :: [(Name, Instance)]) ((_whereIcollectInstances) :: [(Name, Instance)]) ->
     _guardedexpressionsIcollectInstances  ++  _whereIcollectInstances
   {-# INLINE rule2554 #-}
   rule2554 = \ ((_guardedexpressionsIself) :: GuardedExpressions) ((_rangeIself) :: Range) ((_whereIself) :: MaybeDeclarations) ->
     RightHandSide_Guarded _rangeIself _guardedexpressionsIself _whereIself
   {-# INLINE rule2555 #-}
   rule2555 = \ _self ->
     _self
   {-# INLINE rule2556 #-}
   rule2556 = \ ((_whereIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _whereIcollectScopeInfos
   {-# INLINE rule2557 #-}
   rule2557 = \ ((_whereIcounter) :: Int) ->
     _whereIcounter
   {-# INLINE rule2558 #-}
   rule2558 = \ ((_whereIkindErrors) :: [Error]) ->
     _whereIkindErrors
   {-# INLINE rule2559 #-}
   rule2559 = \ ((_whereImiscerrors) :: [Error]) ->
     _whereImiscerrors
   {-# INLINE rule2560 #-}
   rule2560 = \ ((_whereIwarnings) :: [Warning]) ->
     _whereIwarnings
   {-# INLINE rule2561 #-}
   rule2561 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2562 #-}
   rule2562 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2563 #-}
   rule2563 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2564 #-}
   rule2564 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2565 #-}
   rule2565 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2566 #-}
   rule2566 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2567 #-}
   rule2567 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2568 #-}
   rule2568 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2569 #-}
   rule2569 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2570 #-}
   rule2570 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2571 #-}
   rule2571 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2572 #-}
   rule2572 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2573 #-}
   rule2573 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2574 #-}
   rule2574 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2575 #-}
   rule2575 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2576 #-}
   rule2576 = \ ((_guardedexpressionsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _guardedexpressionsIcollectScopeInfos
   {-# INLINE rule2577 #-}
   rule2577 = \ ((_guardedexpressionsIcounter) :: Int) ->
     _guardedexpressionsIcounter
   {-# INLINE rule2578 #-}
   rule2578 = \ ((_guardedexpressionsIkindErrors) :: [Error]) ->
     _guardedexpressionsIkindErrors
   {-# INLINE rule2579 #-}
   rule2579 = \ ((_guardedexpressionsImiscerrors) :: [Error]) ->
     _guardedexpressionsImiscerrors
   {-# INLINE rule2580 #-}
   rule2580 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2581 #-}
   rule2581 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2582 #-}
   rule2582 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2583 #-}
   rule2583 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2584 #-}
   rule2584 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2585 #-}
   rule2585 = \ ((_guardedexpressionsIwarnings) :: [Warning]) ->
     _guardedexpressionsIwarnings

-- SimpleType --------------------------------------------------
-- wrapper
data Inh_SimpleType  = Inh_SimpleType {  }
data Syn_SimpleType  = Syn_SimpleType { name_Syn_SimpleType :: (Name), self_Syn_SimpleType :: (SimpleType), typevariables_Syn_SimpleType :: (Names) }
{-# INLINABLE wrap_SimpleType #-}
wrap_SimpleType :: T_SimpleType  -> Inh_SimpleType  -> (Syn_SimpleType )
wrap_SimpleType (T_SimpleType act) (Inh_SimpleType ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_SimpleType_vIn151 
        (T_SimpleType_vOut151 _lhsOname _lhsOself _lhsOtypevariables) <- return (inv_SimpleType_s152 sem arg)
        return (Syn_SimpleType _lhsOname _lhsOself _lhsOtypevariables)
   )

-- cata
{-# INLINE sem_SimpleType #-}
sem_SimpleType :: SimpleType  -> T_SimpleType 
sem_SimpleType ( SimpleType_SimpleType range_ name_ typevariables_ ) = sem_SimpleType_SimpleType ( sem_Range range_ ) ( sem_Name name_ ) ( sem_Names typevariables_ )

-- semantic domain
newtype T_SimpleType  = T_SimpleType {
                                     attach_T_SimpleType :: Identity (T_SimpleType_s152 )
                                     }
newtype T_SimpleType_s152  = C_SimpleType_s152 {
                                               inv_SimpleType_s152 :: (T_SimpleType_v151 )
                                               }
data T_SimpleType_s153  = C_SimpleType_s153
type T_SimpleType_v151  = (T_SimpleType_vIn151 ) -> (T_SimpleType_vOut151 )
data T_SimpleType_vIn151  = T_SimpleType_vIn151 
data T_SimpleType_vOut151  = T_SimpleType_vOut151 (Name) (SimpleType) (Names)
{-# NOINLINE sem_SimpleType_SimpleType #-}
sem_SimpleType_SimpleType :: T_Range  -> T_Name  -> T_Names  -> T_SimpleType 
sem_SimpleType_SimpleType arg_range_ arg_name_ arg_typevariables_ = T_SimpleType (return st152) where
   {-# NOINLINE st152 #-}
   st152 = let
      v151 :: T_SimpleType_v151 
      v151 = \ (T_SimpleType_vIn151 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _typevariablesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_typevariables_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Names_vOut115 _typevariablesIself) = inv_Names_s116 _typevariablesX116 (T_Names_vIn115 )
         _lhsOname :: Name
         _lhsOname = rule2586 _nameIself
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule2587 _typevariablesIself
         _self = rule2588 _nameIself _rangeIself _typevariablesIself
         _lhsOself :: SimpleType
         _lhsOself = rule2589 _self
         __result_ = T_SimpleType_vOut151 _lhsOname _lhsOself _lhsOtypevariables
         in __result_ )
     in C_SimpleType_s152 v151
   {-# INLINE rule2586 #-}
   rule2586 = \ ((_nameIself) :: Name) ->
                                        _nameIself
   {-# INLINE rule2587 #-}
   rule2587 = \ ((_typevariablesIself) :: Names) ->
                                        _typevariablesIself
   {-# INLINE rule2588 #-}
   rule2588 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ((_typevariablesIself) :: Names) ->
     SimpleType_SimpleType _rangeIself _nameIself _typevariablesIself
   {-# INLINE rule2589 #-}
   rule2589 = \ _self ->
     _self

-- Statement ---------------------------------------------------
-- wrapper
data Inh_Statement  = Inh_Statement { allTypeConstructors_Inh_Statement :: (Names), allValueConstructors_Inh_Statement :: (Names), classEnvironment_Inh_Statement :: (ClassEnvironment), collectScopeInfos_Inh_Statement :: ([(ScopeInfo, Entity)]), counter_Inh_Statement :: (Int), kindErrors_Inh_Statement :: ([Error]), lastStatementIsExpr_Inh_Statement :: (Bool), miscerrors_Inh_Statement :: ([Error]), namesInScope_Inh_Statement :: (Names), options_Inh_Statement :: ([Option]), orderedTypeSynonyms_Inh_Statement :: (OrderedTypeSynonyms), typeConstructors_Inh_Statement :: (M.Map Name Int), unboundNames_Inh_Statement :: (Names), valueConstructors_Inh_Statement :: (M.Map Name TpScheme), warnings_Inh_Statement :: ([Warning]) }
data Syn_Statement  = Syn_Statement { collectInstances_Syn_Statement :: ([(Name, Instance)]), collectScopeInfos_Syn_Statement :: ([(ScopeInfo, Entity)]), counter_Syn_Statement :: (Int), kindErrors_Syn_Statement :: ([Error]), lastStatementIsExpr_Syn_Statement :: (Bool), miscerrors_Syn_Statement :: ([Error]), namesInScope_Syn_Statement :: (Names), self_Syn_Statement :: (Statement), unboundNames_Syn_Statement :: (Names), warnings_Syn_Statement :: ([Warning]) }
{-# INLINABLE wrap_Statement #-}
wrap_Statement :: T_Statement  -> Inh_Statement  -> (Syn_Statement )
wrap_Statement (T_Statement act) (Inh_Statement _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsIlastStatementIsExpr _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Statement_vIn154 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsIlastStatementIsExpr _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings
        (T_Statement_vOut154 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOlastStatementIsExpr _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_Statement_s155 sem arg)
        return (Syn_Statement _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOlastStatementIsExpr _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Statement #-}
sem_Statement :: Statement  -> T_Statement 
sem_Statement ( Statement_Expression range_ expression_ ) = sem_Statement_Expression ( sem_Range range_ ) ( sem_Expression expression_ )
sem_Statement ( Statement_Let range_ declarations_ ) = sem_Statement_Let ( sem_Range range_ ) ( sem_Declarations declarations_ )
sem_Statement ( Statement_Generator range_ pattern_ expression_ ) = sem_Statement_Generator ( sem_Range range_ ) ( sem_Pattern pattern_ ) ( sem_Expression expression_ )
sem_Statement ( Statement_Empty range_ ) = sem_Statement_Empty ( sem_Range range_ )

-- semantic domain
newtype T_Statement  = T_Statement {
                                   attach_T_Statement :: Identity (T_Statement_s155 )
                                   }
newtype T_Statement_s155  = C_Statement_s155 {
                                             inv_Statement_s155 :: (T_Statement_v154 )
                                             }
data T_Statement_s156  = C_Statement_s156
type T_Statement_v154  = (T_Statement_vIn154 ) -> (T_Statement_vOut154 )
data T_Statement_vIn154  = T_Statement_vIn154 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) (Bool) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (Names) (M.Map Name TpScheme) ([Warning])
data T_Statement_vOut154  = T_Statement_vOut154 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) (Bool) ([Error]) (Names) (Statement) (Names) ([Warning])
{-# NOINLINE sem_Statement_Expression #-}
sem_Statement_Expression :: T_Range  -> T_Expression  -> T_Statement 
sem_Statement_Expression arg_range_ arg_expression_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsIlastStatementIsExpr _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2590 _expressionIunboundNames _lhsIunboundNames
         _lhsOlastStatementIsExpr :: Bool
         _lhsOlastStatementIsExpr = rule2591  ()
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2592 _expressionIcollectInstances
         _self = rule2593 _expressionIself _rangeIself
         _lhsOself :: Statement
         _lhsOself = rule2594 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2595 _expressionIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2596 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2597 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2598 _expressionImiscerrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2599 _lhsInamesInScope
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2600 _expressionIwarnings
         _expressionOallTypeConstructors = rule2601 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule2602 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule2603 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule2604 _lhsIcollectScopeInfos
         _expressionOcounter = rule2605 _lhsIcounter
         _expressionOkindErrors = rule2606 _lhsIkindErrors
         _expressionOmiscerrors = rule2607 _lhsImiscerrors
         _expressionOnamesInScope = rule2608 _lhsInamesInScope
         _expressionOoptions = rule2609 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule2610 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule2611 _lhsItypeConstructors
         _expressionOvalueConstructors = rule2612 _lhsIvalueConstructors
         _expressionOwarnings = rule2613 _lhsIwarnings
         __result_ = T_Statement_vOut154 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOlastStatementIsExpr _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule2590 #-}
   rule2590 = \ ((_expressionIunboundNames) :: Names) ((_lhsIunboundNames) :: Names) ->
                                              _expressionIunboundNames ++ _lhsIunboundNames
   {-# INLINE rule2591 #-}
   rule2591 = \  (_ :: ()) ->
                                              True
   {-# INLINE rule2592 #-}
   rule2592 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule2593 #-}
   rule2593 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Statement_Expression _rangeIself _expressionIself
   {-# INLINE rule2594 #-}
   rule2594 = \ _self ->
     _self
   {-# INLINE rule2595 #-}
   rule2595 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _expressionIcollectScopeInfos
   {-# INLINE rule2596 #-}
   rule2596 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule2597 #-}
   rule2597 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule2598 #-}
   rule2598 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule2599 #-}
   rule2599 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2600 #-}
   rule2600 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule2601 #-}
   rule2601 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2602 #-}
   rule2602 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2603 #-}
   rule2603 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2604 #-}
   rule2604 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2605 #-}
   rule2605 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2606 #-}
   rule2606 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2607 #-}
   rule2607 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2608 #-}
   rule2608 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2609 #-}
   rule2609 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2610 #-}
   rule2610 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2611 #-}
   rule2611 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2612 #-}
   rule2612 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2613 #-}
   rule2613 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Statement_Let #-}
sem_Statement_Let :: T_Range  -> T_Declarations  -> T_Statement 
sem_Statement_Let arg_range_ arg_declarations_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsIlastStatementIsExpr _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Declarations_vOut31 _declarationsIcollectInstances _declarationsIcollectScopeInfos _declarationsIcollectTypeConstructors _declarationsIcollectTypeSynonyms _declarationsIcollectValueConstructors _declarationsIcounter _declarationsIdeclVarNames _declarationsIkindErrors _declarationsImiscerrors _declarationsIoperatorFixities _declarationsIpreviousWasAlsoFB _declarationsIrestrictedNames _declarationsIself _declarationsIsuspiciousFBs _declarationsItypeSignatures _declarationsIunboundNames _declarationsIwarnings) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 _declarationsOallTypeConstructors _declarationsOallValueConstructors _declarationsOclassEnvironment _declarationsOcollectScopeInfos _declarationsOcollectTypeConstructors _declarationsOcollectTypeSynonyms _declarationsOcollectValueConstructors _declarationsOcounter _declarationsOkindErrors _declarationsOmiscerrors _declarationsOnamesInScope _declarationsOoperatorFixities _declarationsOoptions _declarationsOorderedTypeSynonyms _declarationsOpreviousWasAlsoFB _declarationsOsuspiciousFBs _declarationsOtypeConstructors _declarationsOtypeSignatures _declarationsOvalueConstructors _declarationsOwarnings)
         _declarationsOtypeSignatures = rule2614  ()
         (_namesInScope,_unboundNames,_scopeInfo) = rule2615 _declarationsIdeclVarNames _declarationsIunboundNames _lhsInamesInScope _lhsIunboundNames
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2616 _unboundNames
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2617 _declarationsIwarnings _suspiciousErrors
         _declarationsOpreviousWasAlsoFB = rule2618  ()
         _declarationsOsuspiciousFBs = rule2619  ()
         _suspiciousErrors = rule2620 _declarationsIsuspiciousFBs _declarationsItypeSignatures
         _lhsOlastStatementIsExpr :: Bool
         _lhsOlastStatementIsExpr = rule2621  ()
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2622 _declarationsImiscerrors _typeSignatureErrors
         (_,_doubles) = rule2623 _declarationsItypeSignatures
         _typeSignatureErrors = rule2624 _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
         (_collectTypeConstructors,_collectValueConstructors,_collectTypeSynonyms,_collectConstructorEnv,_derivedFunctions,_operatorFixities) = rule2625  ()
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2626 _declarationsIcollectScopeInfos _scopeInfo
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2627 _declarationsIcollectInstances
         _self = rule2628 _declarationsIself _rangeIself
         _lhsOself :: Statement
         _lhsOself = rule2629 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule2630 _declarationsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2631 _declarationsIkindErrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2632 _namesInScope
         _declarationsOallTypeConstructors = rule2633 _lhsIallTypeConstructors
         _declarationsOallValueConstructors = rule2634 _lhsIallValueConstructors
         _declarationsOclassEnvironment = rule2635 _lhsIclassEnvironment
         _declarationsOcollectScopeInfos = rule2636 _lhsIcollectScopeInfos
         _declarationsOcollectTypeConstructors = rule2637 _collectTypeConstructors
         _declarationsOcollectTypeSynonyms = rule2638 _collectTypeSynonyms
         _declarationsOcollectValueConstructors = rule2639 _collectValueConstructors
         _declarationsOcounter = rule2640 _lhsIcounter
         _declarationsOkindErrors = rule2641 _lhsIkindErrors
         _declarationsOmiscerrors = rule2642 _lhsImiscerrors
         _declarationsOnamesInScope = rule2643 _namesInScope
         _declarationsOoperatorFixities = rule2644 _operatorFixities
         _declarationsOoptions = rule2645 _lhsIoptions
         _declarationsOorderedTypeSynonyms = rule2646 _lhsIorderedTypeSynonyms
         _declarationsOtypeConstructors = rule2647 _lhsItypeConstructors
         _declarationsOvalueConstructors = rule2648 _lhsIvalueConstructors
         _declarationsOwarnings = rule2649 _lhsIwarnings
         __result_ = T_Statement_vOut154 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOlastStatementIsExpr _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule2614 #-}
   rule2614 = \  (_ :: ()) ->
                                                                  []
   {-# INLINE rule2615 #-}
   rule2615 = \ ((_declarationsIdeclVarNames) :: Names) ((_declarationsIunboundNames) :: Names) ((_lhsInamesInScope) :: Names) ((_lhsIunboundNames) :: Names) ->
                                                             changeOfScope _declarationsIdeclVarNames (_declarationsIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
   {-# INLINE rule2616 #-}
   rule2616 = \ _unboundNames ->
                                              _unboundNames
   {-# INLINE rule2617 #-}
   rule2617 = \ ((_declarationsIwarnings) :: [Warning]) _suspiciousErrors ->
                            _declarationsIwarnings ++
                            _suspiciousErrors
   {-# INLINE rule2618 #-}
   rule2618 = \  (_ :: ()) ->
                                                Nothing
   {-# INLINE rule2619 #-}
   rule2619 = \  (_ :: ()) ->
                                                []
   {-# INLINE rule2620 #-}
   rule2620 = \ ((_declarationsIsuspiciousFBs) :: [(Name,Name)]) ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                                findSimilarFunctionBindings _declarationsItypeSignatures _declarationsIsuspiciousFBs
   {-# INLINE rule2621 #-}
   rule2621 = \  (_ :: ()) ->
                                              False
   {-# INLINE rule2622 #-}
   rule2622 = \ ((_declarationsImiscerrors) :: [Error]) _typeSignatureErrors ->
                                     _typeSignatureErrors ++ _declarationsImiscerrors
   {-# INLINE rule2623 #-}
   rule2623 = \ ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                      uniqueAppearance (map fst _declarationsItypeSignatures)
   {-# INLINE rule2624 #-}
   rule2624 = \ ((_declarationsIdeclVarNames) :: Names) ((_declarationsIrestrictedNames) :: Names) ((_declarationsItypeSignatures) :: [(Name,TpScheme)]) ->
                                              checkTypeSignatures _declarationsIdeclVarNames _declarationsIrestrictedNames _declarationsItypeSignatures
   {-# INLINE rule2625 #-}
   rule2625 = \  (_ :: ()) ->
                                                                                                                                                   internalError "PartialSyntax.ag" "n/a" "toplevel Statement"
   {-# INLINE rule2626 #-}
   rule2626 = \ ((_declarationsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) _scopeInfo ->
                                                 (_scopeInfo, Definition) : _declarationsIcollectScopeInfos
   {-# INLINE rule2627 #-}
   rule2627 = \ ((_declarationsIcollectInstances) :: [(Name, Instance)]) ->
     _declarationsIcollectInstances
   {-# INLINE rule2628 #-}
   rule2628 = \ ((_declarationsIself) :: Declarations) ((_rangeIself) :: Range) ->
     Statement_Let _rangeIself _declarationsIself
   {-# INLINE rule2629 #-}
   rule2629 = \ _self ->
     _self
   {-# INLINE rule2630 #-}
   rule2630 = \ ((_declarationsIcounter) :: Int) ->
     _declarationsIcounter
   {-# INLINE rule2631 #-}
   rule2631 = \ ((_declarationsIkindErrors) :: [Error]) ->
     _declarationsIkindErrors
   {-# INLINE rule2632 #-}
   rule2632 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule2633 #-}
   rule2633 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2634 #-}
   rule2634 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2635 #-}
   rule2635 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2636 #-}
   rule2636 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2637 #-}
   rule2637 = \ _collectTypeConstructors ->
     _collectTypeConstructors
   {-# INLINE rule2638 #-}
   rule2638 = \ _collectTypeSynonyms ->
     _collectTypeSynonyms
   {-# INLINE rule2639 #-}
   rule2639 = \ _collectValueConstructors ->
     _collectValueConstructors
   {-# INLINE rule2640 #-}
   rule2640 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2641 #-}
   rule2641 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2642 #-}
   rule2642 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2643 #-}
   rule2643 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule2644 #-}
   rule2644 = \ _operatorFixities ->
     _operatorFixities
   {-# INLINE rule2645 #-}
   rule2645 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2646 #-}
   rule2646 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2647 #-}
   rule2647 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2648 #-}
   rule2648 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2649 #-}
   rule2649 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Statement_Generator #-}
sem_Statement_Generator :: T_Range  -> T_Pattern  -> T_Expression  -> T_Statement 
sem_Statement_Generator arg_range_ arg_pattern_ arg_expression_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsIlastStatementIsExpr _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIcollectScopeInfos _patternIcounter _patternImiscerrors _patternIpatVarNames _patternIself _patternIunboundNames _patternIwarnings) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 _patternOallTypeConstructors _patternOallValueConstructors _patternOcollectScopeInfos _patternOcounter _patternOlhsPattern _patternOmiscerrors _patternOnamesInScope _patternOtypeConstructors _patternOvalueConstructors _patternOwarnings)
         (T_Expression_vOut40 _expressionIcollectInstances _expressionIcollectScopeInfos _expressionIcounter _expressionIkindErrors _expressionImiscerrors _expressionIself _expressionIunboundNames _expressionIwarnings) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOallTypeConstructors _expressionOallValueConstructors _expressionOclassEnvironment _expressionOcollectScopeInfos _expressionOcounter _expressionOkindErrors _expressionOmiscerrors _expressionOnamesInScope _expressionOoptions _expressionOorderedTypeSynonyms _expressionOtypeConstructors _expressionOvalueConstructors _expressionOwarnings)
         (_namesInScope,_unboundNames,_scopeInfo) = rule2650 _expressionIunboundNames _lhsInamesInScope _lhsIunboundNames _patternIpatVarNames
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2651 _namesInScope
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2652 _unboundNames
         _expressionOnamesInScope = rule2653 _lhsInamesInScope
         _lhsOlastStatementIsExpr :: Bool
         _lhsOlastStatementIsExpr = rule2654  ()
         _patternOlhsPattern = rule2655  ()
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2656 _expressionIcollectScopeInfos _scopeInfo
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2657 _expressionIcollectInstances
         _self = rule2658 _expressionIself _patternIself _rangeIself
         _lhsOself :: Statement
         _lhsOself = rule2659 _self
         _lhsOcounter :: Int
         _lhsOcounter = rule2660 _expressionIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2661 _expressionIkindErrors
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2662 _expressionImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2663 _expressionIwarnings
         _patternOallTypeConstructors = rule2664 _lhsIallTypeConstructors
         _patternOallValueConstructors = rule2665 _lhsIallValueConstructors
         _patternOcollectScopeInfos = rule2666 _lhsIcollectScopeInfos
         _patternOcounter = rule2667 _lhsIcounter
         _patternOmiscerrors = rule2668 _lhsImiscerrors
         _patternOnamesInScope = rule2669 _namesInScope
         _patternOtypeConstructors = rule2670 _lhsItypeConstructors
         _patternOvalueConstructors = rule2671 _lhsIvalueConstructors
         _patternOwarnings = rule2672 _lhsIwarnings
         _expressionOallTypeConstructors = rule2673 _lhsIallTypeConstructors
         _expressionOallValueConstructors = rule2674 _lhsIallValueConstructors
         _expressionOclassEnvironment = rule2675 _lhsIclassEnvironment
         _expressionOcollectScopeInfos = rule2676 _patternIcollectScopeInfos
         _expressionOcounter = rule2677 _patternIcounter
         _expressionOkindErrors = rule2678 _lhsIkindErrors
         _expressionOmiscerrors = rule2679 _patternImiscerrors
         _expressionOoptions = rule2680 _lhsIoptions
         _expressionOorderedTypeSynonyms = rule2681 _lhsIorderedTypeSynonyms
         _expressionOtypeConstructors = rule2682 _lhsItypeConstructors
         _expressionOvalueConstructors = rule2683 _lhsIvalueConstructors
         _expressionOwarnings = rule2684 _patternIwarnings
         __result_ = T_Statement_vOut154 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOlastStatementIsExpr _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule2650 #-}
   rule2650 = \ ((_expressionIunboundNames) :: Names) ((_lhsInamesInScope) :: Names) ((_lhsIunboundNames) :: Names) ((_patternIpatVarNames) :: Names) ->
                                                                        changeOfScope _patternIpatVarNames (_expressionIunboundNames ++ _lhsIunboundNames) _lhsInamesInScope
   {-# INLINE rule2651 #-}
   rule2651 = \ _namesInScope ->
                                              _namesInScope
   {-# INLINE rule2652 #-}
   rule2652 = \ _unboundNames ->
                                              _unboundNames
   {-# INLINE rule2653 #-}
   rule2653 = \ ((_lhsInamesInScope) :: Names) ->
                                              _lhsInamesInScope
   {-# INLINE rule2654 #-}
   rule2654 = \  (_ :: ()) ->
                                              False
   {-# INLINE rule2655 #-}
   rule2655 = \  (_ :: ()) ->
                                                                False
   {-# INLINE rule2656 #-}
   rule2656 = \ ((_expressionIcollectScopeInfos) :: [(ScopeInfo, Entity)]) _scopeInfo ->
                                                 (_scopeInfo, Variable)   : _expressionIcollectScopeInfos
   {-# INLINE rule2657 #-}
   rule2657 = \ ((_expressionIcollectInstances) :: [(Name, Instance)]) ->
     _expressionIcollectInstances
   {-# INLINE rule2658 #-}
   rule2658 = \ ((_expressionIself) :: Expression) ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     Statement_Generator _rangeIself _patternIself _expressionIself
   {-# INLINE rule2659 #-}
   rule2659 = \ _self ->
     _self
   {-# INLINE rule2660 #-}
   rule2660 = \ ((_expressionIcounter) :: Int) ->
     _expressionIcounter
   {-# INLINE rule2661 #-}
   rule2661 = \ ((_expressionIkindErrors) :: [Error]) ->
     _expressionIkindErrors
   {-# INLINE rule2662 #-}
   rule2662 = \ ((_expressionImiscerrors) :: [Error]) ->
     _expressionImiscerrors
   {-# INLINE rule2663 #-}
   rule2663 = \ ((_expressionIwarnings) :: [Warning]) ->
     _expressionIwarnings
   {-# INLINE rule2664 #-}
   rule2664 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2665 #-}
   rule2665 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2666 #-}
   rule2666 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2667 #-}
   rule2667 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2668 #-}
   rule2668 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2669 #-}
   rule2669 = \ _namesInScope ->
     _namesInScope
   {-# INLINE rule2670 #-}
   rule2670 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2671 #-}
   rule2671 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2672 #-}
   rule2672 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2673 #-}
   rule2673 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2674 #-}
   rule2674 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2675 #-}
   rule2675 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2676 #-}
   rule2676 = \ ((_patternIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _patternIcollectScopeInfos
   {-# INLINE rule2677 #-}
   rule2677 = \ ((_patternIcounter) :: Int) ->
     _patternIcounter
   {-# INLINE rule2678 #-}
   rule2678 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2679 #-}
   rule2679 = \ ((_patternImiscerrors) :: [Error]) ->
     _patternImiscerrors
   {-# INLINE rule2680 #-}
   rule2680 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2681 #-}
   rule2681 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2682 #-}
   rule2682 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2683 #-}
   rule2683 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2684 #-}
   rule2684 = \ ((_patternIwarnings) :: [Warning]) ->
     _patternIwarnings
{-# NOINLINE sem_Statement_Empty #-}
sem_Statement_Empty :: T_Range  -> T_Statement 
sem_Statement_Empty arg_range_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsIlastStatementIsExpr _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2685  ()
         _self = rule2686 _rangeIself
         _lhsOself :: Statement
         _lhsOself = rule2687 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2688 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2689 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2690 _lhsIkindErrors
         _lhsOlastStatementIsExpr :: Bool
         _lhsOlastStatementIsExpr = rule2691 _lhsIlastStatementIsExpr
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2692 _lhsImiscerrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2693 _lhsInamesInScope
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2694 _lhsIunboundNames
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2695 _lhsIwarnings
         __result_ = T_Statement_vOut154 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOlastStatementIsExpr _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule2685 #-}
   rule2685 = \  (_ :: ()) ->
     []
   {-# INLINE rule2686 #-}
   rule2686 = \ ((_rangeIself) :: Range) ->
     Statement_Empty _rangeIself
   {-# INLINE rule2687 #-}
   rule2687 = \ _self ->
     _self
   {-# INLINE rule2688 #-}
   rule2688 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2689 #-}
   rule2689 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2690 #-}
   rule2690 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2691 #-}
   rule2691 = \ ((_lhsIlastStatementIsExpr) :: Bool) ->
     _lhsIlastStatementIsExpr
   {-# INLINE rule2692 #-}
   rule2692 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2693 #-}
   rule2693 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2694 #-}
   rule2694 = \ ((_lhsIunboundNames) :: Names) ->
     _lhsIunboundNames
   {-# INLINE rule2695 #-}
   rule2695 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Statements --------------------------------------------------
-- wrapper
data Inh_Statements  = Inh_Statements { allTypeConstructors_Inh_Statements :: (Names), allValueConstructors_Inh_Statements :: (Names), classEnvironment_Inh_Statements :: (ClassEnvironment), collectScopeInfos_Inh_Statements :: ([(ScopeInfo, Entity)]), counter_Inh_Statements :: (Int), kindErrors_Inh_Statements :: ([Error]), lastStatementIsExpr_Inh_Statements :: (Bool), miscerrors_Inh_Statements :: ([Error]), namesInScope_Inh_Statements :: (Names), options_Inh_Statements :: ([Option]), orderedTypeSynonyms_Inh_Statements :: (OrderedTypeSynonyms), typeConstructors_Inh_Statements :: (M.Map Name Int), unboundNames_Inh_Statements :: (Names), valueConstructors_Inh_Statements :: (M.Map Name TpScheme), warnings_Inh_Statements :: ([Warning]) }
data Syn_Statements  = Syn_Statements { collectInstances_Syn_Statements :: ([(Name, Instance)]), collectScopeInfos_Syn_Statements :: ([(ScopeInfo, Entity)]), counter_Syn_Statements :: (Int), kindErrors_Syn_Statements :: ([Error]), lastStatementIsExpr_Syn_Statements :: (Bool), miscerrors_Syn_Statements :: ([Error]), namesInScope_Syn_Statements :: (Names), self_Syn_Statements :: (Statements), unboundNames_Syn_Statements :: (Names), warnings_Syn_Statements :: ([Warning]) }
{-# INLINABLE wrap_Statements #-}
wrap_Statements :: T_Statements  -> Inh_Statements  -> (Syn_Statements )
wrap_Statements (T_Statements act) (Inh_Statements _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsIlastStatementIsExpr _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Statements_vIn157 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsIlastStatementIsExpr _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings
        (T_Statements_vOut157 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOlastStatementIsExpr _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings) <- return (inv_Statements_s158 sem arg)
        return (Syn_Statements _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOlastStatementIsExpr _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Statements #-}
sem_Statements :: Statements  -> T_Statements 
sem_Statements list = Prelude.foldr sem_Statements_Cons sem_Statements_Nil (Prelude.map sem_Statement list)

-- semantic domain
newtype T_Statements  = T_Statements {
                                     attach_T_Statements :: Identity (T_Statements_s158 )
                                     }
newtype T_Statements_s158  = C_Statements_s158 {
                                               inv_Statements_s158 :: (T_Statements_v157 )
                                               }
data T_Statements_s159  = C_Statements_s159
type T_Statements_v157  = (T_Statements_vIn157 ) -> (T_Statements_vOut157 )
data T_Statements_vIn157  = T_Statements_vIn157 (Names) (Names) (ClassEnvironment) ([(ScopeInfo, Entity)]) (Int) ([Error]) (Bool) ([Error]) (Names) ([Option]) (OrderedTypeSynonyms) (M.Map Name Int) (Names) (M.Map Name TpScheme) ([Warning])
data T_Statements_vOut157  = T_Statements_vOut157 ([(Name, Instance)]) ([(ScopeInfo, Entity)]) (Int) ([Error]) (Bool) ([Error]) (Names) (Statements) (Names) ([Warning])
{-# NOINLINE sem_Statements_Cons #-}
sem_Statements_Cons :: T_Statement  -> T_Statements  -> T_Statements 
sem_Statements_Cons arg_hd_ arg_tl_ = T_Statements (return st158) where
   {-# NOINLINE st158 #-}
   st158 = let
      v157 :: T_Statements_v157 
      v157 = \ (T_Statements_vIn157 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsIlastStatementIsExpr _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _hdX155 = Control.Monad.Identity.runIdentity (attach_T_Statement (arg_hd_))
         _tlX158 = Control.Monad.Identity.runIdentity (attach_T_Statements (arg_tl_))
         (T_Statement_vOut154 _hdIcollectInstances _hdIcollectScopeInfos _hdIcounter _hdIkindErrors _hdIlastStatementIsExpr _hdImiscerrors _hdInamesInScope _hdIself _hdIunboundNames _hdIwarnings) = inv_Statement_s155 _hdX155 (T_Statement_vIn154 _hdOallTypeConstructors _hdOallValueConstructors _hdOclassEnvironment _hdOcollectScopeInfos _hdOcounter _hdOkindErrors _hdOlastStatementIsExpr _hdOmiscerrors _hdOnamesInScope _hdOoptions _hdOorderedTypeSynonyms _hdOtypeConstructors _hdOunboundNames _hdOvalueConstructors _hdOwarnings)
         (T_Statements_vOut157 _tlIcollectInstances _tlIcollectScopeInfos _tlIcounter _tlIkindErrors _tlIlastStatementIsExpr _tlImiscerrors _tlInamesInScope _tlIself _tlIunboundNames _tlIwarnings) = inv_Statements_s158 _tlX158 (T_Statements_vIn157 _tlOallTypeConstructors _tlOallValueConstructors _tlOclassEnvironment _tlOcollectScopeInfos _tlOcounter _tlOkindErrors _tlOlastStatementIsExpr _tlOmiscerrors _tlOnamesInScope _tlOoptions _tlOorderedTypeSynonyms _tlOtypeConstructors _tlOunboundNames _tlOvalueConstructors _tlOwarnings)
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2696 _hdIunboundNames
         _tlOunboundNames = rule2697 _lhsIunboundNames
         _hdOunboundNames = rule2698 _tlIunboundNames
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2699 _hdIcollectInstances _tlIcollectInstances
         _self = rule2700 _hdIself _tlIself
         _lhsOself :: Statements
         _lhsOself = rule2701 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2702 _tlIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2703 _tlIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2704 _tlIkindErrors
         _lhsOlastStatementIsExpr :: Bool
         _lhsOlastStatementIsExpr = rule2705 _tlIlastStatementIsExpr
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2706 _tlImiscerrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2707 _tlInamesInScope
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2708 _tlIwarnings
         _hdOallTypeConstructors = rule2709 _lhsIallTypeConstructors
         _hdOallValueConstructors = rule2710 _lhsIallValueConstructors
         _hdOclassEnvironment = rule2711 _lhsIclassEnvironment
         _hdOcollectScopeInfos = rule2712 _lhsIcollectScopeInfos
         _hdOcounter = rule2713 _lhsIcounter
         _hdOkindErrors = rule2714 _lhsIkindErrors
         _hdOlastStatementIsExpr = rule2715 _lhsIlastStatementIsExpr
         _hdOmiscerrors = rule2716 _lhsImiscerrors
         _hdOnamesInScope = rule2717 _lhsInamesInScope
         _hdOoptions = rule2718 _lhsIoptions
         _hdOorderedTypeSynonyms = rule2719 _lhsIorderedTypeSynonyms
         _hdOtypeConstructors = rule2720 _lhsItypeConstructors
         _hdOvalueConstructors = rule2721 _lhsIvalueConstructors
         _hdOwarnings = rule2722 _lhsIwarnings
         _tlOallTypeConstructors = rule2723 _lhsIallTypeConstructors
         _tlOallValueConstructors = rule2724 _lhsIallValueConstructors
         _tlOclassEnvironment = rule2725 _lhsIclassEnvironment
         _tlOcollectScopeInfos = rule2726 _hdIcollectScopeInfos
         _tlOcounter = rule2727 _hdIcounter
         _tlOkindErrors = rule2728 _hdIkindErrors
         _tlOlastStatementIsExpr = rule2729 _hdIlastStatementIsExpr
         _tlOmiscerrors = rule2730 _hdImiscerrors
         _tlOnamesInScope = rule2731 _hdInamesInScope
         _tlOoptions = rule2732 _lhsIoptions
         _tlOorderedTypeSynonyms = rule2733 _lhsIorderedTypeSynonyms
         _tlOtypeConstructors = rule2734 _lhsItypeConstructors
         _tlOvalueConstructors = rule2735 _lhsIvalueConstructors
         _tlOwarnings = rule2736 _hdIwarnings
         __result_ = T_Statements_vOut157 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOlastStatementIsExpr _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Statements_s158 v157
   {-# INLINE rule2696 #-}
   rule2696 = \ ((_hdIunboundNames) :: Names) ->
                                  _hdIunboundNames
   {-# INLINE rule2697 #-}
   rule2697 = \ ((_lhsIunboundNames) :: Names) ->
                                  _lhsIunboundNames
   {-# INLINE rule2698 #-}
   rule2698 = \ ((_tlIunboundNames) :: Names) ->
                                  _tlIunboundNames
   {-# INLINE rule2699 #-}
   rule2699 = \ ((_hdIcollectInstances) :: [(Name, Instance)]) ((_tlIcollectInstances) :: [(Name, Instance)]) ->
     _hdIcollectInstances  ++  _tlIcollectInstances
   {-# INLINE rule2700 #-}
   rule2700 = \ ((_hdIself) :: Statement) ((_tlIself) :: Statements) ->
     (:) _hdIself _tlIself
   {-# INLINE rule2701 #-}
   rule2701 = \ _self ->
     _self
   {-# INLINE rule2702 #-}
   rule2702 = \ ((_tlIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _tlIcollectScopeInfos
   {-# INLINE rule2703 #-}
   rule2703 = \ ((_tlIcounter) :: Int) ->
     _tlIcounter
   {-# INLINE rule2704 #-}
   rule2704 = \ ((_tlIkindErrors) :: [Error]) ->
     _tlIkindErrors
   {-# INLINE rule2705 #-}
   rule2705 = \ ((_tlIlastStatementIsExpr) :: Bool) ->
     _tlIlastStatementIsExpr
   {-# INLINE rule2706 #-}
   rule2706 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule2707 #-}
   rule2707 = \ ((_tlInamesInScope) :: Names) ->
     _tlInamesInScope
   {-# INLINE rule2708 #-}
   rule2708 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule2709 #-}
   rule2709 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2710 #-}
   rule2710 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2711 #-}
   rule2711 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2712 #-}
   rule2712 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2713 #-}
   rule2713 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2714 #-}
   rule2714 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2715 #-}
   rule2715 = \ ((_lhsIlastStatementIsExpr) :: Bool) ->
     _lhsIlastStatementIsExpr
   {-# INLINE rule2716 #-}
   rule2716 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2717 #-}
   rule2717 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2718 #-}
   rule2718 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2719 #-}
   rule2719 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2720 #-}
   rule2720 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2721 #-}
   rule2721 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2722 #-}
   rule2722 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2723 #-}
   rule2723 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2724 #-}
   rule2724 = \ ((_lhsIallValueConstructors) :: Names) ->
     _lhsIallValueConstructors
   {-# INLINE rule2725 #-}
   rule2725 = \ ((_lhsIclassEnvironment) :: ClassEnvironment) ->
     _lhsIclassEnvironment
   {-# INLINE rule2726 #-}
   rule2726 = \ ((_hdIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _hdIcollectScopeInfos
   {-# INLINE rule2727 #-}
   rule2727 = \ ((_hdIcounter) :: Int) ->
     _hdIcounter
   {-# INLINE rule2728 #-}
   rule2728 = \ ((_hdIkindErrors) :: [Error]) ->
     _hdIkindErrors
   {-# INLINE rule2729 #-}
   rule2729 = \ ((_hdIlastStatementIsExpr) :: Bool) ->
     _hdIlastStatementIsExpr
   {-# INLINE rule2730 #-}
   rule2730 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule2731 #-}
   rule2731 = \ ((_hdInamesInScope) :: Names) ->
     _hdInamesInScope
   {-# INLINE rule2732 #-}
   rule2732 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2733 #-}
   rule2733 = \ ((_lhsIorderedTypeSynonyms) :: OrderedTypeSynonyms) ->
     _lhsIorderedTypeSynonyms
   {-# INLINE rule2734 #-}
   rule2734 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2735 #-}
   rule2735 = \ ((_lhsIvalueConstructors) :: M.Map Name TpScheme) ->
     _lhsIvalueConstructors
   {-# INLINE rule2736 #-}
   rule2736 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_Statements_Nil #-}
sem_Statements_Nil ::  T_Statements 
sem_Statements_Nil  = T_Statements (return st158) where
   {-# NOINLINE st158 #-}
   st158 = let
      v157 :: T_Statements_v157 
      v157 = \ (T_Statements_vIn157 _lhsIallTypeConstructors _lhsIallValueConstructors _lhsIclassEnvironment _lhsIcollectScopeInfos _lhsIcounter _lhsIkindErrors _lhsIlastStatementIsExpr _lhsImiscerrors _lhsInamesInScope _lhsIoptions _lhsIorderedTypeSynonyms _lhsItypeConstructors _lhsIunboundNames _lhsIvalueConstructors _lhsIwarnings) -> ( let
         _lhsOunboundNames :: Names
         _lhsOunboundNames = rule2737 _lhsIunboundNames
         _lhsOcollectInstances :: [(Name, Instance)]
         _lhsOcollectInstances = rule2738  ()
         _self = rule2739  ()
         _lhsOself :: Statements
         _lhsOself = rule2740 _self
         _lhsOcollectScopeInfos :: [(ScopeInfo, Entity)]
         _lhsOcollectScopeInfos = rule2741 _lhsIcollectScopeInfos
         _lhsOcounter :: Int
         _lhsOcounter = rule2742 _lhsIcounter
         _lhsOkindErrors :: [Error]
         _lhsOkindErrors = rule2743 _lhsIkindErrors
         _lhsOlastStatementIsExpr :: Bool
         _lhsOlastStatementIsExpr = rule2744 _lhsIlastStatementIsExpr
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2745 _lhsImiscerrors
         _lhsOnamesInScope :: Names
         _lhsOnamesInScope = rule2746 _lhsInamesInScope
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2747 _lhsIwarnings
         __result_ = T_Statements_vOut157 _lhsOcollectInstances _lhsOcollectScopeInfos _lhsOcounter _lhsOkindErrors _lhsOlastStatementIsExpr _lhsOmiscerrors _lhsOnamesInScope _lhsOself _lhsOunboundNames _lhsOwarnings
         in __result_ )
     in C_Statements_s158 v157
   {-# INLINE rule2737 #-}
   rule2737 = \ ((_lhsIunboundNames) :: Names) ->
                                  _lhsIunboundNames
   {-# INLINE rule2738 #-}
   rule2738 = \  (_ :: ()) ->
     []
   {-# INLINE rule2739 #-}
   rule2739 = \  (_ :: ()) ->
     []
   {-# INLINE rule2740 #-}
   rule2740 = \ _self ->
     _self
   {-# INLINE rule2741 #-}
   rule2741 = \ ((_lhsIcollectScopeInfos) :: [(ScopeInfo, Entity)]) ->
     _lhsIcollectScopeInfos
   {-# INLINE rule2742 #-}
   rule2742 = \ ((_lhsIcounter) :: Int) ->
     _lhsIcounter
   {-# INLINE rule2743 #-}
   rule2743 = \ ((_lhsIkindErrors) :: [Error]) ->
     _lhsIkindErrors
   {-# INLINE rule2744 #-}
   rule2744 = \ ((_lhsIlastStatementIsExpr) :: Bool) ->
     _lhsIlastStatementIsExpr
   {-# INLINE rule2745 #-}
   rule2745 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2746 #-}
   rule2746 = \ ((_lhsInamesInScope) :: Names) ->
     _lhsInamesInScope
   {-# INLINE rule2747 #-}
   rule2747 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Strings -----------------------------------------------------
-- wrapper
data Inh_Strings  = Inh_Strings {  }
data Syn_Strings  = Syn_Strings { self_Syn_Strings :: (Strings) }
{-# INLINABLE wrap_Strings #-}
wrap_Strings :: T_Strings  -> Inh_Strings  -> (Syn_Strings )
wrap_Strings (T_Strings act) (Inh_Strings ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Strings_vIn160 
        (T_Strings_vOut160 _lhsOself) <- return (inv_Strings_s161 sem arg)
        return (Syn_Strings _lhsOself)
   )

-- cata
{-# NOINLINE sem_Strings #-}
sem_Strings :: Strings  -> T_Strings 
sem_Strings list = Prelude.foldr sem_Strings_Cons sem_Strings_Nil list

-- semantic domain
newtype T_Strings  = T_Strings {
                               attach_T_Strings :: Identity (T_Strings_s161 )
                               }
newtype T_Strings_s161  = C_Strings_s161 {
                                         inv_Strings_s161 :: (T_Strings_v160 )
                                         }
data T_Strings_s162  = C_Strings_s162
type T_Strings_v160  = (T_Strings_vIn160 ) -> (T_Strings_vOut160 )
data T_Strings_vIn160  = T_Strings_vIn160 
data T_Strings_vOut160  = T_Strings_vOut160 (Strings)
{-# NOINLINE sem_Strings_Cons #-}
sem_Strings_Cons :: (String) -> T_Strings  -> T_Strings 
sem_Strings_Cons arg_hd_ arg_tl_ = T_Strings (return st161) where
   {-# NOINLINE st161 #-}
   st161 = let
      v160 :: T_Strings_v160 
      v160 = \ (T_Strings_vIn160 ) -> ( let
         _tlX161 = Control.Monad.Identity.runIdentity (attach_T_Strings (arg_tl_))
         (T_Strings_vOut160 _tlIself) = inv_Strings_s161 _tlX161 (T_Strings_vIn160 )
         _self = rule2748 _tlIself arg_hd_
         _lhsOself :: Strings
         _lhsOself = rule2749 _self
         __result_ = T_Strings_vOut160 _lhsOself
         in __result_ )
     in C_Strings_s161 v160
   {-# INLINE rule2748 #-}
   rule2748 = \ ((_tlIself) :: Strings) hd_ ->
     (:) hd_ _tlIself
   {-# INLINE rule2749 #-}
   rule2749 = \ _self ->
     _self
{-# NOINLINE sem_Strings_Nil #-}
sem_Strings_Nil ::  T_Strings 
sem_Strings_Nil  = T_Strings (return st161) where
   {-# NOINLINE st161 #-}
   st161 = let
      v160 :: T_Strings_v160 
      v160 = \ (T_Strings_vIn160 ) -> ( let
         _self = rule2750  ()
         _lhsOself :: Strings
         _lhsOself = rule2751 _self
         __result_ = T_Strings_vOut160 _lhsOself
         in __result_ )
     in C_Strings_s161 v160
   {-# INLINE rule2750 #-}
   rule2750 = \  (_ :: ()) ->
     []
   {-# INLINE rule2751 #-}
   rule2751 = \ _self ->
     _self

-- Type --------------------------------------------------------
-- wrapper
data Inh_Type  = Inh_Type { allTypeConstructors_Inh_Type :: (Names), miscerrors_Inh_Type :: ([Error]), options_Inh_Type :: ([Option]), typeConstructors_Inh_Type :: (M.Map Name Int), warnings_Inh_Type :: ([Warning]) }
data Syn_Type  = Syn_Type { contextRange_Syn_Type :: (Range), miscerrors_Syn_Type :: ([Error]), self_Syn_Type :: (Type), typevariables_Syn_Type :: (Names), warnings_Syn_Type :: ([Warning]) }
{-# INLINABLE wrap_Type #-}
wrap_Type :: T_Type  -> Inh_Type  -> (Syn_Type )
wrap_Type (T_Type act) (Inh_Type _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Type_vIn163 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings
        (T_Type_vOut163 _lhsOcontextRange _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings) <- return (inv_Type_s164 sem arg)
        return (Syn_Type _lhsOcontextRange _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Type #-}
sem_Type :: Type  -> T_Type 
sem_Type ( Type_Application range_ prefix_ function_ arguments_ ) = sem_Type_Application ( sem_Range range_ ) prefix_ ( sem_Type function_ ) ( sem_Types arguments_ )
sem_Type ( Type_Variable range_ name_ ) = sem_Type_Variable ( sem_Range range_ ) ( sem_Name name_ )
sem_Type ( Type_Constructor range_ name_ ) = sem_Type_Constructor ( sem_Range range_ ) ( sem_Name name_ )
sem_Type ( Type_Qualified range_ context_ type_ ) = sem_Type_Qualified ( sem_Range range_ ) ( sem_ContextItems context_ ) ( sem_Type type_ )
sem_Type ( Type_Forall range_ typevariables_ type_ ) = sem_Type_Forall ( sem_Range range_ ) ( sem_Names typevariables_ ) ( sem_Type type_ )
sem_Type ( Type_Exists range_ typevariables_ type_ ) = sem_Type_Exists ( sem_Range range_ ) ( sem_Names typevariables_ ) ( sem_Type type_ )
sem_Type ( Type_Parenthesized range_ type_ ) = sem_Type_Parenthesized ( sem_Range range_ ) ( sem_Type type_ )

-- semantic domain
newtype T_Type  = T_Type {
                         attach_T_Type :: Identity (T_Type_s164 )
                         }
newtype T_Type_s164  = C_Type_s164 {
                                   inv_Type_s164 :: (T_Type_v163 )
                                   }
data T_Type_s165  = C_Type_s165
type T_Type_v163  = (T_Type_vIn163 ) -> (T_Type_vOut163 )
data T_Type_vIn163  = T_Type_vIn163 (Names) ([Error]) ([Option]) (M.Map Name Int) ([Warning])
data T_Type_vOut163  = T_Type_vOut163 (Range) ([Error]) (Type) (Names) ([Warning])
{-# NOINLINE sem_Type_Application #-}
sem_Type_Application :: T_Range  -> (Bool) -> T_Type  -> T_Types  -> T_Type 
sem_Type_Application arg_range_ arg_prefix_ arg_function_ arg_arguments_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _functionX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_function_))
         _argumentsX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_arguments_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Type_vOut163 _functionIcontextRange _functionImiscerrors _functionIself _functionItypevariables _functionIwarnings) = inv_Type_s164 _functionX164 (T_Type_vIn163 _functionOallTypeConstructors _functionOmiscerrors _functionOoptions _functionOtypeConstructors _functionOwarnings)
         (T_Types_vOut166 _argumentsImiscerrors _argumentsIself _argumentsItypevariables _argumentsIwarnings) = inv_Types_s167 _argumentsX167 (T_Types_vIn166 _argumentsOallTypeConstructors _argumentsOmiscerrors _argumentsOoptions _argumentsOtypeConstructors _argumentsOwarnings)
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule2752 _argumentsItypevariables _functionItypevariables
         _self = rule2753 _argumentsIself _functionIself _rangeIself arg_prefix_
         _lhsOself :: Type
         _lhsOself = rule2754 _self
         _lhsOcontextRange :: Range
         _lhsOcontextRange = rule2755 _functionIcontextRange
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2756 _argumentsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2757 _argumentsIwarnings
         _functionOallTypeConstructors = rule2758 _lhsIallTypeConstructors
         _functionOmiscerrors = rule2759 _lhsImiscerrors
         _functionOoptions = rule2760 _lhsIoptions
         _functionOtypeConstructors = rule2761 _lhsItypeConstructors
         _functionOwarnings = rule2762 _lhsIwarnings
         _argumentsOallTypeConstructors = rule2763 _lhsIallTypeConstructors
         _argumentsOmiscerrors = rule2764 _functionImiscerrors
         _argumentsOoptions = rule2765 _lhsIoptions
         _argumentsOtypeConstructors = rule2766 _lhsItypeConstructors
         _argumentsOwarnings = rule2767 _functionIwarnings
         __result_ = T_Type_vOut163 _lhsOcontextRange _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule2752 #-}
   rule2752 = \ ((_argumentsItypevariables) :: Names) ((_functionItypevariables) :: Names) ->
     _functionItypevariables  ++  _argumentsItypevariables
   {-# INLINE rule2753 #-}
   rule2753 = \ ((_argumentsIself) :: Types) ((_functionIself) :: Type) ((_rangeIself) :: Range) prefix_ ->
     Type_Application _rangeIself prefix_ _functionIself _argumentsIself
   {-# INLINE rule2754 #-}
   rule2754 = \ _self ->
     _self
   {-# INLINE rule2755 #-}
   rule2755 = \ ((_functionIcontextRange) :: Range) ->
     _functionIcontextRange
   {-# INLINE rule2756 #-}
   rule2756 = \ ((_argumentsImiscerrors) :: [Error]) ->
     _argumentsImiscerrors
   {-# INLINE rule2757 #-}
   rule2757 = \ ((_argumentsIwarnings) :: [Warning]) ->
     _argumentsIwarnings
   {-# INLINE rule2758 #-}
   rule2758 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2759 #-}
   rule2759 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2760 #-}
   rule2760 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2761 #-}
   rule2761 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2762 #-}
   rule2762 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2763 #-}
   rule2763 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2764 #-}
   rule2764 = \ ((_functionImiscerrors) :: [Error]) ->
     _functionImiscerrors
   {-# INLINE rule2765 #-}
   rule2765 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2766 #-}
   rule2766 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2767 #-}
   rule2767 = \ ((_functionIwarnings) :: [Warning]) ->
     _functionIwarnings
{-# NOINLINE sem_Type_Variable #-}
sem_Type_Variable :: T_Range  -> T_Name  -> T_Type 
sem_Type_Variable arg_range_ arg_name_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule2768 _nameIself
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2769 _lhsIallTypeConstructors _lhsIwarnings _nameIself
         _lhsOcontextRange :: Range
         _lhsOcontextRange = rule2770  ()
         _self = rule2771 _nameIself _rangeIself
         _lhsOself :: Type
         _lhsOself = rule2772 _self
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2773 _lhsImiscerrors
         __result_ = T_Type_vOut163 _lhsOcontextRange _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule2768 #-}
   rule2768 = \ ((_nameIself) :: Name) ->
                                      [ _nameIself ]
   {-# INLINE rule2769 #-}
   rule2769 = \ ((_lhsIallTypeConstructors) :: Names) ((_lhsIwarnings) :: [Warning]) ((_nameIself) :: Name) ->
                                  let xs = [ SuspiciousTypeVariable _nameIself tc
                                           | length (show _nameIself) > 1
                                           , tc <- _lhsIallTypeConstructors
                                           , capitalize (show _nameIself) == (show tc)
                                           ]
                                  in xs ++ _lhsIwarnings
   {-# INLINE rule2770 #-}
   rule2770 = \  (_ :: ()) ->
                                      noRange
   {-# INLINE rule2771 #-}
   rule2771 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Type_Variable _rangeIself _nameIself
   {-# INLINE rule2772 #-}
   rule2772 = \ _self ->
     _self
   {-# INLINE rule2773 #-}
   rule2773 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
{-# NOINLINE sem_Type_Constructor #-}
sem_Type_Constructor :: T_Range  -> T_Name  -> T_Type 
sem_Type_Constructor arg_range_ arg_name_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOcontextRange :: Range
         _lhsOcontextRange = rule2774  ()
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule2775  ()
         _self = rule2776 _nameIself _rangeIself
         _lhsOself :: Type
         _lhsOself = rule2777 _self
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2778 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2779 _lhsIwarnings
         __result_ = T_Type_vOut163 _lhsOcontextRange _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule2774 #-}
   rule2774 = \  (_ :: ()) ->
                                      noRange
   {-# INLINE rule2775 #-}
   rule2775 = \  (_ :: ()) ->
     []
   {-# INLINE rule2776 #-}
   rule2776 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Type_Constructor _rangeIself _nameIself
   {-# INLINE rule2777 #-}
   rule2777 = \ _self ->
     _self
   {-# INLINE rule2778 #-}
   rule2778 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2779 #-}
   rule2779 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Type_Qualified #-}
sem_Type_Qualified :: T_Range  -> T_ContextItems  -> T_Type  -> T_Type 
sem_Type_Qualified arg_range_ arg_context_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextIcontextRanges _contextIcontextVars _contextImiscerrors _contextIself _contextIwarnings) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 _contextOallTypeConstructors _contextOmiscerrors _contextOoptions _contextOtypeConstructors _contextOwarnings)
         (T_Type_vOut163 _typeIcontextRange _typeImiscerrors _typeIself _typeItypevariables _typeIwarnings) = inv_Type_s164 _typeX164 (T_Type_vIn163 _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings)
         _lhsOcontextRange :: Range
         _lhsOcontextRange = rule2780 _contextIcontextRanges
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2781 _contextIcontextVars _lhsIoptions _rangeIself _typeImiscerrors _typeItypevariables
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule2782 _typeItypevariables
         _self = rule2783 _contextIself _rangeIself _typeIself
         _lhsOself :: Type
         _lhsOself = rule2784 _self
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2785 _typeIwarnings
         _contextOallTypeConstructors = rule2786 _lhsIallTypeConstructors
         _contextOmiscerrors = rule2787 _lhsImiscerrors
         _contextOoptions = rule2788 _lhsIoptions
         _contextOtypeConstructors = rule2789 _lhsItypeConstructors
         _contextOwarnings = rule2790 _lhsIwarnings
         _typeOallTypeConstructors = rule2791 _lhsIallTypeConstructors
         _typeOmiscerrors = rule2792 _contextImiscerrors
         _typeOoptions = rule2793 _lhsIoptions
         _typeOtypeConstructors = rule2794 _lhsItypeConstructors
         _typeOwarnings = rule2795 _contextIwarnings
         __result_ = T_Type_vOut163 _lhsOcontextRange _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule2780 #-}
   rule2780 = \ ((_contextIcontextRanges) :: [Range]) ->
                                      if null _contextIcontextRanges
                                        then noRange
                                        else foldr1 mergeRanges _contextIcontextRanges
   {-# INLINE rule2781 #-}
   rule2781 = \ ((_contextIcontextVars) :: [Name]) ((_lhsIoptions) :: [Option]) ((_rangeIself) :: Range) ((_typeImiscerrors) :: [Error]) ((_typeItypevariables) :: Names) ->
          ( if Overloading `elem` _lhsIoptions then
              [ AmbiguousContext v | v <-  _contextIcontextVars, v `notElem` _typeItypevariables ]
            else
              [ OverloadingDisabled _rangeIself ]
          )
          ++
          _typeImiscerrors
   {-# INLINE rule2782 #-}
   rule2782 = \ ((_typeItypevariables) :: Names) ->
     _typeItypevariables
   {-# INLINE rule2783 #-}
   rule2783 = \ ((_contextIself) :: ContextItems) ((_rangeIself) :: Range) ((_typeIself) :: Type) ->
     Type_Qualified _rangeIself _contextIself _typeIself
   {-# INLINE rule2784 #-}
   rule2784 = \ _self ->
     _self
   {-# INLINE rule2785 #-}
   rule2785 = \ ((_typeIwarnings) :: [Warning]) ->
     _typeIwarnings
   {-# INLINE rule2786 #-}
   rule2786 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2787 #-}
   rule2787 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2788 #-}
   rule2788 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2789 #-}
   rule2789 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2790 #-}
   rule2790 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2791 #-}
   rule2791 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2792 #-}
   rule2792 = \ ((_contextImiscerrors) :: [Error]) ->
     _contextImiscerrors
   {-# INLINE rule2793 #-}
   rule2793 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2794 #-}
   rule2794 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2795 #-}
   rule2795 = \ ((_contextIwarnings) :: [Warning]) ->
     _contextIwarnings
{-# NOINLINE sem_Type_Forall #-}
sem_Type_Forall :: T_Range  -> T_Names  -> T_Type  -> T_Type 
sem_Type_Forall arg_range_ arg_typevariables_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typevariablesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_typevariables_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _typevariablesIself) = inv_Names_s116 _typevariablesX116 (T_Names_vIn115 )
         (T_Type_vOut163 _typeIcontextRange _typeImiscerrors _typeIself _typeItypevariables _typeIwarnings) = inv_Type_s164 _typeX164 (T_Type_vIn163 _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings)
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule2796 _typeItypevariables
         _self = rule2797 _rangeIself _typeIself _typevariablesIself
         _lhsOself :: Type
         _lhsOself = rule2798 _self
         _lhsOcontextRange :: Range
         _lhsOcontextRange = rule2799 _typeIcontextRange
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2800 _typeImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2801 _typeIwarnings
         _typeOallTypeConstructors = rule2802 _lhsIallTypeConstructors
         _typeOmiscerrors = rule2803 _lhsImiscerrors
         _typeOoptions = rule2804 _lhsIoptions
         _typeOtypeConstructors = rule2805 _lhsItypeConstructors
         _typeOwarnings = rule2806 _lhsIwarnings
         __result_ = T_Type_vOut163 _lhsOcontextRange _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule2796 #-}
   rule2796 = \ ((_typeItypevariables) :: Names) ->
     _typeItypevariables
   {-# INLINE rule2797 #-}
   rule2797 = \ ((_rangeIself) :: Range) ((_typeIself) :: Type) ((_typevariablesIself) :: Names) ->
     Type_Forall _rangeIself _typevariablesIself _typeIself
   {-# INLINE rule2798 #-}
   rule2798 = \ _self ->
     _self
   {-# INLINE rule2799 #-}
   rule2799 = \ ((_typeIcontextRange) :: Range) ->
     _typeIcontextRange
   {-# INLINE rule2800 #-}
   rule2800 = \ ((_typeImiscerrors) :: [Error]) ->
     _typeImiscerrors
   {-# INLINE rule2801 #-}
   rule2801 = \ ((_typeIwarnings) :: [Warning]) ->
     _typeIwarnings
   {-# INLINE rule2802 #-}
   rule2802 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2803 #-}
   rule2803 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2804 #-}
   rule2804 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2805 #-}
   rule2805 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2806 #-}
   rule2806 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Type_Exists #-}
sem_Type_Exists :: T_Range  -> T_Names  -> T_Type  -> T_Type 
sem_Type_Exists arg_range_ arg_typevariables_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typevariablesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_typevariables_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _typevariablesIself) = inv_Names_s116 _typevariablesX116 (T_Names_vIn115 )
         (T_Type_vOut163 _typeIcontextRange _typeImiscerrors _typeIself _typeItypevariables _typeIwarnings) = inv_Type_s164 _typeX164 (T_Type_vIn163 _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings)
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule2807 _typeItypevariables
         _self = rule2808 _rangeIself _typeIself _typevariablesIself
         _lhsOself :: Type
         _lhsOself = rule2809 _self
         _lhsOcontextRange :: Range
         _lhsOcontextRange = rule2810 _typeIcontextRange
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2811 _typeImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2812 _typeIwarnings
         _typeOallTypeConstructors = rule2813 _lhsIallTypeConstructors
         _typeOmiscerrors = rule2814 _lhsImiscerrors
         _typeOoptions = rule2815 _lhsIoptions
         _typeOtypeConstructors = rule2816 _lhsItypeConstructors
         _typeOwarnings = rule2817 _lhsIwarnings
         __result_ = T_Type_vOut163 _lhsOcontextRange _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule2807 #-}
   rule2807 = \ ((_typeItypevariables) :: Names) ->
     _typeItypevariables
   {-# INLINE rule2808 #-}
   rule2808 = \ ((_rangeIself) :: Range) ((_typeIself) :: Type) ((_typevariablesIself) :: Names) ->
     Type_Exists _rangeIself _typevariablesIself _typeIself
   {-# INLINE rule2809 #-}
   rule2809 = \ _self ->
     _self
   {-# INLINE rule2810 #-}
   rule2810 = \ ((_typeIcontextRange) :: Range) ->
     _typeIcontextRange
   {-# INLINE rule2811 #-}
   rule2811 = \ ((_typeImiscerrors) :: [Error]) ->
     _typeImiscerrors
   {-# INLINE rule2812 #-}
   rule2812 = \ ((_typeIwarnings) :: [Warning]) ->
     _typeIwarnings
   {-# INLINE rule2813 #-}
   rule2813 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2814 #-}
   rule2814 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2815 #-}
   rule2815 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2816 #-}
   rule2816 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2817 #-}
   rule2817 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
{-# NOINLINE sem_Type_Parenthesized #-}
sem_Type_Parenthesized :: T_Range  -> T_Type  -> T_Type 
sem_Type_Parenthesized arg_range_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Type_vOut163 _typeIcontextRange _typeImiscerrors _typeIself _typeItypevariables _typeIwarnings) = inv_Type_s164 _typeX164 (T_Type_vIn163 _typeOallTypeConstructors _typeOmiscerrors _typeOoptions _typeOtypeConstructors _typeOwarnings)
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule2818 _typeItypevariables
         _self = rule2819 _rangeIself _typeIself
         _lhsOself :: Type
         _lhsOself = rule2820 _self
         _lhsOcontextRange :: Range
         _lhsOcontextRange = rule2821 _typeIcontextRange
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2822 _typeImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2823 _typeIwarnings
         _typeOallTypeConstructors = rule2824 _lhsIallTypeConstructors
         _typeOmiscerrors = rule2825 _lhsImiscerrors
         _typeOoptions = rule2826 _lhsIoptions
         _typeOtypeConstructors = rule2827 _lhsItypeConstructors
         _typeOwarnings = rule2828 _lhsIwarnings
         __result_ = T_Type_vOut163 _lhsOcontextRange _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule2818 #-}
   rule2818 = \ ((_typeItypevariables) :: Names) ->
     _typeItypevariables
   {-# INLINE rule2819 #-}
   rule2819 = \ ((_rangeIself) :: Range) ((_typeIself) :: Type) ->
     Type_Parenthesized _rangeIself _typeIself
   {-# INLINE rule2820 #-}
   rule2820 = \ _self ->
     _self
   {-# INLINE rule2821 #-}
   rule2821 = \ ((_typeIcontextRange) :: Range) ->
     _typeIcontextRange
   {-# INLINE rule2822 #-}
   rule2822 = \ ((_typeImiscerrors) :: [Error]) ->
     _typeImiscerrors
   {-# INLINE rule2823 #-}
   rule2823 = \ ((_typeIwarnings) :: [Warning]) ->
     _typeIwarnings
   {-# INLINE rule2824 #-}
   rule2824 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2825 #-}
   rule2825 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2826 #-}
   rule2826 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2827 #-}
   rule2827 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2828 #-}
   rule2828 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings

-- Types -------------------------------------------------------
-- wrapper
data Inh_Types  = Inh_Types { allTypeConstructors_Inh_Types :: (Names), miscerrors_Inh_Types :: ([Error]), options_Inh_Types :: ([Option]), typeConstructors_Inh_Types :: (M.Map Name Int), warnings_Inh_Types :: ([Warning]) }
data Syn_Types  = Syn_Types { miscerrors_Syn_Types :: ([Error]), self_Syn_Types :: (Types), typevariables_Syn_Types :: (Names), warnings_Syn_Types :: ([Warning]) }
{-# INLINABLE wrap_Types #-}
wrap_Types :: T_Types  -> Inh_Types  -> (Syn_Types )
wrap_Types (T_Types act) (Inh_Types _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Types_vIn166 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings
        (T_Types_vOut166 _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings) <- return (inv_Types_s167 sem arg)
        return (Syn_Types _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings)
   )

-- cata
{-# NOINLINE sem_Types #-}
sem_Types :: Types  -> T_Types 
sem_Types list = Prelude.foldr sem_Types_Cons sem_Types_Nil (Prelude.map sem_Type list)

-- semantic domain
newtype T_Types  = T_Types {
                           attach_T_Types :: Identity (T_Types_s167 )
                           }
newtype T_Types_s167  = C_Types_s167 {
                                     inv_Types_s167 :: (T_Types_v166 )
                                     }
data T_Types_s168  = C_Types_s168
type T_Types_v166  = (T_Types_vIn166 ) -> (T_Types_vOut166 )
data T_Types_vIn166  = T_Types_vIn166 (Names) ([Error]) ([Option]) (M.Map Name Int) ([Warning])
data T_Types_vOut166  = T_Types_vOut166 ([Error]) (Types) (Names) ([Warning])
{-# NOINLINE sem_Types_Cons #-}
sem_Types_Cons :: T_Type  -> T_Types  -> T_Types 
sem_Types_Cons arg_hd_ arg_tl_ = T_Types (return st167) where
   {-# NOINLINE st167 #-}
   st167 = let
      v166 :: T_Types_v166 
      v166 = \ (T_Types_vIn166 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _hdX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_hd_))
         _tlX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_tl_))
         (T_Type_vOut163 _hdIcontextRange _hdImiscerrors _hdIself _hdItypevariables _hdIwarnings) = inv_Type_s164 _hdX164 (T_Type_vIn163 _hdOallTypeConstructors _hdOmiscerrors _hdOoptions _hdOtypeConstructors _hdOwarnings)
         (T_Types_vOut166 _tlImiscerrors _tlIself _tlItypevariables _tlIwarnings) = inv_Types_s167 _tlX167 (T_Types_vIn166 _tlOallTypeConstructors _tlOmiscerrors _tlOoptions _tlOtypeConstructors _tlOwarnings)
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule2829 _hdItypevariables _tlItypevariables
         _self = rule2830 _hdIself _tlIself
         _lhsOself :: Types
         _lhsOself = rule2831 _self
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2832 _tlImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2833 _tlIwarnings
         _hdOallTypeConstructors = rule2834 _lhsIallTypeConstructors
         _hdOmiscerrors = rule2835 _lhsImiscerrors
         _hdOoptions = rule2836 _lhsIoptions
         _hdOtypeConstructors = rule2837 _lhsItypeConstructors
         _hdOwarnings = rule2838 _lhsIwarnings
         _tlOallTypeConstructors = rule2839 _lhsIallTypeConstructors
         _tlOmiscerrors = rule2840 _hdImiscerrors
         _tlOoptions = rule2841 _lhsIoptions
         _tlOtypeConstructors = rule2842 _lhsItypeConstructors
         _tlOwarnings = rule2843 _hdIwarnings
         __result_ = T_Types_vOut166 _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings
         in __result_ )
     in C_Types_s167 v166
   {-# INLINE rule2829 #-}
   rule2829 = \ ((_hdItypevariables) :: Names) ((_tlItypevariables) :: Names) ->
     _hdItypevariables  ++  _tlItypevariables
   {-# INLINE rule2830 #-}
   rule2830 = \ ((_hdIself) :: Type) ((_tlIself) :: Types) ->
     (:) _hdIself _tlIself
   {-# INLINE rule2831 #-}
   rule2831 = \ _self ->
     _self
   {-# INLINE rule2832 #-}
   rule2832 = \ ((_tlImiscerrors) :: [Error]) ->
     _tlImiscerrors
   {-# INLINE rule2833 #-}
   rule2833 = \ ((_tlIwarnings) :: [Warning]) ->
     _tlIwarnings
   {-# INLINE rule2834 #-}
   rule2834 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2835 #-}
   rule2835 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2836 #-}
   rule2836 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2837 #-}
   rule2837 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2838 #-}
   rule2838 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
   {-# INLINE rule2839 #-}
   rule2839 = \ ((_lhsIallTypeConstructors) :: Names) ->
     _lhsIallTypeConstructors
   {-# INLINE rule2840 #-}
   rule2840 = \ ((_hdImiscerrors) :: [Error]) ->
     _hdImiscerrors
   {-# INLINE rule2841 #-}
   rule2841 = \ ((_lhsIoptions) :: [Option]) ->
     _lhsIoptions
   {-# INLINE rule2842 #-}
   rule2842 = \ ((_lhsItypeConstructors) :: M.Map Name Int) ->
     _lhsItypeConstructors
   {-# INLINE rule2843 #-}
   rule2843 = \ ((_hdIwarnings) :: [Warning]) ->
     _hdIwarnings
{-# NOINLINE sem_Types_Nil #-}
sem_Types_Nil ::  T_Types 
sem_Types_Nil  = T_Types (return st167) where
   {-# NOINLINE st167 #-}
   st167 = let
      v166 :: T_Types_v166 
      v166 = \ (T_Types_vIn166 _lhsIallTypeConstructors _lhsImiscerrors _lhsIoptions _lhsItypeConstructors _lhsIwarnings) -> ( let
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule2844  ()
         _self = rule2845  ()
         _lhsOself :: Types
         _lhsOself = rule2846 _self
         _lhsOmiscerrors :: [Error]
         _lhsOmiscerrors = rule2847 _lhsImiscerrors
         _lhsOwarnings :: [Warning]
         _lhsOwarnings = rule2848 _lhsIwarnings
         __result_ = T_Types_vOut166 _lhsOmiscerrors _lhsOself _lhsOtypevariables _lhsOwarnings
         in __result_ )
     in C_Types_s167 v166
   {-# INLINE rule2844 #-}
   rule2844 = \  (_ :: ()) ->
     []
   {-# INLINE rule2845 #-}
   rule2845 = \  (_ :: ()) ->
     []
   {-# INLINE rule2846 #-}
   rule2846 = \ _self ->
     _self
   {-# INLINE rule2847 #-}
   rule2847 = \ ((_lhsImiscerrors) :: [Error]) ->
     _lhsImiscerrors
   {-# INLINE rule2848 #-}
   rule2848 = \ ((_lhsIwarnings) :: [Warning]) ->
     _lhsIwarnings
