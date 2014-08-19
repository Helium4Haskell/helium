{-# LANGUAGE Rank2Types, GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}

module CodeGeneration.CodeGeneration where

import Syntax.UHA_Syntax
import Syntax.UHA_Utils
import Syntax.UHA_Range 
import ModuleSystem.ImportEnvironment
import ModuleSystem.DictionaryEnvironment
import qualified Data.Map as M
import StaticAnalysis.Miscellaneous.TypeConversion
import Data.Char (ord)


import Lvm.Common.Id
import Lvm.Common.IdSet 
import Utils.Utils(internalError)

import Top.Types

import CodeGeneration.PatternMatch
import qualified CodeGeneration.DerivingShow as DerivingShow
import qualified CodeGeneration.DerivingEq as DerivingEq

-- Semi-Daan
import CodeGeneration.CoreUtils

-- Daan
import qualified Lvm.Core.Expr as Core
import qualified Lvm.Core.Module as Core
import qualified Lvm.Core.Module as Module
import qualified Lvm.Common.Byte as Byte


import Lvm.Common.Byte(bytesFromString)
import Control.Monad.Identity (Identity)
import qualified Control.Monad.Identity


type CoreDecl = Core.Decl Core.Expr


makeCoreModule :: Maybe Id -> [Module.Decl v] -> Module.Module v
makeCoreModule name decls =
    Module.Module
        { Module.moduleName   =
            case name of
                Nothing -> idFromString "Main"
                Just n -> n
        , Module.moduleMajorVer = 0
        , Module.moduleMinorVer = 0
        , Module.moduleDecls    = decls
        }

interpreterMain :: String
interpreterMain = "interpreter_main"

-- Unfortunately we need a hack for the interpreter
-- The interpreter_main has te be wrapped inside unsafePerformIO etcetera, too
-- We can't just call it main because we'll get import clashes.  Sigh!

insertedMain :: TypeEnvironment -> CoreDecl
insertedMain toplevelTypes =
    let maybeWrapMainAndType = 
            case M.lookup (Name_Identifier noRange [] "main") toplevelTypes of -- !!!Name
                Just t -> Just ("main", t)
                Nothing ->
                    case M.lookup (Name_Identifier noRange [] interpreterMain) toplevelTypes of -- !!!Name
                        Just t -> Just (interpreterMain, t)
                        Nothing -> Nothing
    in
    decl False "main$" $
        app_ unsafePIO $
            case maybeWrapMainAndType of 
                Nothing -> 
                    var "$primPutStrLn" `app_` 
                        (var "$primPackedToString" `app_`
                            packedString "No 'main' function defined in this module")
                Just (name, tpScheme)
                    | not (null qs) ->
                        var "$primPutStrLn" `app_` 
                            (var "$primPackedToString" `app_`
                                packedString "<<overloaded function>>")
                    | isIOType tp -> 
                        var name
                    | otherwise ->
                        var "$primPutStrLn" `app_` 
                            (DerivingShow.showFunctionOfType True (makeTypeFromTp tp) `app_` 
                                var name)
                    where                        
                        (qs, tp) = split (snd (instantiate 123456789 tpScheme))
    where
        unsafePIO = var "$primUnsafePerformIO"    
                


-- set the public bit of all declarations except those that are imported from
-- Prelude or HeliumLang. I.e. export everything everywhere
everythingPublicButPrelude :: Core.CoreModule -> Core.CoreModule
everythingPublicButPrelude theModule = theModule { Core.moduleDecls = map setPublic (Core.moduleDecls theModule) }
  where
    setPublic declaration = 
        let -- accessRecord = Core.declAccess decl
            public = case Core.declAccess declaration of 
                    Core.Defined _ -> True
                    Core.Imported { Core.importModule = m } -> 
                        stringFromId m `notElem` ["Prelude", "HeliumLang"] 
        in 
        declaration{ Core.declAccess = 
                  (Core.declAccess declaration){ Core.accessPublic = public } }


predicateToId :: Predicate -> Id
predicateToId (Predicate class_ tp) =
    idFromString $ "$dict" ++ class_ ++ show tp
    
dictionaryTreeToCore :: DictionaryTree -> Core.Expr
dictionaryTreeToCore theTree = 
   case theTree of
      ByPredicate predicate -> 
         Core.Var (predicateToId predicate)
      ByInstance className instanceName trees ->
         foldl Core.Ap
               (Core.Var (idFromString ("$dict"++className++instanceName)))
               (map dictionaryTreeToCore trees)
      BySuperClass subClass superClass tree -> 
         Core.Ap (Core.Var (idFromString ("$get" ++ superClass ++ "From" ++ subClass)))          
                 (dictionaryTreeToCore tree)

insertDictionaries :: Name -> DictionaryEnvironment -> Core.Expr
insertDictionaries name dictionaryEnv = 
   foldl Core.Ap
         (Core.Var (idFromName name))
         (map dictionaryTreeToCore (getDictionaryTrees name dictionaryEnv))


toplevelType :: Name -> ImportEnvironment -> Bool -> [Core.Custom]
toplevelType name ie isTopLevel
    | isTopLevel = [custom "type" typeString]
    | otherwise  = []
    where
        typeString = maybe
            (internalError "ToCoreDecl" "Declaration" ("no type found for " ++ getNameName name))
            show
            (M.lookup name (typeEnvironment ie))

constructorCustoms :: Name -> Name -> ValueConstructorEnvironment -> [Core.Custom]
constructorCustoms dataTypeName name env =
    maybe 
        (internalError "ToCoreDecl" "Constructor" ("no type found for " ++ show name))
        (\tpScheme -> 
            [ custom "type" (show tpScheme)
            , Core.CustomLink 
                    (idFromName dataTypeName) 
                    (Core.DeclKindCustom (idFromString "data"))
            ]
        )
        (M.lookup name env)



-- Function "bind" is used in the translation of do-expressions
bind :: Core.Expr -> Core.Expr -> Core.Expr
bind ma f = Core.Var primBindIOId `app_` ma `app_` f

primBindIOId, caseExprId, okId, parameterId :: Id
( primBindIOId :  caseExprId :  okId :  parameterId : []) = map idFromString $
 "$primBindIO"  : "caseExpr$" : "ok$" : "parameter$" : []

-- Function "chainCode" is used in the translation of do-expressions
chainCode :: [Maybe Core.Expr -> Core.Expr] -> Core.Expr
chainCode theCores =
    case theCores of
        [core] -> core Nothing
        (core:cores) -> core (Just (chainCode cores))
        [] -> error "pattern match failure in CodeGeneration.ToCoreExpr.chainCode"



patternAlwaysSucceeds :: Pattern -> Bool
patternAlwaysSucceeds p = 
    case p of
        Pattern_Variable _ _ -> True
        Pattern_Wildcard _ -> True
        Pattern_As _ _ pat -> patternAlwaysSucceeds pat
        Pattern_Parenthesized _ pat -> patternAlwaysSucceeds pat
        _ -> False

patternMatchFail :: String -> Range -> Core.Expr
patternMatchFail nodeDescription range =
    var "$primPatternFailPacked"
        `app_` packedString (
                    nodeDescription ++ " ranging from " ++ 
                    showPosition start ++ " to " ++ 
                    showPosition (getRangeEnd range) ++ " in module " ++
                    moduleFromPosition start
               )
    where
        start = getRangeStart range
-- Alternative -------------------------------------------------
-- wrapper
data Inh_Alternative  = Inh_Alternative { dictionaryEnv_Inh_Alternative :: (DictionaryEnvironment) }
data Syn_Alternative  = Syn_Alternative { core_Syn_Alternative :: ( Core.Expr -> Core.Expr ), self_Syn_Alternative :: (Alternative) }
{-# INLINABLE wrap_Alternative #-}
wrap_Alternative :: T_Alternative  -> Inh_Alternative  -> (Syn_Alternative )
wrap_Alternative (T_Alternative act) (Inh_Alternative _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Alternative_vIn1 _lhsIdictionaryEnv
        (T_Alternative_vOut1 _lhsOcore _lhsOself) <- return (inv_Alternative_s2 sem arg)
        return (Syn_Alternative _lhsOcore _lhsOself)
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
data T_Alternative_vIn1  = T_Alternative_vIn1 (DictionaryEnvironment)
data T_Alternative_vOut1  = T_Alternative_vOut1 ( Core.Expr -> Core.Expr ) (Alternative)
{-# NOINLINE sem_Alternative_Hole #-}
sem_Alternative_Hole :: T_Range  -> (Integer) -> T_Alternative 
sem_Alternative_Hole arg_range_ arg_id_ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule0  ()
         _self = rule1 _rangeIself arg_id_
         _lhsOself :: Alternative
         _lhsOself = rule2 _self
         __result_ = T_Alternative_vOut1 _lhsOcore _lhsOself
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule0 #-}
   rule0 = \  (_ :: ()) ->
                                       id
   {-# INLINE rule1 #-}
   rule1 = \ ((_rangeIself) :: Range) id_ ->
     Alternative_Hole _rangeIself id_
   {-# INLINE rule2 #-}
   rule2 = \ _self ->
     _self
{-# NOINLINE sem_Alternative_Feedback #-}
sem_Alternative_Feedback :: T_Range  -> (String) -> T_Alternative  -> T_Alternative 
sem_Alternative_Feedback arg_range_ arg_feedback_ arg_alternative_ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _alternativeX2 = Control.Monad.Identity.runIdentity (attach_T_Alternative (arg_alternative_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Alternative_vOut1 _alternativeIcore _alternativeIself) = inv_Alternative_s2 _alternativeX2 (T_Alternative_vIn1 _alternativeOdictionaryEnv)
         _self = rule3 _alternativeIself _rangeIself arg_feedback_
         _lhsOself :: Alternative
         _lhsOself = rule4 _self
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule5 _alternativeIcore
         _alternativeOdictionaryEnv = rule6 _lhsIdictionaryEnv
         __result_ = T_Alternative_vOut1 _lhsOcore _lhsOself
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule3 #-}
   rule3 = \ ((_alternativeIself) :: Alternative) ((_rangeIself) :: Range) feedback_ ->
     Alternative_Feedback _rangeIself feedback_ _alternativeIself
   {-# INLINE rule4 #-}
   rule4 = \ _self ->
     _self
   {-# INLINE rule5 #-}
   rule5 = \ ((_alternativeIcore) ::  Core.Expr -> Core.Expr ) ->
     _alternativeIcore
   {-# INLINE rule6 #-}
   rule6 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Alternative_Alternative #-}
sem_Alternative_Alternative :: T_Range  -> T_Pattern  -> T_RightHandSide  -> T_Alternative 
sem_Alternative_Alternative arg_range_ arg_pattern_ arg_righthandside_ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _righthandsideX149 = Control.Monad.Identity.runIdentity (attach_T_RightHandSide (arg_righthandside_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIself _patternIvars) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         (T_RightHandSide_vOut148 _righthandsideIcore _righthandsideIisGuarded _righthandsideIself) = inv_RightHandSide_s149 _righthandsideX149 (T_RightHandSide_vIn148 _righthandsideOdictionaryEnv)
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule7 _patternIself _righthandsideIcore
         _self = rule8 _patternIself _rangeIself _righthandsideIself
         _lhsOself :: Alternative
         _lhsOself = rule9 _self
         _righthandsideOdictionaryEnv = rule10 _lhsIdictionaryEnv
         __result_ = T_Alternative_vOut1 _lhsOcore _lhsOself
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule7 #-}
   rule7 = \ ((_patternIself) :: Pattern) ((_righthandsideIcore) ::  Core.Expr ) ->
                                       \nextCase  ->
                                          let thisCase =
                                                  patternToCore
                                                      (caseExprId, _patternIself)
                                                      _righthandsideIcore
                                          in
                                              let_ nextClauseId nextCase thisCase
   {-# INLINE rule8 #-}
   rule8 = \ ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ((_righthandsideIself) :: RightHandSide) ->
     Alternative_Alternative _rangeIself _patternIself _righthandsideIself
   {-# INLINE rule9 #-}
   rule9 = \ _self ->
     _self
   {-# INLINE rule10 #-}
   rule10 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Alternative_Empty #-}
sem_Alternative_Empty :: T_Range  -> T_Alternative 
sem_Alternative_Empty arg_range_ = T_Alternative (return st2) where
   {-# NOINLINE st2 #-}
   st2 = let
      v1 :: T_Alternative_v1 
      v1 = \ (T_Alternative_vIn1 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule11  ()
         _self = rule12 _rangeIself
         _lhsOself :: Alternative
         _lhsOself = rule13 _self
         __result_ = T_Alternative_vOut1 _lhsOcore _lhsOself
         in __result_ )
     in C_Alternative_s2 v1
   {-# INLINE rule11 #-}
   rule11 = \  (_ :: ()) ->
                                       id
   {-# INLINE rule12 #-}
   rule12 = \ ((_rangeIself) :: Range) ->
     Alternative_Empty _rangeIself
   {-# INLINE rule13 #-}
   rule13 = \ _self ->
     _self

-- Alternatives ------------------------------------------------
-- wrapper
data Inh_Alternatives  = Inh_Alternatives { caseRange_Inh_Alternatives :: (Range), dictionaryEnv_Inh_Alternatives :: (DictionaryEnvironment) }
data Syn_Alternatives  = Syn_Alternatives { core_Syn_Alternatives :: ( Core.Expr ), self_Syn_Alternatives :: (Alternatives) }
{-# INLINABLE wrap_Alternatives #-}
wrap_Alternatives :: T_Alternatives  -> Inh_Alternatives  -> (Syn_Alternatives )
wrap_Alternatives (T_Alternatives act) (Inh_Alternatives _lhsIcaseRange _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Alternatives_vIn4 _lhsIcaseRange _lhsIdictionaryEnv
        (T_Alternatives_vOut4 _lhsOcore _lhsOself) <- return (inv_Alternatives_s5 sem arg)
        return (Syn_Alternatives _lhsOcore _lhsOself)
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
data T_Alternatives_vIn4  = T_Alternatives_vIn4 (Range) (DictionaryEnvironment)
data T_Alternatives_vOut4  = T_Alternatives_vOut4 ( Core.Expr ) (Alternatives)
{-# NOINLINE sem_Alternatives_Cons #-}
sem_Alternatives_Cons :: T_Alternative  -> T_Alternatives  -> T_Alternatives 
sem_Alternatives_Cons arg_hd_ arg_tl_ = T_Alternatives (return st5) where
   {-# NOINLINE st5 #-}
   st5 = let
      v4 :: T_Alternatives_v4 
      v4 = \ (T_Alternatives_vIn4 _lhsIcaseRange _lhsIdictionaryEnv) -> ( let
         _hdX2 = Control.Monad.Identity.runIdentity (attach_T_Alternative (arg_hd_))
         _tlX5 = Control.Monad.Identity.runIdentity (attach_T_Alternatives (arg_tl_))
         (T_Alternative_vOut1 _hdIcore _hdIself) = inv_Alternative_s2 _hdX2 (T_Alternative_vIn1 _hdOdictionaryEnv)
         (T_Alternatives_vOut4 _tlIcore _tlIself) = inv_Alternatives_s5 _tlX5 (T_Alternatives_vIn4 _tlOcaseRange _tlOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule14 _hdIcore _tlIcore
         _self = rule15 _hdIself _tlIself
         _lhsOself :: Alternatives
         _lhsOself = rule16 _self
         _hdOdictionaryEnv = rule17 _lhsIdictionaryEnv
         _tlOcaseRange = rule18 _lhsIcaseRange
         _tlOdictionaryEnv = rule19 _lhsIdictionaryEnv
         __result_ = T_Alternatives_vOut4 _lhsOcore _lhsOself
         in __result_ )
     in C_Alternatives_s5 v4
   {-# INLINE rule14 #-}
   rule14 = \ ((_hdIcore) ::  Core.Expr -> Core.Expr ) ((_tlIcore) ::  Core.Expr ) ->
                                         _hdIcore _tlIcore
   {-# INLINE rule15 #-}
   rule15 = \ ((_hdIself) :: Alternative) ((_tlIself) :: Alternatives) ->
     (:) _hdIself _tlIself
   {-# INLINE rule16 #-}
   rule16 = \ _self ->
     _self
   {-# INLINE rule17 #-}
   rule17 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule18 #-}
   rule18 = \ ((_lhsIcaseRange) :: Range) ->
     _lhsIcaseRange
   {-# INLINE rule19 #-}
   rule19 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Alternatives_Nil #-}
sem_Alternatives_Nil ::  T_Alternatives 
sem_Alternatives_Nil  = T_Alternatives (return st5) where
   {-# NOINLINE st5 #-}
   st5 = let
      v4 :: T_Alternatives_v4 
      v4 = \ (T_Alternatives_vIn4 _lhsIcaseRange _lhsIdictionaryEnv) -> ( let
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule20 _lhsIcaseRange
         _self = rule21  ()
         _lhsOself :: Alternatives
         _lhsOself = rule22 _self
         __result_ = T_Alternatives_vOut4 _lhsOcore _lhsOself
         in __result_ )
     in C_Alternatives_s5 v4
   {-# INLINE rule20 #-}
   rule20 = \ ((_lhsIcaseRange) :: Range) ->
                                         patternMatchFail "case expression" _lhsIcaseRange
   {-# INLINE rule21 #-}
   rule21 = \  (_ :: ()) ->
     []
   {-# INLINE rule22 #-}
   rule22 = \ _self ->
     _self

-- AnnotatedType -----------------------------------------------
-- wrapper
data Inh_AnnotatedType  = Inh_AnnotatedType {  }
data Syn_AnnotatedType  = Syn_AnnotatedType { self_Syn_AnnotatedType :: (AnnotatedType) }
{-# INLINABLE wrap_AnnotatedType #-}
wrap_AnnotatedType :: T_AnnotatedType  -> Inh_AnnotatedType  -> (Syn_AnnotatedType )
wrap_AnnotatedType (T_AnnotatedType act) (Inh_AnnotatedType ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_AnnotatedType_vIn7 
        (T_AnnotatedType_vOut7 _lhsOself) <- return (inv_AnnotatedType_s8 sem arg)
        return (Syn_AnnotatedType _lhsOself)
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
data T_AnnotatedType_vIn7  = T_AnnotatedType_vIn7 
data T_AnnotatedType_vOut7  = T_AnnotatedType_vOut7 (AnnotatedType)
{-# NOINLINE sem_AnnotatedType_AnnotatedType #-}
sem_AnnotatedType_AnnotatedType :: T_Range  -> (Bool) -> T_Type  -> T_AnnotatedType 
sem_AnnotatedType_AnnotatedType arg_range_ arg_strict_ arg_type_ = T_AnnotatedType (return st8) where
   {-# NOINLINE st8 #-}
   st8 = let
      v7 :: T_AnnotatedType_v7 
      v7 = \ (T_AnnotatedType_vIn7 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Type_vOut163 _typeIself) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _self = rule23 _rangeIself _typeIself arg_strict_
         _lhsOself :: AnnotatedType
         _lhsOself = rule24 _self
         __result_ = T_AnnotatedType_vOut7 _lhsOself
         in __result_ )
     in C_AnnotatedType_s8 v7
   {-# INLINE rule23 #-}
   rule23 = \ ((_rangeIself) :: Range) ((_typeIself) :: Type) strict_ ->
     AnnotatedType_AnnotatedType _rangeIself strict_ _typeIself
   {-# INLINE rule24 #-}
   rule24 = \ _self ->
     _self

-- AnnotatedTypes ----------------------------------------------
-- wrapper
data Inh_AnnotatedTypes  = Inh_AnnotatedTypes {  }
data Syn_AnnotatedTypes  = Syn_AnnotatedTypes { length_Syn_AnnotatedTypes :: (Int), self_Syn_AnnotatedTypes :: (AnnotatedTypes) }
{-# INLINABLE wrap_AnnotatedTypes #-}
wrap_AnnotatedTypes :: T_AnnotatedTypes  -> Inh_AnnotatedTypes  -> (Syn_AnnotatedTypes )
wrap_AnnotatedTypes (T_AnnotatedTypes act) (Inh_AnnotatedTypes ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_AnnotatedTypes_vIn10 
        (T_AnnotatedTypes_vOut10 _lhsOlength _lhsOself) <- return (inv_AnnotatedTypes_s11 sem arg)
        return (Syn_AnnotatedTypes _lhsOlength _lhsOself)
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
data T_AnnotatedTypes_vIn10  = T_AnnotatedTypes_vIn10 
data T_AnnotatedTypes_vOut10  = T_AnnotatedTypes_vOut10 (Int) (AnnotatedTypes)
{-# NOINLINE sem_AnnotatedTypes_Cons #-}
sem_AnnotatedTypes_Cons :: T_AnnotatedType  -> T_AnnotatedTypes  -> T_AnnotatedTypes 
sem_AnnotatedTypes_Cons arg_hd_ arg_tl_ = T_AnnotatedTypes (return st11) where
   {-# NOINLINE st11 #-}
   st11 = let
      v10 :: T_AnnotatedTypes_v10 
      v10 = \ (T_AnnotatedTypes_vIn10 ) -> ( let
         _hdX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_hd_))
         _tlX11 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedTypes (arg_tl_))
         (T_AnnotatedType_vOut7 _hdIself) = inv_AnnotatedType_s8 _hdX8 (T_AnnotatedType_vIn7 )
         (T_AnnotatedTypes_vOut10 _tlIlength _tlIself) = inv_AnnotatedTypes_s11 _tlX11 (T_AnnotatedTypes_vIn10 )
         _lhsOlength :: Int
         _lhsOlength = rule25 _tlIlength
         _self = rule26 _hdIself _tlIself
         _lhsOself :: AnnotatedTypes
         _lhsOself = rule27 _self
         __result_ = T_AnnotatedTypes_vOut10 _lhsOlength _lhsOself
         in __result_ )
     in C_AnnotatedTypes_s11 v10
   {-# INLINE rule25 #-}
   rule25 = \ ((_tlIlength) :: Int) ->
                          1 + _tlIlength
   {-# INLINE rule26 #-}
   rule26 = \ ((_hdIself) :: AnnotatedType) ((_tlIself) :: AnnotatedTypes) ->
     (:) _hdIself _tlIself
   {-# INLINE rule27 #-}
   rule27 = \ _self ->
     _self
{-# NOINLINE sem_AnnotatedTypes_Nil #-}
sem_AnnotatedTypes_Nil ::  T_AnnotatedTypes 
sem_AnnotatedTypes_Nil  = T_AnnotatedTypes (return st11) where
   {-# NOINLINE st11 #-}
   st11 = let
      v10 :: T_AnnotatedTypes_v10 
      v10 = \ (T_AnnotatedTypes_vIn10 ) -> ( let
         _lhsOlength :: Int
         _lhsOlength = rule28  ()
         _self = rule29  ()
         _lhsOself :: AnnotatedTypes
         _lhsOself = rule30 _self
         __result_ = T_AnnotatedTypes_vOut10 _lhsOlength _lhsOself
         in __result_ )
     in C_AnnotatedTypes_s11 v10
   {-# INLINE rule28 #-}
   rule28 = \  (_ :: ()) ->
                          0
   {-# INLINE rule29 #-}
   rule29 = \  (_ :: ()) ->
     []
   {-# INLINE rule30 #-}
   rule30 = \ _self ->
     _self

-- Body --------------------------------------------------------
-- wrapper
data Inh_Body  = Inh_Body { dictionaryEnv_Inh_Body :: (DictionaryEnvironment), importEnv_Inh_Body :: (ImportEnvironment) }
data Syn_Body  = Syn_Body { decls_Syn_Body :: ( [CoreDecl] ), self_Syn_Body :: (Body) }
{-# INLINABLE wrap_Body #-}
wrap_Body :: T_Body  -> Inh_Body  -> (Syn_Body )
wrap_Body (T_Body act) (Inh_Body _lhsIdictionaryEnv _lhsIimportEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Body_vIn13 _lhsIdictionaryEnv _lhsIimportEnv
        (T_Body_vOut13 _lhsOdecls _lhsOself) <- return (inv_Body_s14 sem arg)
        return (Syn_Body _lhsOdecls _lhsOself)
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
data T_Body_vIn13  = T_Body_vIn13 (DictionaryEnvironment) (ImportEnvironment)
data T_Body_vOut13  = T_Body_vOut13 ( [CoreDecl] ) (Body)
{-# NOINLINE sem_Body_Hole #-}
sem_Body_Hole :: T_Range  -> (Integer) -> T_Body 
sem_Body_Hole arg_range_ arg_id_ = T_Body (return st14) where
   {-# NOINLINE st14 #-}
   st14 = let
      v13 :: T_Body_v13 
      v13 = \ (T_Body_vIn13 _lhsIdictionaryEnv _lhsIimportEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule31  ()
         _self = rule32 _rangeIself arg_id_
         _lhsOself :: Body
         _lhsOself = rule33 _self
         __result_ = T_Body_vOut13 _lhsOdecls _lhsOself
         in __result_ )
     in C_Body_s14 v13
   {-# INLINE rule31 #-}
   rule31 = \  (_ :: ()) ->
     []
   {-# INLINE rule32 #-}
   rule32 = \ ((_rangeIself) :: Range) id_ ->
     Body_Hole _rangeIself id_
   {-# INLINE rule33 #-}
   rule33 = \ _self ->
     _self
{-# NOINLINE sem_Body_Body #-}
sem_Body_Body :: T_Range  -> T_ImportDeclarations  -> T_Declarations  -> T_Body 
sem_Body_Body arg_range_ arg_importdeclarations_ arg_declarations_ = T_Body (return st14) where
   {-# NOINLINE st14 #-}
   st14 = let
      v13 :: T_Body_v13 
      v13 = \ (T_Body_vIn13 _lhsIdictionaryEnv _lhsIimportEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _importdeclarationsX74 = Control.Monad.Identity.runIdentity (attach_T_ImportDeclarations (arg_importdeclarations_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ImportDeclarations_vOut73 _importdeclarationsIself) = inv_ImportDeclarations_s74 _importdeclarationsX74 (T_ImportDeclarations_vIn73 )
         (T_Declarations_vOut31 _declarationsIdecls _declarationsIpatBindNr _declarationsIself) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 _declarationsOdictionaryEnv _declarationsOimportEnv _declarationsOisTopLevel _declarationsOpatBindNr)
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule34 _declarationsIdecls
         _declarationsOpatBindNr = rule35  ()
         _declarationsOisTopLevel = rule36  ()
         _self = rule37 _declarationsIself _importdeclarationsIself _rangeIself
         _lhsOself :: Body
         _lhsOself = rule38 _self
         _declarationsOdictionaryEnv = rule39 _lhsIdictionaryEnv
         _declarationsOimportEnv = rule40 _lhsIimportEnv
         __result_ = T_Body_vOut13 _lhsOdecls _lhsOself
         in __result_ )
     in C_Body_s14 v13
   {-# INLINE rule34 #-}
   rule34 = \ ((_declarationsIdecls) ::  [CoreDecl] ) ->
                                        _declarationsIdecls
   {-# INLINE rule35 #-}
   rule35 = \  (_ :: ()) ->
                                                  0
   {-# INLINE rule36 #-}
   rule36 = \  (_ :: ()) ->
                                                   True
   {-# INLINE rule37 #-}
   rule37 = \ ((_declarationsIself) :: Declarations) ((_importdeclarationsIself) :: ImportDeclarations) ((_rangeIself) :: Range) ->
     Body_Body _rangeIself _importdeclarationsIself _declarationsIself
   {-# INLINE rule38 #-}
   rule38 = \ _self ->
     _self
   {-# INLINE rule39 #-}
   rule39 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule40 #-}
   rule40 = \ ((_lhsIimportEnv) :: ImportEnvironment) ->
     _lhsIimportEnv

-- Constructor -------------------------------------------------
-- wrapper
data Inh_Constructor  = Inh_Constructor { dataTypeName_Inh_Constructor :: (Name), dictionaryEnv_Inh_Constructor :: (DictionaryEnvironment), importEnv_Inh_Constructor :: (ImportEnvironment), tag_Inh_Constructor :: (Int) }
data Syn_Constructor  = Syn_Constructor { cons_Syn_Constructor :: ( [(Id, CoreDecl)] ), self_Syn_Constructor :: (Constructor) }
{-# INLINABLE wrap_Constructor #-}
wrap_Constructor :: T_Constructor  -> Inh_Constructor  -> (Syn_Constructor )
wrap_Constructor (T_Constructor act) (Inh_Constructor _lhsIdataTypeName _lhsIdictionaryEnv _lhsIimportEnv _lhsItag) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Constructor_vIn16 _lhsIdataTypeName _lhsIdictionaryEnv _lhsIimportEnv _lhsItag
        (T_Constructor_vOut16 _lhsOcons _lhsOself) <- return (inv_Constructor_s17 sem arg)
        return (Syn_Constructor _lhsOcons _lhsOself)
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
data T_Constructor_vIn16  = T_Constructor_vIn16 (Name) (DictionaryEnvironment) (ImportEnvironment) (Int)
data T_Constructor_vOut16  = T_Constructor_vOut16 ( [(Id, CoreDecl)] ) (Constructor)
{-# NOINLINE sem_Constructor_Constructor #-}
sem_Constructor_Constructor :: T_Range  -> T_Name  -> T_AnnotatedTypes  -> T_Constructor 
sem_Constructor_Constructor arg_range_ arg_constructor_ arg_types_ = T_Constructor (return st17) where
   {-# NOINLINE st17 #-}
   st17 = let
      v16 :: T_Constructor_v16 
      v16 = \ (T_Constructor_vIn16 _lhsIdataTypeName _lhsIdictionaryEnv _lhsIimportEnv _lhsItag) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _constructorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructor_))
         _typesX11 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedTypes (arg_types_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _constructorIself) = inv_Name_s113 _constructorX113 (T_Name_vIn112 )
         (T_AnnotatedTypes_vOut10 _typesIlength _typesIself) = inv_AnnotatedTypes_s11 _typesX11 (T_AnnotatedTypes_vIn10 )
         _lhsOcons ::  [(Id, CoreDecl)] 
         _lhsOcons = rule41 _constructorIself _lhsIdataTypeName _lhsIimportEnv _lhsItag _typesIlength
         _self = rule42 _constructorIself _rangeIself _typesIself
         _lhsOself :: Constructor
         _lhsOself = rule43 _self
         __result_ = T_Constructor_vOut16 _lhsOcons _lhsOself
         in __result_ )
     in C_Constructor_s17 v16
   {-# INLINE rule41 #-}
   rule41 = \ ((_constructorIself) :: Name) ((_lhsIdataTypeName) :: Name) ((_lhsIimportEnv) :: ImportEnvironment) ((_lhsItag) :: Int) ((_typesIlength) :: Int) ->
          [ (idFromName _constructorIself, Core.DeclCon
              { Core.declName    = idFromName _constructorIself
              , Core.declAccess  = Core.private
              , Core.declArity   = _typesIlength
              , Core.conTag      = _lhsItag
              , Core.declCustoms = constructorCustoms
                                      _lhsIdataTypeName
                                      _constructorIself
                                      (valueConstructors _lhsIimportEnv)
              }
            )
          ]
   {-# INLINE rule42 #-}
   rule42 = \ ((_constructorIself) :: Name) ((_rangeIself) :: Range) ((_typesIself) :: AnnotatedTypes) ->
     Constructor_Constructor _rangeIself _constructorIself _typesIself
   {-# INLINE rule43 #-}
   rule43 = \ _self ->
     _self
{-# NOINLINE sem_Constructor_Infix #-}
sem_Constructor_Infix :: T_Range  -> T_AnnotatedType  -> T_Name  -> T_AnnotatedType  -> T_Constructor 
sem_Constructor_Infix arg_range_ arg_leftType_ arg_constructorOperator_ arg_rightType_ = T_Constructor (return st17) where
   {-# NOINLINE st17 #-}
   st17 = let
      v16 :: T_Constructor_v16 
      v16 = \ (T_Constructor_vIn16 _lhsIdataTypeName _lhsIdictionaryEnv _lhsIimportEnv _lhsItag) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftTypeX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_leftType_))
         _constructorOperatorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructorOperator_))
         _rightTypeX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_rightType_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_AnnotatedType_vOut7 _leftTypeIself) = inv_AnnotatedType_s8 _leftTypeX8 (T_AnnotatedType_vIn7 )
         (T_Name_vOut112 _constructorOperatorIself) = inv_Name_s113 _constructorOperatorX113 (T_Name_vIn112 )
         (T_AnnotatedType_vOut7 _rightTypeIself) = inv_AnnotatedType_s8 _rightTypeX8 (T_AnnotatedType_vIn7 )
         _lhsOcons ::  [(Id, CoreDecl)] 
         _lhsOcons = rule44 _constructorOperatorIself _lhsIdataTypeName _lhsIimportEnv _lhsItag
         _self = rule45 _constructorOperatorIself _leftTypeIself _rangeIself _rightTypeIself
         _lhsOself :: Constructor
         _lhsOself = rule46 _self
         __result_ = T_Constructor_vOut16 _lhsOcons _lhsOself
         in __result_ )
     in C_Constructor_s17 v16
   {-# INLINE rule44 #-}
   rule44 = \ ((_constructorOperatorIself) :: Name) ((_lhsIdataTypeName) :: Name) ((_lhsIimportEnv) :: ImportEnvironment) ((_lhsItag) :: Int) ->
          [ (idFromName _constructorOperatorIself, Core.DeclCon
              { Core.declName    = idFromName _constructorOperatorIself
              , Core.declAccess  = Core.private
              , Core.declArity   = 2
              , Core.conTag      = _lhsItag
              , Core.declCustoms = constructorCustoms
                                      _lhsIdataTypeName
                                      _constructorOperatorIself
                                      (valueConstructors _lhsIimportEnv)
              }
            )
          ]
   {-# INLINE rule45 #-}
   rule45 = \ ((_constructorOperatorIself) :: Name) ((_leftTypeIself) :: AnnotatedType) ((_rangeIself) :: Range) ((_rightTypeIself) :: AnnotatedType) ->
     Constructor_Infix _rangeIself _leftTypeIself _constructorOperatorIself _rightTypeIself
   {-# INLINE rule46 #-}
   rule46 = \ _self ->
     _self
{-# NOINLINE sem_Constructor_Record #-}
sem_Constructor_Record :: T_Range  -> T_Name  -> T_FieldDeclarations  -> T_Constructor 
sem_Constructor_Record arg_range_ arg_constructor_ arg_fieldDeclarations_ = T_Constructor (return st17) where
   {-# NOINLINE st17 #-}
   st17 = let
      v16 :: T_Constructor_v16 
      v16 = \ (T_Constructor_vIn16 _lhsIdataTypeName _lhsIdictionaryEnv _lhsIimportEnv _lhsItag) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _constructorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructor_))
         _fieldDeclarationsX50 = Control.Monad.Identity.runIdentity (attach_T_FieldDeclarations (arg_fieldDeclarations_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _constructorIself) = inv_Name_s113 _constructorX113 (T_Name_vIn112 )
         (T_FieldDeclarations_vOut49 _fieldDeclarationsIself) = inv_FieldDeclarations_s50 _fieldDeclarationsX50 (T_FieldDeclarations_vIn49 )
         _lhsOcons ::  [(Id, CoreDecl)] 
         _lhsOcons = rule47  ()
         _self = rule48 _constructorIself _fieldDeclarationsIself _rangeIself
         _lhsOself :: Constructor
         _lhsOself = rule49 _self
         __result_ = T_Constructor_vOut16 _lhsOcons _lhsOself
         in __result_ )
     in C_Constructor_s17 v16
   {-# INLINE rule47 #-}
   rule47 = \  (_ :: ()) ->
                                     internalError "ToCoreDecl" "Constructor" "records not supported"
   {-# INLINE rule48 #-}
   rule48 = \ ((_constructorIself) :: Name) ((_fieldDeclarationsIself) :: FieldDeclarations) ((_rangeIself) :: Range) ->
     Constructor_Record _rangeIself _constructorIself _fieldDeclarationsIself
   {-# INLINE rule49 #-}
   rule49 = \ _self ->
     _self

-- Constructors ------------------------------------------------
-- wrapper
data Inh_Constructors  = Inh_Constructors { dataTypeName_Inh_Constructors :: (Name), dictionaryEnv_Inh_Constructors :: (DictionaryEnvironment), importEnv_Inh_Constructors :: (ImportEnvironment), tag_Inh_Constructors :: (Int) }
data Syn_Constructors  = Syn_Constructors { cons_Syn_Constructors :: ( [(Id, CoreDecl)] ), self_Syn_Constructors :: (Constructors) }
{-# INLINABLE wrap_Constructors #-}
wrap_Constructors :: T_Constructors  -> Inh_Constructors  -> (Syn_Constructors )
wrap_Constructors (T_Constructors act) (Inh_Constructors _lhsIdataTypeName _lhsIdictionaryEnv _lhsIimportEnv _lhsItag) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Constructors_vIn19 _lhsIdataTypeName _lhsIdictionaryEnv _lhsIimportEnv _lhsItag
        (T_Constructors_vOut19 _lhsOcons _lhsOself) <- return (inv_Constructors_s20 sem arg)
        return (Syn_Constructors _lhsOcons _lhsOself)
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
data T_Constructors_vIn19  = T_Constructors_vIn19 (Name) (DictionaryEnvironment) (ImportEnvironment) (Int)
data T_Constructors_vOut19  = T_Constructors_vOut19 ( [(Id, CoreDecl)] ) (Constructors)
{-# NOINLINE sem_Constructors_Cons #-}
sem_Constructors_Cons :: T_Constructor  -> T_Constructors  -> T_Constructors 
sem_Constructors_Cons arg_hd_ arg_tl_ = T_Constructors (return st20) where
   {-# NOINLINE st20 #-}
   st20 = let
      v19 :: T_Constructors_v19 
      v19 = \ (T_Constructors_vIn19 _lhsIdataTypeName _lhsIdictionaryEnv _lhsIimportEnv _lhsItag) -> ( let
         _hdX17 = Control.Monad.Identity.runIdentity (attach_T_Constructor (arg_hd_))
         _tlX20 = Control.Monad.Identity.runIdentity (attach_T_Constructors (arg_tl_))
         (T_Constructor_vOut16 _hdIcons _hdIself) = inv_Constructor_s17 _hdX17 (T_Constructor_vIn16 _hdOdataTypeName _hdOdictionaryEnv _hdOimportEnv _hdOtag)
         (T_Constructors_vOut19 _tlIcons _tlIself) = inv_Constructors_s20 _tlX20 (T_Constructors_vIn19 _tlOdataTypeName _tlOdictionaryEnv _tlOimportEnv _tlOtag)
         _hdOtag = rule50 _lhsItag
         _tlOtag = rule51 _lhsItag
         _lhsOcons ::  [(Id, CoreDecl)] 
         _lhsOcons = rule52 _hdIcons _tlIcons
         _self = rule53 _hdIself _tlIself
         _lhsOself :: Constructors
         _lhsOself = rule54 _self
         _hdOdataTypeName = rule55 _lhsIdataTypeName
         _hdOdictionaryEnv = rule56 _lhsIdictionaryEnv
         _hdOimportEnv = rule57 _lhsIimportEnv
         _tlOdataTypeName = rule58 _lhsIdataTypeName
         _tlOdictionaryEnv = rule59 _lhsIdictionaryEnv
         _tlOimportEnv = rule60 _lhsIimportEnv
         __result_ = T_Constructors_vOut19 _lhsOcons _lhsOself
         in __result_ )
     in C_Constructors_s20 v19
   {-# INLINE rule50 #-}
   rule50 = \ ((_lhsItag) :: Int) ->
                       _lhsItag
   {-# INLINE rule51 #-}
   rule51 = \ ((_lhsItag) :: Int) ->
                       _lhsItag + 1
   {-# INLINE rule52 #-}
   rule52 = \ ((_hdIcons) ::  [(Id, CoreDecl)] ) ((_tlIcons) ::  [(Id, CoreDecl)] ) ->
     _hdIcons  ++  _tlIcons
   {-# INLINE rule53 #-}
   rule53 = \ ((_hdIself) :: Constructor) ((_tlIself) :: Constructors) ->
     (:) _hdIself _tlIself
   {-# INLINE rule54 #-}
   rule54 = \ _self ->
     _self
   {-# INLINE rule55 #-}
   rule55 = \ ((_lhsIdataTypeName) :: Name) ->
     _lhsIdataTypeName
   {-# INLINE rule56 #-}
   rule56 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule57 #-}
   rule57 = \ ((_lhsIimportEnv) :: ImportEnvironment) ->
     _lhsIimportEnv
   {-# INLINE rule58 #-}
   rule58 = \ ((_lhsIdataTypeName) :: Name) ->
     _lhsIdataTypeName
   {-# INLINE rule59 #-}
   rule59 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule60 #-}
   rule60 = \ ((_lhsIimportEnv) :: ImportEnvironment) ->
     _lhsIimportEnv
{-# NOINLINE sem_Constructors_Nil #-}
sem_Constructors_Nil ::  T_Constructors 
sem_Constructors_Nil  = T_Constructors (return st20) where
   {-# NOINLINE st20 #-}
   st20 = let
      v19 :: T_Constructors_v19 
      v19 = \ (T_Constructors_vIn19 _lhsIdataTypeName _lhsIdictionaryEnv _lhsIimportEnv _lhsItag) -> ( let
         _lhsOcons ::  [(Id, CoreDecl)] 
         _lhsOcons = rule61  ()
         _self = rule62  ()
         _lhsOself :: Constructors
         _lhsOself = rule63 _self
         __result_ = T_Constructors_vOut19 _lhsOcons _lhsOself
         in __result_ )
     in C_Constructors_s20 v19
   {-# INLINE rule61 #-}
   rule61 = \  (_ :: ()) ->
     []
   {-# INLINE rule62 #-}
   rule62 = \  (_ :: ()) ->
     []
   {-# INLINE rule63 #-}
   rule63 = \ _self ->
     _self

-- ContextItem -------------------------------------------------
-- wrapper
data Inh_ContextItem  = Inh_ContextItem {  }
data Syn_ContextItem  = Syn_ContextItem { self_Syn_ContextItem :: (ContextItem) }
{-# INLINABLE wrap_ContextItem #-}
wrap_ContextItem :: T_ContextItem  -> Inh_ContextItem  -> (Syn_ContextItem )
wrap_ContextItem (T_ContextItem act) (Inh_ContextItem ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_ContextItem_vIn22 
        (T_ContextItem_vOut22 _lhsOself) <- return (inv_ContextItem_s23 sem arg)
        return (Syn_ContextItem _lhsOself)
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
data T_ContextItem_vIn22  = T_ContextItem_vIn22 
data T_ContextItem_vOut22  = T_ContextItem_vOut22 (ContextItem)
{-# NOINLINE sem_ContextItem_ContextItem #-}
sem_ContextItem_ContextItem :: T_Range  -> T_Name  -> T_Types  -> T_ContextItem 
sem_ContextItem_ContextItem arg_range_ arg_name_ arg_types_ = T_ContextItem (return st23) where
   {-# NOINLINE st23 #-}
   st23 = let
      v22 :: T_ContextItem_v22 
      v22 = \ (T_ContextItem_vIn22 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _typesX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_types_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Types_vOut166 _typesIself) = inv_Types_s167 _typesX167 (T_Types_vIn166 )
         _self = rule64 _nameIself _rangeIself _typesIself
         _lhsOself :: ContextItem
         _lhsOself = rule65 _self
         __result_ = T_ContextItem_vOut22 _lhsOself
         in __result_ )
     in C_ContextItem_s23 v22
   {-# INLINE rule64 #-}
   rule64 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ((_typesIself) :: Types) ->
     ContextItem_ContextItem _rangeIself _nameIself _typesIself
   {-# INLINE rule65 #-}
   rule65 = \ _self ->
     _self

-- ContextItems ------------------------------------------------
-- wrapper
data Inh_ContextItems  = Inh_ContextItems {  }
data Syn_ContextItems  = Syn_ContextItems { self_Syn_ContextItems :: (ContextItems) }
{-# INLINABLE wrap_ContextItems #-}
wrap_ContextItems :: T_ContextItems  -> Inh_ContextItems  -> (Syn_ContextItems )
wrap_ContextItems (T_ContextItems act) (Inh_ContextItems ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_ContextItems_vIn25 
        (T_ContextItems_vOut25 _lhsOself) <- return (inv_ContextItems_s26 sem arg)
        return (Syn_ContextItems _lhsOself)
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
data T_ContextItems_vIn25  = T_ContextItems_vIn25 
data T_ContextItems_vOut25  = T_ContextItems_vOut25 (ContextItems)
{-# NOINLINE sem_ContextItems_Cons #-}
sem_ContextItems_Cons :: T_ContextItem  -> T_ContextItems  -> T_ContextItems 
sem_ContextItems_Cons arg_hd_ arg_tl_ = T_ContextItems (return st26) where
   {-# NOINLINE st26 #-}
   st26 = let
      v25 :: T_ContextItems_v25 
      v25 = \ (T_ContextItems_vIn25 ) -> ( let
         _hdX23 = Control.Monad.Identity.runIdentity (attach_T_ContextItem (arg_hd_))
         _tlX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_tl_))
         (T_ContextItem_vOut22 _hdIself) = inv_ContextItem_s23 _hdX23 (T_ContextItem_vIn22 )
         (T_ContextItems_vOut25 _tlIself) = inv_ContextItems_s26 _tlX26 (T_ContextItems_vIn25 )
         _self = rule66 _hdIself _tlIself
         _lhsOself :: ContextItems
         _lhsOself = rule67 _self
         __result_ = T_ContextItems_vOut25 _lhsOself
         in __result_ )
     in C_ContextItems_s26 v25
   {-# INLINE rule66 #-}
   rule66 = \ ((_hdIself) :: ContextItem) ((_tlIself) :: ContextItems) ->
     (:) _hdIself _tlIself
   {-# INLINE rule67 #-}
   rule67 = \ _self ->
     _self
{-# NOINLINE sem_ContextItems_Nil #-}
sem_ContextItems_Nil ::  T_ContextItems 
sem_ContextItems_Nil  = T_ContextItems (return st26) where
   {-# NOINLINE st26 #-}
   st26 = let
      v25 :: T_ContextItems_v25 
      v25 = \ (T_ContextItems_vIn25 ) -> ( let
         _self = rule68  ()
         _lhsOself :: ContextItems
         _lhsOself = rule69 _self
         __result_ = T_ContextItems_vOut25 _lhsOself
         in __result_ )
     in C_ContextItems_s26 v25
   {-# INLINE rule68 #-}
   rule68 = \  (_ :: ()) ->
     []
   {-# INLINE rule69 #-}
   rule69 = \ _self ->
     _self

-- Declaration -------------------------------------------------
-- wrapper
data Inh_Declaration  = Inh_Declaration { dictionaryEnv_Inh_Declaration :: (DictionaryEnvironment), importEnv_Inh_Declaration :: (ImportEnvironment), isTopLevel_Inh_Declaration :: (Bool), patBindNr_Inh_Declaration :: (Int) }
data Syn_Declaration  = Syn_Declaration { decls_Syn_Declaration :: ( [CoreDecl] ), patBindNr_Syn_Declaration :: (Int), self_Syn_Declaration :: (Declaration) }
{-# INLINABLE wrap_Declaration #-}
wrap_Declaration :: T_Declaration  -> Inh_Declaration  -> (Syn_Declaration )
wrap_Declaration (T_Declaration act) (Inh_Declaration _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr
        (T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself) <- return (inv_Declaration_s29 sem arg)
        return (Syn_Declaration _lhsOdecls _lhsOpatBindNr _lhsOself)
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
data T_Declaration_vIn28  = T_Declaration_vIn28 (DictionaryEnvironment) (ImportEnvironment) (Bool) (Int)
data T_Declaration_vOut28  = T_Declaration_vOut28 ( [CoreDecl] ) (Int) (Declaration)
{-# NOINLINE sem_Declaration_Hole #-}
sem_Declaration_Hole :: T_Range  -> (Integer) -> T_Declaration 
sem_Declaration_Hole arg_range_ arg_id_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule70  ()
         _self = rule71 _rangeIself arg_id_
         _lhsOself :: Declaration
         _lhsOself = rule72 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule73 _lhsIpatBindNr
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule70 #-}
   rule70 = \  (_ :: ()) ->
     []
   {-# INLINE rule71 #-}
   rule71 = \ ((_rangeIself) :: Range) id_ ->
     Declaration_Hole _rangeIself id_
   {-# INLINE rule72 #-}
   rule72 = \ _self ->
     _self
   {-# INLINE rule73 #-}
   rule73 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr
{-# NOINLINE sem_Declaration_Type #-}
sem_Declaration_Type :: T_Range  -> T_SimpleType  -> T_Type  -> T_Declaration 
sem_Declaration_Type arg_range_ arg_simpletype_ arg_type_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_SimpleType_vOut151 _simpletypeIname _simpletypeIself _simpletypeItypevariables) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_Type_vOut163 _typeIself) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule74 _self _simpletypeIname _simpletypeIself _simpletypeItypevariables _typeIself
         _self = rule75 _rangeIself _simpletypeIself _typeIself
         _lhsOself :: Declaration
         _lhsOself = rule76 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule77 _lhsIpatBindNr
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule74 #-}
   rule74 = \ _self ((_simpletypeIname) :: Name) ((_simpletypeIself) :: SimpleType) ((_simpletypeItypevariables) :: Names) ((_typeIself) :: Type) ->
          let
              (t1,[t2])   = convertFromSimpleTypeAndTypes _simpletypeIself [_typeIself]
              allTypeVars = ftv [t1,t2]
              (ts1,ts2)   = ( Quantification (allTypeVars, [], [] .=>. t1) :: TpScheme
                            , Quantification (allTypeVars, [], [] .=>. t2) :: TpScheme
                            )
          in
          [ Core.DeclCustom
              { Core.declName    = idFromString (getNameName _simpletypeIname)
              , Core.declAccess  = Core.private
              , Core.declKind    = Core.DeclKindCustom (idFromString "typedecl")
              , Core.declCustoms =
                  [ Core.CustomBytes
                      (Byte.bytesFromString
                          (  show ts1
                          ++ " = "
                          ++ show ts2
                          )
                      )
                  , Core.CustomInt
                      (length _simpletypeItypevariables)
                  ]
              }
          ]
          ++
          [ DerivingShow.typeShowFunction _self ]
   {-# INLINE rule75 #-}
   rule75 = \ ((_rangeIself) :: Range) ((_simpletypeIself) :: SimpleType) ((_typeIself) :: Type) ->
     Declaration_Type _rangeIself _simpletypeIself _typeIself
   {-# INLINE rule76 #-}
   rule76 = \ _self ->
     _self
   {-# INLINE rule77 #-}
   rule77 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr
{-# NOINLINE sem_Declaration_Data #-}
sem_Declaration_Data :: T_Range  -> T_ContextItems  -> T_SimpleType  -> T_Constructors  -> T_Names  -> T_Declaration 
sem_Declaration_Data arg_range_ arg_context_ arg_simpletype_ arg_constructors_ arg_derivings_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _constructorsX20 = Control.Monad.Identity.runIdentity (attach_T_Constructors (arg_constructors_))
         _derivingsX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_derivings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextIself) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 )
         (T_SimpleType_vOut151 _simpletypeIname _simpletypeIself _simpletypeItypevariables) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_Constructors_vOut19 _constructorsIcons _constructorsIself) = inv_Constructors_s20 _constructorsX20 (T_Constructors_vIn19 _constructorsOdataTypeName _constructorsOdictionaryEnv _constructorsOimportEnv _constructorsOtag)
         (T_Names_vOut115 _derivingsInames _derivingsIself) = inv_Names_s116 _derivingsX116 (T_Names_vIn115 )
         _constructorsOtag = rule78  ()
         _constructorsOdataTypeName = rule79 _simpletypeIname
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule80 _constructorsIcons _derivingsIself _self _simpletypeIname _simpletypeItypevariables
         _self = rule81 _constructorsIself _contextIself _derivingsIself _rangeIself _simpletypeIself
         _lhsOself :: Declaration
         _lhsOself = rule82 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule83 _lhsIpatBindNr
         _constructorsOdictionaryEnv = rule84 _lhsIdictionaryEnv
         _constructorsOimportEnv = rule85 _lhsIimportEnv
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule78 #-}
   rule78 = \  (_ :: ()) ->
                                   0
   {-# INLINE rule79 #-}
   rule79 = \ ((_simpletypeIname) :: Name) ->
                                            _simpletypeIname
   {-# INLINE rule80 #-}
   rule80 = \ ((_constructorsIcons) ::  [(Id, CoreDecl)] ) ((_derivingsIself) :: Names) _self ((_simpletypeIname) :: Name) ((_simpletypeItypevariables) :: Names) ->
          map snd _constructorsIcons
          ++
          [ Core.DeclCustom
              { Core.declName    = idFromString (getNameName _simpletypeIname)
              , Core.declAccess  = Core.private
              , Core.declKind    = Core.DeclKindCustom (idFromString "data")
              , Core.declCustoms = [Core.CustomInt (length _simpletypeItypevariables)]
              }
          ]
          ++
          [ DerivingShow.dataShowFunction _self ]
          ++
          (if "Show" `elem` map show _derivingsIself
           then [ DerivingShow.dataDictionary _self ]
           else []
          )
          ++
          (if "Eq" `elem` map show _derivingsIself
           then [ DerivingEq.dataDictionary _self ]
           else []
          )
   {-# INLINE rule81 #-}
   rule81 = \ ((_constructorsIself) :: Constructors) ((_contextIself) :: ContextItems) ((_derivingsIself) :: Names) ((_rangeIself) :: Range) ((_simpletypeIself) :: SimpleType) ->
     Declaration_Data _rangeIself _contextIself _simpletypeIself _constructorsIself _derivingsIself
   {-# INLINE rule82 #-}
   rule82 = \ _self ->
     _self
   {-# INLINE rule83 #-}
   rule83 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr
   {-# INLINE rule84 #-}
   rule84 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule85 #-}
   rule85 = \ ((_lhsIimportEnv) :: ImportEnvironment) ->
     _lhsIimportEnv
{-# NOINLINE sem_Declaration_Newtype #-}
sem_Declaration_Newtype :: T_Range  -> T_ContextItems  -> T_SimpleType  -> T_Constructor  -> T_Names  -> T_Declaration 
sem_Declaration_Newtype arg_range_ arg_context_ arg_simpletype_ arg_constructor_ arg_derivings_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _constructorX17 = Control.Monad.Identity.runIdentity (attach_T_Constructor (arg_constructor_))
         _derivingsX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_derivings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextIself) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 )
         (T_SimpleType_vOut151 _simpletypeIname _simpletypeIself _simpletypeItypevariables) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_Constructor_vOut16 _constructorIcons _constructorIself) = inv_Constructor_s17 _constructorX17 (T_Constructor_vIn16 _constructorOdataTypeName _constructorOdictionaryEnv _constructorOimportEnv _constructorOtag)
         (T_Names_vOut115 _derivingsInames _derivingsIself) = inv_Names_s116 _derivingsX116 (T_Names_vIn115 )
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule86  ()
         _constructorOtag = rule87  ()
         _constructorOdataTypeName = rule88 _simpletypeIname
         _self = rule89 _constructorIself _contextIself _derivingsIself _rangeIself _simpletypeIself
         _lhsOself :: Declaration
         _lhsOself = rule90 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule91 _lhsIpatBindNr
         _constructorOdictionaryEnv = rule92 _lhsIdictionaryEnv
         _constructorOimportEnv = rule93 _lhsIimportEnv
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule86 #-}
   rule86 = \  (_ :: ()) ->
                                         internalError "ToCoreDecl" "Declaration" "'newType' not supported"
   {-# INLINE rule87 #-}
   rule87 = \  (_ :: ()) ->
                                            0
   {-# INLINE rule88 #-}
   rule88 = \ ((_simpletypeIname) :: Name) ->
                                                     _simpletypeIname
   {-# INLINE rule89 #-}
   rule89 = \ ((_constructorIself) :: Constructor) ((_contextIself) :: ContextItems) ((_derivingsIself) :: Names) ((_rangeIself) :: Range) ((_simpletypeIself) :: SimpleType) ->
     Declaration_Newtype _rangeIself _contextIself _simpletypeIself _constructorIself _derivingsIself
   {-# INLINE rule90 #-}
   rule90 = \ _self ->
     _self
   {-# INLINE rule91 #-}
   rule91 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr
   {-# INLINE rule92 #-}
   rule92 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule93 #-}
   rule93 = \ ((_lhsIimportEnv) :: ImportEnvironment) ->
     _lhsIimportEnv
{-# NOINLINE sem_Declaration_Class #-}
sem_Declaration_Class :: T_Range  -> T_ContextItems  -> T_SimpleType  -> T_MaybeDeclarations  -> T_Declaration 
sem_Declaration_Class arg_range_ arg_context_ arg_simpletype_ arg_where_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _simpletypeX152 = Control.Monad.Identity.runIdentity (attach_T_SimpleType (arg_simpletype_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextIself) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 )
         (T_SimpleType_vOut151 _simpletypeIname _simpletypeIself _simpletypeItypevariables) = inv_SimpleType_s152 _simpletypeX152 (T_SimpleType_vIn151 )
         (T_MaybeDeclarations_vOut88 _whereIcore _whereIself) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 _whereOdictionaryEnv)
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule94  ()
         _self = rule95 _contextIself _rangeIself _simpletypeIself _whereIself
         _lhsOself :: Declaration
         _lhsOself = rule96 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule97 _lhsIpatBindNr
         _whereOdictionaryEnv = rule98 _lhsIdictionaryEnv
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule94 #-}
   rule94 = \  (_ :: ()) ->
                                         internalError "ToCoreDecl" "Declaration" "'class' not supported"
   {-# INLINE rule95 #-}
   rule95 = \ ((_contextIself) :: ContextItems) ((_rangeIself) :: Range) ((_simpletypeIself) :: SimpleType) ((_whereIself) :: MaybeDeclarations) ->
     Declaration_Class _rangeIself _contextIself _simpletypeIself _whereIself
   {-# INLINE rule96 #-}
   rule96 = \ _self ->
     _self
   {-# INLINE rule97 #-}
   rule97 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr
   {-# INLINE rule98 #-}
   rule98 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Declaration_Instance #-}
sem_Declaration_Instance :: T_Range  -> T_ContextItems  -> T_Name  -> T_Types  -> T_MaybeDeclarations  -> T_Declaration 
sem_Declaration_Instance arg_range_ arg_context_ arg_name_ arg_types_ arg_where_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _typesX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_types_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextIself) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Types_vOut166 _typesIself) = inv_Types_s167 _typesX167 (T_Types_vIn166 )
         (T_MaybeDeclarations_vOut88 _whereIcore _whereIself) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 _whereOdictionaryEnv)
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule99  ()
         _self = rule100 _contextIself _nameIself _rangeIself _typesIself _whereIself
         _lhsOself :: Declaration
         _lhsOself = rule101 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule102 _lhsIpatBindNr
         _whereOdictionaryEnv = rule103 _lhsIdictionaryEnv
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule99 #-}
   rule99 = \  (_ :: ()) ->
                                         internalError "ToCoreDecl" "Declaration" "'instance' not supported"
   {-# INLINE rule100 #-}
   rule100 = \ ((_contextIself) :: ContextItems) ((_nameIself) :: Name) ((_rangeIself) :: Range) ((_typesIself) :: Types) ((_whereIself) :: MaybeDeclarations) ->
     Declaration_Instance _rangeIself _contextIself _nameIself _typesIself _whereIself
   {-# INLINE rule101 #-}
   rule101 = \ _self ->
     _self
   {-# INLINE rule102 #-}
   rule102 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr
   {-# INLINE rule103 #-}
   rule103 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Declaration_Default #-}
sem_Declaration_Default :: T_Range  -> T_Types  -> T_Declaration 
sem_Declaration_Default arg_range_ arg_types_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typesX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_types_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Types_vOut166 _typesIself) = inv_Types_s167 _typesX167 (T_Types_vIn166 )
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule104  ()
         _self = rule105 _rangeIself _typesIself
         _lhsOself :: Declaration
         _lhsOself = rule106 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule107 _lhsIpatBindNr
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule104 #-}
   rule104 = \  (_ :: ()) ->
                                         internalError "ToCoreDecl" "Declaration" "'default' not supported"
   {-# INLINE rule105 #-}
   rule105 = \ ((_rangeIself) :: Range) ((_typesIself) :: Types) ->
     Declaration_Default _rangeIself _typesIself
   {-# INLINE rule106 #-}
   rule106 = \ _self ->
     _self
   {-# INLINE rule107 #-}
   rule107 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr
{-# NOINLINE sem_Declaration_FunctionBindings #-}
sem_Declaration_FunctionBindings :: T_Range  -> T_FunctionBindings  -> T_Declaration 
sem_Declaration_FunctionBindings arg_range_ arg_bindings_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _bindingsX59 = Control.Monad.Identity.runIdentity (attach_T_FunctionBindings (arg_bindings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_FunctionBindings_vOut58 _bindingsIarity _bindingsIcore _bindingsIname _bindingsIself) = inv_FunctionBindings_s59 _bindingsX59 (T_FunctionBindings_vIn58 _bindingsOdictionaryEnv _bindingsOids _bindingsOrange)
         _ids = rule108 _bindingsIarity
         _bindingsOids = rule109 _ids
         _bindingsOrange = rule110 _rangeIself
         _dictionaries = rule111 _bindingsIname _lhsIdictionaryEnv
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule112 _bindingsIcore _bindingsIname _dictionaries _ids _lhsIimportEnv _lhsIisTopLevel
         _self = rule113 _bindingsIself _rangeIself
         _lhsOself :: Declaration
         _lhsOself = rule114 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule115 _lhsIpatBindNr
         _bindingsOdictionaryEnv = rule116 _lhsIdictionaryEnv
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule108 #-}
   rule108 = \ ((_bindingsIarity) :: Int) ->
                                         freshIds "u$" _bindingsIarity
   {-# INLINE rule109 #-}
   rule109 = \ _ids ->
                                         _ids
   {-# INLINE rule110 #-}
   rule110 = \ ((_rangeIself) :: Range) ->
                                           _rangeIself
   {-# INLINE rule111 #-}
   rule111 = \ ((_bindingsIname) :: Name) ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
                                             map predicateToId
                                                (getPredicateForDecl _bindingsIname _lhsIdictionaryEnv)
   {-# INLINE rule112 #-}
   rule112 = \ ((_bindingsIcore) :: Core.Expr) ((_bindingsIname) :: Name) _dictionaries _ids ((_lhsIimportEnv) :: ImportEnvironment) ((_lhsIisTopLevel) :: Bool) ->
          [ Core.DeclValue
              { Core.declName    = idFromName _bindingsIname
              , Core.declAccess  = Core.private
              , Core.valueEnc    = Nothing
              , Core.valueValue  = foldr Core.Lam _bindingsIcore (_dictionaries ++ _ids)
              , Core.declCustoms = toplevelType _bindingsIname _lhsIimportEnv _lhsIisTopLevel
              }
          ]
   {-# INLINE rule113 #-}
   rule113 = \ ((_bindingsIself) :: FunctionBindings) ((_rangeIself) :: Range) ->
     Declaration_FunctionBindings _rangeIself _bindingsIself
   {-# INLINE rule114 #-}
   rule114 = \ _self ->
     _self
   {-# INLINE rule115 #-}
   rule115 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr
   {-# INLINE rule116 #-}
   rule116 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Declaration_PatternBinding #-}
sem_Declaration_PatternBinding :: T_Range  -> T_Pattern  -> T_RightHandSide  -> T_Declaration 
sem_Declaration_PatternBinding arg_range_ arg_pattern_ arg_righthandside_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _righthandsideX149 = Control.Monad.Identity.runIdentity (attach_T_RightHandSide (arg_righthandside_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIself _patternIvars) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         (T_RightHandSide_vOut148 _righthandsideIcore _righthandsideIisGuarded _righthandsideIself) = inv_RightHandSide_s149 _righthandsideX149 (T_RightHandSide_vIn148 _righthandsideOdictionaryEnv)
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule117 _lhsIpatBindNr
         _dictionaries = rule118 _lhsIdictionaryEnv _patternIself
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule119 _dictionaries _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr _patternIself _patternIvars _rangeIself _righthandsideIcore
         _self = rule120 _patternIself _rangeIself _righthandsideIself
         _lhsOself :: Declaration
         _lhsOself = rule121 _self
         _righthandsideOdictionaryEnv = rule122 _lhsIdictionaryEnv
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule117 #-}
   rule117 = \ ((_lhsIpatBindNr) :: Int) ->
                                          _lhsIpatBindNr + 1
   {-# INLINE rule118 #-}
   rule118 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ((_patternIself) :: Pattern) ->
                              case _patternIself of
                                  Pattern_Variable _ n ->
                                     map predicateToId
                                        (getPredicateForDecl n _lhsIdictionaryEnv)
                                  _ -> []
   {-# INLINE rule119 #-}
   rule119 = \ _dictionaries ((_lhsIimportEnv) :: ImportEnvironment) ((_lhsIisTopLevel) :: Bool) ((_lhsIpatBindNr) :: Int) ((_patternIself) :: Pattern) ((_patternIvars) ::  [Name] ) ((_rangeIself) :: Range) ((_righthandsideIcore) ::  Core.Expr ) ->
          case _patternIself of
              Pattern_Variable _ n ->
                  [ Core.DeclValue
                      { Core.declName    = idFromName n
                      , Core.declAccess  = Core.private
                      , Core.valueEnc    = Nothing
                      , Core.valueValue  =
                          foldr Core.Lam
                              ( let_
                                  nextClauseId (patternMatchFail "pattern binding" _rangeIself)
                                  _righthandsideIcore
                              )
                              _dictionaries
                      , Core.declCustoms = toplevelType n _lhsIimportEnv _lhsIisTopLevel
                      }
                 ]
              _ ->
                  Core.DeclValue
                      { Core.declName    = patBindId
                      , Core.declAccess  = Core.private
                      , Core.valueEnc    = Nothing
                      , Core.valueValue  =
                          let_
                              nextClauseId (patternMatchFail "pattern binding" _rangeIself)
                              _righthandsideIcore
                      , Core.declCustoms = [custom "type" "patternbinding"]
                      }
                  :
                  [ Core.DeclValue
                      { Core.declName    = idFromName v
                      , Core.declAccess  = Core.private
                      , Core.valueEnc    = Nothing
                      , Core.valueValue  =
                          (let_ nextClauseId (patternMatchFail "pattern binding" _rangeIself)
                              (patternToCore (patBindId, _patternIself) (Core.Var (idFromName v)))
                          )
                      , Core.declCustoms = toplevelType v _lhsIimportEnv _lhsIisTopLevel
                      }
                  | v <- _patternIvars
                  ]
                  where
                      patBindId = idFromString ("patBind$" ++ show _lhsIpatBindNr)
   {-# INLINE rule120 #-}
   rule120 = \ ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ((_righthandsideIself) :: RightHandSide) ->
     Declaration_PatternBinding _rangeIself _patternIself _righthandsideIself
   {-# INLINE rule121 #-}
   rule121 = \ _self ->
     _self
   {-# INLINE rule122 #-}
   rule122 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Declaration_TypeSignature #-}
sem_Declaration_TypeSignature :: T_Range  -> T_Names  -> T_Type  -> T_Declaration 
sem_Declaration_TypeSignature arg_range_ arg_names_ arg_type_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _namesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_names_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _namesInames _namesIself) = inv_Names_s116 _namesX116 (T_Names_vIn115 )
         (T_Type_vOut163 _typeIself) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule123  ()
         _self = rule124 _namesIself _rangeIself _typeIself
         _lhsOself :: Declaration
         _lhsOself = rule125 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule126 _lhsIpatBindNr
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule123 #-}
   rule123 = \  (_ :: ()) ->
                                         []
   {-# INLINE rule124 #-}
   rule124 = \ ((_namesIself) :: Names) ((_rangeIself) :: Range) ((_typeIself) :: Type) ->
     Declaration_TypeSignature _rangeIself _namesIself _typeIself
   {-# INLINE rule125 #-}
   rule125 = \ _self ->
     _self
   {-# INLINE rule126 #-}
   rule126 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr
{-# NOINLINE sem_Declaration_Fixity #-}
sem_Declaration_Fixity :: T_Range  -> T_Fixity  -> T_MaybeInt  -> T_Names  -> T_Declaration 
sem_Declaration_Fixity arg_range_ arg_fixity_ arg_priority_ arg_operators_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _fixityX53 = Control.Monad.Identity.runIdentity (attach_T_Fixity (arg_fixity_))
         _priorityX101 = Control.Monad.Identity.runIdentity (attach_T_MaybeInt (arg_priority_))
         _operatorsX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_operators_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Fixity_vOut52 _fixityIself) = inv_Fixity_s53 _fixityX53 (T_Fixity_vIn52 )
         (T_MaybeInt_vOut100 _priorityIself) = inv_MaybeInt_s101 _priorityX101 (T_MaybeInt_vIn100 )
         (T_Names_vOut115 _operatorsInames _operatorsIself) = inv_Names_s116 _operatorsX116 (T_Names_vIn115 )
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule127 _fixityIself _operatorsIself _priorityIself
         _self = rule128 _fixityIself _operatorsIself _priorityIself _rangeIself
         _lhsOself :: Declaration
         _lhsOself = rule129 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule130 _lhsIpatBindNr
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule127 #-}
   rule127 = \ ((_fixityIself) :: Fixity) ((_operatorsIself) :: Names) ((_priorityIself) :: MaybeInt) ->
          map
              ( ( \n ->
                  Core.DeclCustom
                      { Core.declName    = idFromString n
                      , Core.declAccess  = Core.private
                      , Core.declKind    = (Core.DeclKindCustom . idFromString) "infix"
                      , Core.declCustoms =
                          [ Core.CustomInt
                               ( case _priorityIself of
                                    MaybeInt_Just i  -> i
                                    MaybeInt_Nothing -> 9 )
                          , (Core.CustomBytes . bytesFromString)
                                ( case _fixityIself of
                                     Fixity_Infixr _ -> "right"
                                     Fixity_Infixl _ -> "left"
                                     Fixity_Infix  _ -> "none"
                                )
                          ]
                      }
                )
                .
                getNameName
              )
              _operatorsIself
   {-# INLINE rule128 #-}
   rule128 = \ ((_fixityIself) :: Fixity) ((_operatorsIself) :: Names) ((_priorityIself) :: MaybeInt) ((_rangeIself) :: Range) ->
     Declaration_Fixity _rangeIself _fixityIself _priorityIself _operatorsIself
   {-# INLINE rule129 #-}
   rule129 = \ _self ->
     _self
   {-# INLINE rule130 #-}
   rule130 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr
{-# NOINLINE sem_Declaration_Empty #-}
sem_Declaration_Empty :: T_Range  -> T_Declaration 
sem_Declaration_Empty arg_range_ = T_Declaration (return st29) where
   {-# NOINLINE st29 #-}
   st29 = let
      v28 :: T_Declaration_v28 
      v28 = \ (T_Declaration_vIn28 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule131  ()
         _self = rule132 _rangeIself
         _lhsOself :: Declaration
         _lhsOself = rule133 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule134 _lhsIpatBindNr
         __result_ = T_Declaration_vOut28 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declaration_s29 v28
   {-# INLINE rule131 #-}
   rule131 = \  (_ :: ()) ->
                                         internalError "ToCoreDecl" "Declaration" "empty declarations not supported"
   {-# INLINE rule132 #-}
   rule132 = \ ((_rangeIself) :: Range) ->
     Declaration_Empty _rangeIself
   {-# INLINE rule133 #-}
   rule133 = \ _self ->
     _self
   {-# INLINE rule134 #-}
   rule134 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr

-- Declarations ------------------------------------------------
-- wrapper
data Inh_Declarations  = Inh_Declarations { dictionaryEnv_Inh_Declarations :: (DictionaryEnvironment), importEnv_Inh_Declarations :: (ImportEnvironment), isTopLevel_Inh_Declarations :: (Bool), patBindNr_Inh_Declarations :: (Int) }
data Syn_Declarations  = Syn_Declarations { decls_Syn_Declarations :: ( [CoreDecl] ), patBindNr_Syn_Declarations :: (Int), self_Syn_Declarations :: (Declarations) }
{-# INLINABLE wrap_Declarations #-}
wrap_Declarations :: T_Declarations  -> Inh_Declarations  -> (Syn_Declarations )
wrap_Declarations (T_Declarations act) (Inh_Declarations _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Declarations_vIn31 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr
        (T_Declarations_vOut31 _lhsOdecls _lhsOpatBindNr _lhsOself) <- return (inv_Declarations_s32 sem arg)
        return (Syn_Declarations _lhsOdecls _lhsOpatBindNr _lhsOself)
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
data T_Declarations_vIn31  = T_Declarations_vIn31 (DictionaryEnvironment) (ImportEnvironment) (Bool) (Int)
data T_Declarations_vOut31  = T_Declarations_vOut31 ( [CoreDecl] ) (Int) (Declarations)
{-# NOINLINE sem_Declarations_Cons #-}
sem_Declarations_Cons :: T_Declaration  -> T_Declarations  -> T_Declarations 
sem_Declarations_Cons arg_hd_ arg_tl_ = T_Declarations (return st32) where
   {-# NOINLINE st32 #-}
   st32 = let
      v31 :: T_Declarations_v31 
      v31 = \ (T_Declarations_vIn31 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _hdX29 = Control.Monad.Identity.runIdentity (attach_T_Declaration (arg_hd_))
         _tlX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_tl_))
         (T_Declaration_vOut28 _hdIdecls _hdIpatBindNr _hdIself) = inv_Declaration_s29 _hdX29 (T_Declaration_vIn28 _hdOdictionaryEnv _hdOimportEnv _hdOisTopLevel _hdOpatBindNr)
         (T_Declarations_vOut31 _tlIdecls _tlIpatBindNr _tlIself) = inv_Declarations_s32 _tlX32 (T_Declarations_vIn31 _tlOdictionaryEnv _tlOimportEnv _tlOisTopLevel _tlOpatBindNr)
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule135 _hdIdecls _tlIdecls
         _self = rule136 _hdIself _tlIself
         _lhsOself :: Declarations
         _lhsOself = rule137 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule138 _tlIpatBindNr
         _hdOdictionaryEnv = rule139 _lhsIdictionaryEnv
         _hdOimportEnv = rule140 _lhsIimportEnv
         _hdOisTopLevel = rule141 _lhsIisTopLevel
         _hdOpatBindNr = rule142 _lhsIpatBindNr
         _tlOdictionaryEnv = rule143 _lhsIdictionaryEnv
         _tlOimportEnv = rule144 _lhsIimportEnv
         _tlOisTopLevel = rule145 _lhsIisTopLevel
         _tlOpatBindNr = rule146 _hdIpatBindNr
         __result_ = T_Declarations_vOut31 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declarations_s32 v31
   {-# INLINE rule135 #-}
   rule135 = \ ((_hdIdecls) ::  [CoreDecl] ) ((_tlIdecls) ::  [CoreDecl] ) ->
     _hdIdecls  ++  _tlIdecls
   {-# INLINE rule136 #-}
   rule136 = \ ((_hdIself) :: Declaration) ((_tlIself) :: Declarations) ->
     (:) _hdIself _tlIself
   {-# INLINE rule137 #-}
   rule137 = \ _self ->
     _self
   {-# INLINE rule138 #-}
   rule138 = \ ((_tlIpatBindNr) :: Int) ->
     _tlIpatBindNr
   {-# INLINE rule139 #-}
   rule139 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule140 #-}
   rule140 = \ ((_lhsIimportEnv) :: ImportEnvironment) ->
     _lhsIimportEnv
   {-# INLINE rule141 #-}
   rule141 = \ ((_lhsIisTopLevel) :: Bool) ->
     _lhsIisTopLevel
   {-# INLINE rule142 #-}
   rule142 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr
   {-# INLINE rule143 #-}
   rule143 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule144 #-}
   rule144 = \ ((_lhsIimportEnv) :: ImportEnvironment) ->
     _lhsIimportEnv
   {-# INLINE rule145 #-}
   rule145 = \ ((_lhsIisTopLevel) :: Bool) ->
     _lhsIisTopLevel
   {-# INLINE rule146 #-}
   rule146 = \ ((_hdIpatBindNr) :: Int) ->
     _hdIpatBindNr
{-# NOINLINE sem_Declarations_Nil #-}
sem_Declarations_Nil ::  T_Declarations 
sem_Declarations_Nil  = T_Declarations (return st32) where
   {-# NOINLINE st32 #-}
   st32 = let
      v31 :: T_Declarations_v31 
      v31 = \ (T_Declarations_vIn31 _lhsIdictionaryEnv _lhsIimportEnv _lhsIisTopLevel _lhsIpatBindNr) -> ( let
         _lhsOdecls ::  [CoreDecl] 
         _lhsOdecls = rule147  ()
         _self = rule148  ()
         _lhsOself :: Declarations
         _lhsOself = rule149 _self
         _lhsOpatBindNr :: Int
         _lhsOpatBindNr = rule150 _lhsIpatBindNr
         __result_ = T_Declarations_vOut31 _lhsOdecls _lhsOpatBindNr _lhsOself
         in __result_ )
     in C_Declarations_s32 v31
   {-# INLINE rule147 #-}
   rule147 = \  (_ :: ()) ->
     []
   {-# INLINE rule148 #-}
   rule148 = \  (_ :: ()) ->
     []
   {-# INLINE rule149 #-}
   rule149 = \ _self ->
     _self
   {-# INLINE rule150 #-}
   rule150 = \ ((_lhsIpatBindNr) :: Int) ->
     _lhsIpatBindNr

-- Export ------------------------------------------------------
-- wrapper
data Inh_Export  = Inh_Export {  }
data Syn_Export  = Syn_Export { cons_Syn_Export :: (IdSet), mods_Syn_Export :: (IdSet), self_Syn_Export :: (Export), types_Syn_Export :: (IdSet), values_Syn_Export :: (IdSet) }
{-# INLINABLE wrap_Export #-}
wrap_Export :: T_Export  -> Inh_Export  -> (Syn_Export )
wrap_Export (T_Export act) (Inh_Export ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Export_vIn34 
        (T_Export_vOut34 _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues) <- return (inv_Export_s35 sem arg)
        return (Syn_Export _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues)
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
data T_Export_vIn34  = T_Export_vIn34 
data T_Export_vOut34  = T_Export_vOut34 (IdSet) (IdSet) (Export) (IdSet) (IdSet)
{-# NOINLINE sem_Export_Variable #-}
sem_Export_Variable :: T_Range  -> T_Name  -> T_Export 
sem_Export_Variable arg_range_ arg_name_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOvalues :: IdSet
         _lhsOvalues = rule151 _nameIself
         _lhsOtypes :: IdSet
         _lhsOtypes = rule152  ()
         _lhsOcons :: IdSet
         _lhsOcons = rule153  ()
         _lhsOmods :: IdSet
         _lhsOmods = rule154  ()
         _self = rule155 _nameIself _rangeIself
         _lhsOself :: Export
         _lhsOself = rule156 _self
         __result_ = T_Export_vOut34 _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule151 #-}
   rule151 = \ ((_nameIself) :: Name) ->
                                            singleSet (idFromName _nameIself)
   {-# INLINE rule152 #-}
   rule152 = \  (_ :: ()) ->
                                            emptySet
   {-# INLINE rule153 #-}
   rule153 = \  (_ :: ()) ->
                                            emptySet
   {-# INLINE rule154 #-}
   rule154 = \  (_ :: ()) ->
                                            emptySet
   {-# INLINE rule155 #-}
   rule155 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Export_Variable _rangeIself _nameIself
   {-# INLINE rule156 #-}
   rule156 = \ _self ->
     _self
{-# NOINLINE sem_Export_TypeOrClass #-}
sem_Export_TypeOrClass :: T_Range  -> T_Name  -> T_MaybeNames  -> T_Export 
sem_Export_TypeOrClass arg_range_ arg_name_ arg_names_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _namesX107 = Control.Monad.Identity.runIdentity (attach_T_MaybeNames (arg_names_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_MaybeNames_vOut106 _namesInames _namesIself) = inv_MaybeNames_s107 _namesX107 (T_MaybeNames_vIn106 )
         _lhsOvalues :: IdSet
         _lhsOvalues = rule157  ()
         _lhsOtypes :: IdSet
         _lhsOtypes = rule158 _nameIself
         _lhsOcons :: IdSet
         _lhsOcons = rule159 _namesInames
         _lhsOmods :: IdSet
         _lhsOmods = rule160  ()
         _self = rule161 _nameIself _namesIself _rangeIself
         _lhsOself :: Export
         _lhsOself = rule162 _self
         __result_ = T_Export_vOut34 _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule157 #-}
   rule157 = \  (_ :: ()) ->
                                            emptySet
   {-# INLINE rule158 #-}
   rule158 = \ ((_nameIself) :: Name) ->
                                            singleSet (idFromName _nameIself)
   {-# INLINE rule159 #-}
   rule159 = \ ((_namesInames) ::  Maybe [Name] ) ->
                                            setFromList (maybe [] (map idFromName) _namesInames)
   {-# INLINE rule160 #-}
   rule160 = \  (_ :: ()) ->
                                            emptySet
   {-# INLINE rule161 #-}
   rule161 = \ ((_nameIself) :: Name) ((_namesIself) :: MaybeNames) ((_rangeIself) :: Range) ->
     Export_TypeOrClass _rangeIself _nameIself _namesIself
   {-# INLINE rule162 #-}
   rule162 = \ _self ->
     _self
{-# NOINLINE sem_Export_TypeOrClassComplete #-}
sem_Export_TypeOrClassComplete :: T_Range  -> T_Name  -> T_Export 
sem_Export_TypeOrClassComplete arg_range_ arg_name_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOvalues :: IdSet
         _lhsOvalues = rule163  ()
         _lhsOtypes :: IdSet
         _lhsOtypes = rule164  ()
         _lhsOcons :: IdSet
         _lhsOcons = rule165  ()
         _lhsOmods :: IdSet
         _lhsOmods = rule166  ()
         _self = rule167 _nameIself _rangeIself
         _lhsOself :: Export
         _lhsOself = rule168 _self
         __result_ = T_Export_vOut34 _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule163 #-}
   rule163 = \  (_ :: ()) ->
                                            internalError "ToCoreModule" "exports.tocc" "Unsupported export declaration"
   {-# INLINE rule164 #-}
   rule164 = \  (_ :: ()) ->
                                            internalError "ToCoreModule" "exports.tocc" "Unsupported export declaration"
   {-# INLINE rule165 #-}
   rule165 = \  (_ :: ()) ->
                                            internalError "ToCoreModule" "exports.tocc" "Unsupported export declaration"
   {-# INLINE rule166 #-}
   rule166 = \  (_ :: ()) ->
                                            internalError "ToCoreModule" "exports.tocc" "Unsupported export declaration"
   {-# INLINE rule167 #-}
   rule167 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Export_TypeOrClassComplete _rangeIself _nameIself
   {-# INLINE rule168 #-}
   rule168 = \ _self ->
     _self
{-# NOINLINE sem_Export_Module #-}
sem_Export_Module :: T_Range  -> T_Name  -> T_Export 
sem_Export_Module arg_range_ arg_name_ = T_Export (return st35) where
   {-# NOINLINE st35 #-}
   st35 = let
      v34 :: T_Export_v34 
      v34 = \ (T_Export_vIn34 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOvalues :: IdSet
         _lhsOvalues = rule169  ()
         _lhsOtypes :: IdSet
         _lhsOtypes = rule170  ()
         _lhsOcons :: IdSet
         _lhsOcons = rule171  ()
         _lhsOmods :: IdSet
         _lhsOmods = rule172 _nameIself
         _self = rule173 _nameIself _rangeIself
         _lhsOself :: Export
         _lhsOself = rule174 _self
         __result_ = T_Export_vOut34 _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues
         in __result_ )
     in C_Export_s35 v34
   {-# INLINE rule169 #-}
   rule169 = \  (_ :: ()) ->
                                            emptySet
   {-# INLINE rule170 #-}
   rule170 = \  (_ :: ()) ->
                                            emptySet
   {-# INLINE rule171 #-}
   rule171 = \  (_ :: ()) ->
                                            emptySet
   {-# INLINE rule172 #-}
   rule172 = \ ((_nameIself) :: Name) ->
                                            singleSet (idFromName _nameIself)
   {-# INLINE rule173 #-}
   rule173 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Export_Module _rangeIself _nameIself
   {-# INLINE rule174 #-}
   rule174 = \ _self ->
     _self

-- Exports -----------------------------------------------------
-- wrapper
data Inh_Exports  = Inh_Exports {  }
data Syn_Exports  = Syn_Exports { cons_Syn_Exports :: (IdSet), mods_Syn_Exports :: (IdSet), self_Syn_Exports :: (Exports), types_Syn_Exports :: (IdSet), values_Syn_Exports :: (IdSet) }
{-# INLINABLE wrap_Exports #-}
wrap_Exports :: T_Exports  -> Inh_Exports  -> (Syn_Exports )
wrap_Exports (T_Exports act) (Inh_Exports ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Exports_vIn37 
        (T_Exports_vOut37 _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues) <- return (inv_Exports_s38 sem arg)
        return (Syn_Exports _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues)
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
data T_Exports_vIn37  = T_Exports_vIn37 
data T_Exports_vOut37  = T_Exports_vOut37 (IdSet) (IdSet) (Exports) (IdSet) (IdSet)
{-# NOINLINE sem_Exports_Cons #-}
sem_Exports_Cons :: T_Export  -> T_Exports  -> T_Exports 
sem_Exports_Cons arg_hd_ arg_tl_ = T_Exports (return st38) where
   {-# NOINLINE st38 #-}
   st38 = let
      v37 :: T_Exports_v37 
      v37 = \ (T_Exports_vIn37 ) -> ( let
         _hdX35 = Control.Monad.Identity.runIdentity (attach_T_Export (arg_hd_))
         _tlX38 = Control.Monad.Identity.runIdentity (attach_T_Exports (arg_tl_))
         (T_Export_vOut34 _hdIcons _hdImods _hdIself _hdItypes _hdIvalues) = inv_Export_s35 _hdX35 (T_Export_vIn34 )
         (T_Exports_vOut37 _tlIcons _tlImods _tlIself _tlItypes _tlIvalues) = inv_Exports_s38 _tlX38 (T_Exports_vIn37 )
         _lhsOcons :: IdSet
         _lhsOcons = rule175 _hdIcons _tlIcons
         _lhsOmods :: IdSet
         _lhsOmods = rule176 _hdImods _tlImods
         _lhsOtypes :: IdSet
         _lhsOtypes = rule177 _hdItypes _tlItypes
         _lhsOvalues :: IdSet
         _lhsOvalues = rule178 _hdIvalues _tlIvalues
         _self = rule179 _hdIself _tlIself
         _lhsOself :: Exports
         _lhsOself = rule180 _self
         __result_ = T_Exports_vOut37 _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues
         in __result_ )
     in C_Exports_s38 v37
   {-# INLINE rule175 #-}
   rule175 = \ ((_hdIcons) :: IdSet) ((_tlIcons) :: IdSet) ->
     _hdIcons  `unionSet`  _tlIcons
   {-# INLINE rule176 #-}
   rule176 = \ ((_hdImods) :: IdSet) ((_tlImods) :: IdSet) ->
     _hdImods  `unionSet`  _tlImods
   {-# INLINE rule177 #-}
   rule177 = \ ((_hdItypes) :: IdSet) ((_tlItypes) :: IdSet) ->
     _hdItypes  `unionSet`  _tlItypes
   {-# INLINE rule178 #-}
   rule178 = \ ((_hdIvalues) :: IdSet) ((_tlIvalues) :: IdSet) ->
     _hdIvalues  `unionSet`  _tlIvalues
   {-# INLINE rule179 #-}
   rule179 = \ ((_hdIself) :: Export) ((_tlIself) :: Exports) ->
     (:) _hdIself _tlIself
   {-# INLINE rule180 #-}
   rule180 = \ _self ->
     _self
{-# NOINLINE sem_Exports_Nil #-}
sem_Exports_Nil ::  T_Exports 
sem_Exports_Nil  = T_Exports (return st38) where
   {-# NOINLINE st38 #-}
   st38 = let
      v37 :: T_Exports_v37 
      v37 = \ (T_Exports_vIn37 ) -> ( let
         _lhsOcons :: IdSet
         _lhsOcons = rule181  ()
         _lhsOmods :: IdSet
         _lhsOmods = rule182  ()
         _lhsOtypes :: IdSet
         _lhsOtypes = rule183  ()
         _lhsOvalues :: IdSet
         _lhsOvalues = rule184  ()
         _self = rule185  ()
         _lhsOself :: Exports
         _lhsOself = rule186 _self
         __result_ = T_Exports_vOut37 _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues
         in __result_ )
     in C_Exports_s38 v37
   {-# INLINE rule181 #-}
   rule181 = \  (_ :: ()) ->
     emptySet
   {-# INLINE rule182 #-}
   rule182 = \  (_ :: ()) ->
     emptySet
   {-# INLINE rule183 #-}
   rule183 = \  (_ :: ()) ->
     emptySet
   {-# INLINE rule184 #-}
   rule184 = \  (_ :: ()) ->
     emptySet
   {-# INLINE rule185 #-}
   rule185 = \  (_ :: ()) ->
     []
   {-# INLINE rule186 #-}
   rule186 = \ _self ->
     _self

-- Expression --------------------------------------------------
-- wrapper
data Inh_Expression  = Inh_Expression { dictionaryEnv_Inh_Expression :: (DictionaryEnvironment) }
data Syn_Expression  = Syn_Expression { core_Syn_Expression :: ( Core.Expr ), self_Syn_Expression :: (Expression) }
{-# INLINABLE wrap_Expression #-}
wrap_Expression :: T_Expression  -> Inh_Expression  -> (Syn_Expression )
wrap_Expression (T_Expression act) (Inh_Expression _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Expression_vIn40 _lhsIdictionaryEnv
        (T_Expression_vOut40 _lhsOcore _lhsOself) <- return (inv_Expression_s41 sem arg)
        return (Syn_Expression _lhsOcore _lhsOself)
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
data T_Expression_vIn40  = T_Expression_vIn40 (DictionaryEnvironment)
data T_Expression_vOut40  = T_Expression_vOut40 ( Core.Expr ) (Expression)
{-# NOINLINE sem_Expression_Hole #-}
sem_Expression_Hole :: T_Range  -> (Integer) -> T_Expression 
sem_Expression_Hole arg_range_ arg_id_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule187  ()
         _self = rule188 _rangeIself arg_id_
         _lhsOself :: Expression
         _lhsOself = rule189 _self
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule187 #-}
   rule187 = \  (_ :: ()) ->
                                      Core.Var (idFromString "undefined")
   {-# INLINE rule188 #-}
   rule188 = \ ((_rangeIself) :: Range) id_ ->
     Expression_Hole _rangeIself id_
   {-# INLINE rule189 #-}
   rule189 = \ _self ->
     _self
{-# NOINLINE sem_Expression_Feedback #-}
sem_Expression_Feedback :: T_Range  -> (String) -> T_Expression  -> T_Expression 
sem_Expression_Feedback arg_range_ arg_feedback_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _self = rule190 _expressionIself _rangeIself arg_feedback_
         _lhsOself :: Expression
         _lhsOself = rule191 _self
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule192 _expressionIcore
         _expressionOdictionaryEnv = rule193 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule190 #-}
   rule190 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) feedback_ ->
     Expression_Feedback _rangeIself feedback_ _expressionIself
   {-# INLINE rule191 #-}
   rule191 = \ _self ->
     _self
   {-# INLINE rule192 #-}
   rule192 = \ ((_expressionIcore) ::  Core.Expr ) ->
     _expressionIcore
   {-# INLINE rule193 #-}
   rule193 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_MustUse #-}
sem_Expression_MustUse :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_MustUse arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _self = rule194 _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule195 _self
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule196 _expressionIcore
         _expressionOdictionaryEnv = rule197 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule194 #-}
   rule194 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_MustUse _rangeIself _expressionIself
   {-# INLINE rule195 #-}
   rule195 = \ _self ->
     _self
   {-# INLINE rule196 #-}
   rule196 = \ ((_expressionIcore) ::  Core.Expr ) ->
     _expressionIcore
   {-# INLINE rule197 #-}
   rule197 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_Literal #-}
sem_Expression_Literal :: T_Range  -> T_Literal  -> T_Expression 
sem_Expression_Literal arg_range_ arg_literal_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalIcore _literalIself) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 )
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule198 _literalIcore
         _self = rule199 _literalIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule200 _self
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule198 #-}
   rule198 = \ ((_literalIcore) ::  Core.Expr ) ->
                                      _literalIcore
   {-# INLINE rule199 #-}
   rule199 = \ ((_literalIself) :: Literal) ((_rangeIself) :: Range) ->
     Expression_Literal _rangeIself _literalIself
   {-# INLINE rule200 #-}
   rule200 = \ _self ->
     _self
{-# NOINLINE sem_Expression_Variable #-}
sem_Expression_Variable :: T_Range  -> T_Name  -> T_Expression 
sem_Expression_Variable arg_range_ arg_name_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule201 _lhsIdictionaryEnv _nameIself
         _self = rule202 _nameIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule203 _self
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule201 #-}
   rule201 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ((_nameIself) :: Name) ->
                                      insertDictionaries _nameIself _lhsIdictionaryEnv
   {-# INLINE rule202 #-}
   rule202 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Expression_Variable _rangeIself _nameIself
   {-# INLINE rule203 #-}
   rule203 = \ _self ->
     _self
{-# NOINLINE sem_Expression_Constructor #-}
sem_Expression_Constructor :: T_Range  -> T_Name  -> T_Expression 
sem_Expression_Constructor arg_range_ arg_name_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule204 _nameIself
         _self = rule205 _nameIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule206 _self
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule204 #-}
   rule204 = \ ((_nameIself) :: Name) ->
                                      Core.Con (Core.ConId (idFromName _nameIself))
   {-# INLINE rule205 #-}
   rule205 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Expression_Constructor _rangeIself _nameIself
   {-# INLINE rule206 #-}
   rule206 = \ _self ->
     _self
{-# NOINLINE sem_Expression_Parenthesized #-}
sem_Expression_Parenthesized :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_Parenthesized arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule207 _expressionIcore
         _self = rule208 _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule209 _self
         _expressionOdictionaryEnv = rule210 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule207 #-}
   rule207 = \ ((_expressionIcore) ::  Core.Expr ) ->
                                      _expressionIcore
   {-# INLINE rule208 #-}
   rule208 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_Parenthesized _rangeIself _expressionIself
   {-# INLINE rule209 #-}
   rule209 = \ _self ->
     _self
   {-# INLINE rule210 #-}
   rule210 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_NormalApplication #-}
sem_Expression_NormalApplication :: T_Range  -> T_Expression  -> T_Expressions  -> T_Expression 
sem_Expression_NormalApplication arg_range_ arg_function_ arg_arguments_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _functionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_function_))
         _argumentsX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_arguments_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _functionIcore _functionIself) = inv_Expression_s41 _functionX41 (T_Expression_vIn40 _functionOdictionaryEnv)
         (T_Expressions_vOut43 _argumentsIcore _argumentsIself) = inv_Expressions_s44 _argumentsX44 (T_Expressions_vIn43 _argumentsOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule211 _argumentsIcore _functionIcore
         _self = rule212 _argumentsIself _functionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule213 _self
         _functionOdictionaryEnv = rule214 _lhsIdictionaryEnv
         _argumentsOdictionaryEnv = rule215 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule211 #-}
   rule211 = \ ((_argumentsIcore) ::  [Core.Expr] ) ((_functionIcore) ::  Core.Expr ) ->
                                      foldl Core.Ap _functionIcore _argumentsIcore
   {-# INLINE rule212 #-}
   rule212 = \ ((_argumentsIself) :: Expressions) ((_functionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_NormalApplication _rangeIself _functionIself _argumentsIself
   {-# INLINE rule213 #-}
   rule213 = \ _self ->
     _self
   {-# INLINE rule214 #-}
   rule214 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule215 #-}
   rule215 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_InfixApplication #-}
sem_Expression_InfixApplication :: T_Range  -> T_MaybeExpression  -> T_Expression  -> T_MaybeExpression  -> T_Expression 
sem_Expression_InfixApplication arg_range_ arg_leftExpression_ arg_operator_ arg_rightExpression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftExpressionX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_leftExpression_))
         _operatorX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_operator_))
         _rightExpressionX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_rightExpression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_MaybeExpression_vOut94 _leftExpressionIcore _leftExpressionIself) = inv_MaybeExpression_s95 _leftExpressionX95 (T_MaybeExpression_vIn94 _leftExpressionOdictionaryEnv)
         (T_Expression_vOut40 _operatorIcore _operatorIself) = inv_Expression_s41 _operatorX41 (T_Expression_vIn40 _operatorOdictionaryEnv)
         (T_MaybeExpression_vOut94 _rightExpressionIcore _rightExpressionIself) = inv_MaybeExpression_s95 _rightExpressionX95 (T_MaybeExpression_vIn94 _rightExpressionOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule216 _leftExpressionIcore _operatorIcore _rightExpressionIcore
         _self = rule217 _leftExpressionIself _operatorIself _rangeIself _rightExpressionIself
         _lhsOself :: Expression
         _lhsOself = rule218 _self
         _leftExpressionOdictionaryEnv = rule219 _lhsIdictionaryEnv
         _operatorOdictionaryEnv = rule220 _lhsIdictionaryEnv
         _rightExpressionOdictionaryEnv = rule221 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule216 #-}
   rule216 = \ ((_leftExpressionIcore) ::  Maybe Core.Expr ) ((_operatorIcore) ::  Core.Expr ) ((_rightExpressionIcore) ::  Maybe Core.Expr ) ->
          case (_leftExpressionIcore, _rightExpressionIcore) of
              (Nothing, Nothing) -> _operatorIcore
              (Just l , Nothing) -> Core.Ap _operatorIcore l
              (Nothing, Just r ) -> Core.Lam parameterId
                                      (foldl Core.Ap _operatorIcore [Core.Var parameterId, r])
              (Just l , Just r ) -> foldl Core.Ap _operatorIcore [l,r]
   {-# INLINE rule217 #-}
   rule217 = \ ((_leftExpressionIself) :: MaybeExpression) ((_operatorIself) :: Expression) ((_rangeIself) :: Range) ((_rightExpressionIself) :: MaybeExpression) ->
     Expression_InfixApplication _rangeIself _leftExpressionIself _operatorIself _rightExpressionIself
   {-# INLINE rule218 #-}
   rule218 = \ _self ->
     _self
   {-# INLINE rule219 #-}
   rule219 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule220 #-}
   rule220 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule221 #-}
   rule221 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_If #-}
sem_Expression_If :: T_Range  -> T_Expression  -> T_Expression  -> T_Expression  -> T_Expression 
sem_Expression_If arg_range_ arg_guardExpression_ arg_thenExpression_ arg_elseExpression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardExpressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_guardExpression_))
         _thenExpressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_thenExpression_))
         _elseExpressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_elseExpression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _guardExpressionIcore _guardExpressionIself) = inv_Expression_s41 _guardExpressionX41 (T_Expression_vIn40 _guardExpressionOdictionaryEnv)
         (T_Expression_vOut40 _thenExpressionIcore _thenExpressionIself) = inv_Expression_s41 _thenExpressionX41 (T_Expression_vIn40 _thenExpressionOdictionaryEnv)
         (T_Expression_vOut40 _elseExpressionIcore _elseExpressionIself) = inv_Expression_s41 _elseExpressionX41 (T_Expression_vIn40 _elseExpressionOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule222 _elseExpressionIcore _guardExpressionIcore _thenExpressionIcore
         _self = rule223 _elseExpressionIself _guardExpressionIself _rangeIself _thenExpressionIself
         _lhsOself :: Expression
         _lhsOself = rule224 _self
         _guardExpressionOdictionaryEnv = rule225 _lhsIdictionaryEnv
         _thenExpressionOdictionaryEnv = rule226 _lhsIdictionaryEnv
         _elseExpressionOdictionaryEnv = rule227 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule222 #-}
   rule222 = \ ((_elseExpressionIcore) ::  Core.Expr ) ((_guardExpressionIcore) ::  Core.Expr ) ((_thenExpressionIcore) ::  Core.Expr ) ->
          if_ _guardExpressionIcore _thenExpressionIcore _elseExpressionIcore
   {-# INLINE rule223 #-}
   rule223 = \ ((_elseExpressionIself) :: Expression) ((_guardExpressionIself) :: Expression) ((_rangeIself) :: Range) ((_thenExpressionIself) :: Expression) ->
     Expression_If _rangeIself _guardExpressionIself _thenExpressionIself _elseExpressionIself
   {-# INLINE rule224 #-}
   rule224 = \ _self ->
     _self
   {-# INLINE rule225 #-}
   rule225 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule226 #-}
   rule226 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule227 #-}
   rule227 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_Lambda #-}
sem_Expression_Lambda :: T_Range  -> T_Patterns  -> T_Expression  -> T_Expression 
sem_Expression_Lambda arg_range_ arg_patterns_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Patterns_vOut121 _patternsIlength _patternsIself _patternsIvars) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule228 _expressionIcore _patternsIlength _patternsIself _rangeIself
         _self = rule229 _expressionIself _patternsIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule230 _self
         _expressionOdictionaryEnv = rule231 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule228 #-}
   rule228 = \ ((_expressionIcore) ::  Core.Expr ) ((_patternsIlength) :: Int) ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
          let ids = freshIds "u$" _patternsIlength
          in let_ nextClauseId (patternMatchFail "lambda expression" _rangeIself)
              (foldr
                  Core.Lam
                  (patternsToCore
                      (zip ids _patternsIself)
                      _expressionIcore
                  )
                  ids
              )
   {-# INLINE rule229 #-}
   rule229 = \ ((_expressionIself) :: Expression) ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     Expression_Lambda _rangeIself _patternsIself _expressionIself
   {-# INLINE rule230 #-}
   rule230 = \ _self ->
     _self
   {-# INLINE rule231 #-}
   rule231 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_Case #-}
sem_Expression_Case :: T_Range  -> T_Expression  -> T_Alternatives  -> T_Expression 
sem_Expression_Case arg_range_ arg_expression_ arg_alternatives_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _alternativesX5 = Control.Monad.Identity.runIdentity (attach_T_Alternatives (arg_alternatives_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         (T_Alternatives_vOut4 _alternativesIcore _alternativesIself) = inv_Alternatives_s5 _alternativesX5 (T_Alternatives_vIn4 _alternativesOcaseRange _alternativesOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule232 _alternativesIcore _expressionIcore
         _alternativesOcaseRange = rule233 _rangeIself
         _self = rule234 _alternativesIself _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule235 _self
         _expressionOdictionaryEnv = rule236 _lhsIdictionaryEnv
         _alternativesOdictionaryEnv = rule237 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule232 #-}
   rule232 = \ ((_alternativesIcore) ::  Core.Expr ) ((_expressionIcore) ::  Core.Expr ) ->
                                      let_ caseExprId _expressionIcore _alternativesIcore
   {-# INLINE rule233 #-}
   rule233 = \ ((_rangeIself) :: Range) ->
                                                    _rangeIself
   {-# INLINE rule234 #-}
   rule234 = \ ((_alternativesIself) :: Alternatives) ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_Case _rangeIself _expressionIself _alternativesIself
   {-# INLINE rule235 #-}
   rule235 = \ _self ->
     _self
   {-# INLINE rule236 #-}
   rule236 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule237 #-}
   rule237 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_Let #-}
sem_Expression_Let :: T_Range  -> T_Declarations  -> T_Expression  -> T_Expression 
sem_Expression_Let arg_range_ arg_declarations_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Declarations_vOut31 _declarationsIdecls _declarationsIpatBindNr _declarationsIself) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 _declarationsOdictionaryEnv _declarationsOimportEnv _declarationsOisTopLevel _declarationsOpatBindNr)
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _importEnv = rule238  ()
         _declarationsOpatBindNr = rule239  ()
         _declarationsOisTopLevel = rule240  ()
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule241 _declarationsIdecls _expressionIcore
         _self = rule242 _declarationsIself _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule243 _self
         _declarationsOdictionaryEnv = rule244 _lhsIdictionaryEnv
         _declarationsOimportEnv = rule245 _importEnv
         _expressionOdictionaryEnv = rule246 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule238 #-}
   rule238 = \  (_ :: ()) ->
                                               internalError "CodeGeneration.ag" "Expression.Let" ""
   {-# INLINE rule239 #-}
   rule239 = \  (_ :: ()) ->
                                                    0
   {-# INLINE rule240 #-}
   rule240 = \  (_ :: ()) ->
                                                     False
   {-# INLINE rule241 #-}
   rule241 = \ ((_declarationsIdecls) ::  [CoreDecl] ) ((_expressionIcore) ::  Core.Expr ) ->
          letrec_ _declarationsIdecls _expressionIcore
   {-# INLINE rule242 #-}
   rule242 = \ ((_declarationsIself) :: Declarations) ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_Let _rangeIself _declarationsIself _expressionIself
   {-# INLINE rule243 #-}
   rule243 = \ _self ->
     _self
   {-# INLINE rule244 #-}
   rule244 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule245 #-}
   rule245 = \ _importEnv ->
     _importEnv
   {-# INLINE rule246 #-}
   rule246 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_Do #-}
sem_Expression_Do :: T_Range  -> T_Statements  -> T_Expression 
sem_Expression_Do arg_range_ arg_statements_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _statementsX158 = Control.Monad.Identity.runIdentity (attach_T_Statements (arg_statements_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Statements_vOut157 _statementsIcore _statementsIself) = inv_Statements_s158 _statementsX158 (T_Statements_vIn157 _statementsOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule247 _statementsIcore
         _self = rule248 _rangeIself _statementsIself
         _lhsOself :: Expression
         _lhsOself = rule249 _self
         _statementsOdictionaryEnv = rule250 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule247 #-}
   rule247 = \ ((_statementsIcore) ::  [Maybe Core.Expr -> Core.Expr] ) ->
                                      chainCode _statementsIcore
   {-# INLINE rule248 #-}
   rule248 = \ ((_rangeIself) :: Range) ((_statementsIself) :: Statements) ->
     Expression_Do _rangeIself _statementsIself
   {-# INLINE rule249 #-}
   rule249 = \ _self ->
     _self
   {-# INLINE rule250 #-}
   rule250 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_List #-}
sem_Expression_List :: T_Range  -> T_Expressions  -> T_Expression 
sem_Expression_List arg_range_ arg_expressions_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionsX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_expressions_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expressions_vOut43 _expressionsIcore _expressionsIself) = inv_Expressions_s44 _expressionsX44 (T_Expressions_vIn43 _expressionsOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule251 _expressionsIcore
         _self = rule252 _expressionsIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule253 _self
         _expressionsOdictionaryEnv = rule254 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule251 #-}
   rule251 = \ ((_expressionsIcore) ::  [Core.Expr] ) ->
                                      coreList _expressionsIcore
   {-# INLINE rule252 #-}
   rule252 = \ ((_expressionsIself) :: Expressions) ((_rangeIself) :: Range) ->
     Expression_List _rangeIself _expressionsIself
   {-# INLINE rule253 #-}
   rule253 = \ _self ->
     _self
   {-# INLINE rule254 #-}
   rule254 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_Tuple #-}
sem_Expression_Tuple :: T_Range  -> T_Expressions  -> T_Expression 
sem_Expression_Tuple arg_range_ arg_expressions_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionsX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_expressions_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expressions_vOut43 _expressionsIcore _expressionsIself) = inv_Expressions_s44 _expressionsX44 (T_Expressions_vIn43 _expressionsOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule255 _expressionsIcore
         _self = rule256 _expressionsIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule257 _self
         _expressionsOdictionaryEnv = rule258 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule255 #-}
   rule255 = \ ((_expressionsIcore) ::  [Core.Expr] ) ->
          foldl
              Core.Ap
              (Core.Con
                  (Core.ConTag
                      (Core.Lit (Core.LitInt 0))
                      (length _expressionsIcore)
                  )
              )
              _expressionsIcore
   {-# INLINE rule256 #-}
   rule256 = \ ((_expressionsIself) :: Expressions) ((_rangeIself) :: Range) ->
     Expression_Tuple _rangeIself _expressionsIself
   {-# INLINE rule257 #-}
   rule257 = \ _self ->
     _self
   {-# INLINE rule258 #-}
   rule258 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_Comprehension #-}
sem_Expression_Comprehension :: T_Range  -> T_Expression  -> T_Qualifiers  -> T_Expression 
sem_Expression_Comprehension arg_range_ arg_expression_ arg_qualifiers_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _qualifiersX131 = Control.Monad.Identity.runIdentity (attach_T_Qualifiers (arg_qualifiers_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         (T_Qualifiers_vOut130 _qualifiersIcore _qualifiersIself) = inv_Qualifiers_s131 _qualifiersX131 (T_Qualifiers_vIn130 _qualifiersOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule259 _expressionIcore _qualifiersIcore
         _self = rule260 _expressionIself _qualifiersIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule261 _self
         _expressionOdictionaryEnv = rule262 _lhsIdictionaryEnv
         _qualifiersOdictionaryEnv = rule263 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule259 #-}
   rule259 = \ ((_expressionIcore) ::  Core.Expr ) ((_qualifiersIcore) ::  [Core.Expr -> Core.Expr] ) ->
          let singleton x = cons x nil
          in foldr ($) (singleton _expressionIcore) _qualifiersIcore
   {-# INLINE rule260 #-}
   rule260 = \ ((_expressionIself) :: Expression) ((_qualifiersIself) :: Qualifiers) ((_rangeIself) :: Range) ->
     Expression_Comprehension _rangeIself _expressionIself _qualifiersIself
   {-# INLINE rule261 #-}
   rule261 = \ _self ->
     _self
   {-# INLINE rule262 #-}
   rule262 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule263 #-}
   rule263 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_Typed #-}
sem_Expression_Typed :: T_Range  -> T_Expression  -> T_Type  -> T_Expression 
sem_Expression_Typed arg_range_ arg_expression_ arg_type_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         (T_Type_vOut163 _typeIself) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule264 _expressionIcore
         _self = rule265 _expressionIself _rangeIself _typeIself
         _lhsOself :: Expression
         _lhsOself = rule266 _self
         _expressionOdictionaryEnv = rule267 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule264 #-}
   rule264 = \ ((_expressionIcore) ::  Core.Expr ) ->
                                      _expressionIcore
   {-# INLINE rule265 #-}
   rule265 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ((_typeIself) :: Type) ->
     Expression_Typed _rangeIself _expressionIself _typeIself
   {-# INLINE rule266 #-}
   rule266 = \ _self ->
     _self
   {-# INLINE rule267 #-}
   rule267 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_RecordConstruction #-}
sem_Expression_RecordConstruction :: T_Range  -> T_Name  -> T_RecordExpressionBindings  -> T_Expression 
sem_Expression_RecordConstruction arg_range_ arg_name_ arg_recordExpressionBindings_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _recordExpressionBindingsX140 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBindings (arg_recordExpressionBindings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_RecordExpressionBindings_vOut139 _recordExpressionBindingsIself) = inv_RecordExpressionBindings_s140 _recordExpressionBindingsX140 (T_RecordExpressionBindings_vIn139 _recordExpressionBindingsOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule268  ()
         _self = rule269 _nameIself _rangeIself _recordExpressionBindingsIself
         _lhsOself :: Expression
         _lhsOself = rule270 _self
         _recordExpressionBindingsOdictionaryEnv = rule271 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule268 #-}
   rule268 = \  (_ :: ()) ->
                                      internalError "ToCoreExpr" "Expression" "records not supported"
   {-# INLINE rule269 #-}
   rule269 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ((_recordExpressionBindingsIself) :: RecordExpressionBindings) ->
     Expression_RecordConstruction _rangeIself _nameIself _recordExpressionBindingsIself
   {-# INLINE rule270 #-}
   rule270 = \ _self ->
     _self
   {-# INLINE rule271 #-}
   rule271 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_RecordUpdate #-}
sem_Expression_RecordUpdate :: T_Range  -> T_Expression  -> T_RecordExpressionBindings  -> T_Expression 
sem_Expression_RecordUpdate arg_range_ arg_expression_ arg_recordExpressionBindings_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _recordExpressionBindingsX140 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBindings (arg_recordExpressionBindings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         (T_RecordExpressionBindings_vOut139 _recordExpressionBindingsIself) = inv_RecordExpressionBindings_s140 _recordExpressionBindingsX140 (T_RecordExpressionBindings_vIn139 _recordExpressionBindingsOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule272  ()
         _self = rule273 _expressionIself _rangeIself _recordExpressionBindingsIself
         _lhsOself :: Expression
         _lhsOself = rule274 _self
         _expressionOdictionaryEnv = rule275 _lhsIdictionaryEnv
         _recordExpressionBindingsOdictionaryEnv = rule276 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule272 #-}
   rule272 = \  (_ :: ()) ->
                                      internalError "ToCoreExpr" "Expression" "records not supported"
   {-# INLINE rule273 #-}
   rule273 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ((_recordExpressionBindingsIself) :: RecordExpressionBindings) ->
     Expression_RecordUpdate _rangeIself _expressionIself _recordExpressionBindingsIself
   {-# INLINE rule274 #-}
   rule274 = \ _self ->
     _self
   {-# INLINE rule275 #-}
   rule275 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule276 #-}
   rule276 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_Enum #-}
sem_Expression_Enum :: T_Range  -> T_Expression  -> T_MaybeExpression  -> T_MaybeExpression  -> T_Expression 
sem_Expression_Enum arg_range_ arg_from_ arg_then_ arg_to_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _fromX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_from_))
         _thenX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_then_))
         _toX95 = Control.Monad.Identity.runIdentity (attach_T_MaybeExpression (arg_to_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _fromIcore _fromIself) = inv_Expression_s41 _fromX41 (T_Expression_vIn40 _fromOdictionaryEnv)
         (T_MaybeExpression_vOut94 _thenIcore _thenIself) = inv_MaybeExpression_s95 _thenX95 (T_MaybeExpression_vIn94 _thenOdictionaryEnv)
         (T_MaybeExpression_vOut94 _toIcore _toIself) = inv_MaybeExpression_s95 _toX95 (T_MaybeExpression_vIn94 _toOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule277 _fromIcore _lhsIdictionaryEnv _rangeIself _thenIcore _toIcore
         _self = rule278 _fromIself _rangeIself _thenIself _toIself
         _lhsOself :: Expression
         _lhsOself = rule279 _self
         _fromOdictionaryEnv = rule280 _lhsIdictionaryEnv
         _thenOdictionaryEnv = rule281 _lhsIdictionaryEnv
         _toOdictionaryEnv = rule282 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule277 #-}
   rule277 = \ ((_fromIcore) ::  Core.Expr ) ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ((_rangeIself) :: Range) ((_thenIcore) ::  Maybe Core.Expr ) ((_toIcore) ::  Maybe Core.Expr ) ->
              case (_thenIcore, _toIcore) of
                  (Just then_, Just to) ->
                      insertDictionaries (setNameRange enumFromThenToName _rangeIself) _lhsIdictionaryEnv
                         `app_` _fromIcore `app_` then_ `app_` to
                  (Just then_, Nothing) ->
                      insertDictionaries (setNameRange enumFromThenName _rangeIself) _lhsIdictionaryEnv
                         `app_` _fromIcore `app_` then_
                  (Nothing, Just to) ->
                      insertDictionaries (setNameRange enumFromToName _rangeIself) _lhsIdictionaryEnv
                         `app_` _fromIcore `app_` to
                  (Nothing, Nothing) ->
                      insertDictionaries (setNameRange enumFromName _rangeIself) _lhsIdictionaryEnv
                         `app_` _fromIcore
   {-# INLINE rule278 #-}
   rule278 = \ ((_fromIself) :: Expression) ((_rangeIself) :: Range) ((_thenIself) :: MaybeExpression) ((_toIself) :: MaybeExpression) ->
     Expression_Enum _rangeIself _fromIself _thenIself _toIself
   {-# INLINE rule279 #-}
   rule279 = \ _self ->
     _self
   {-# INLINE rule280 #-}
   rule280 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule281 #-}
   rule281 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule282 #-}
   rule282 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_Negate #-}
sem_Expression_Negate :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_Negate arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule283 _expressionIcore _lhsIdictionaryEnv _rangeIself
         _self = rule284 _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule285 _self
         _expressionOdictionaryEnv = rule286 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule283 #-}
   rule283 = \ ((_expressionIcore) ::  Core.Expr ) ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ((_rangeIself) :: Range) ->
                                      insertDictionaries (setNameRange intUnaryMinusName _rangeIself) _lhsIdictionaryEnv
                                      `app_` _expressionIcore
   {-# INLINE rule284 #-}
   rule284 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_Negate _rangeIself _expressionIself
   {-# INLINE rule285 #-}
   rule285 = \ _self ->
     _self
   {-# INLINE rule286 #-}
   rule286 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expression_NegateFloat #-}
sem_Expression_NegateFloat :: T_Range  -> T_Expression  -> T_Expression 
sem_Expression_NegateFloat arg_range_ arg_expression_ = T_Expression (return st41) where
   {-# NOINLINE st41 #-}
   st41 = let
      v40 :: T_Expression_v40 
      v40 = \ (T_Expression_vIn40 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule287 _expressionIcore
         _self = rule288 _expressionIself _rangeIself
         _lhsOself :: Expression
         _lhsOself = rule289 _self
         _expressionOdictionaryEnv = rule290 _lhsIdictionaryEnv
         __result_ = T_Expression_vOut40 _lhsOcore _lhsOself
         in __result_ )
     in C_Expression_s41 v40
   {-# INLINE rule287 #-}
   rule287 = \ ((_expressionIcore) ::  Core.Expr ) ->
              var "$primNegFloat" `app_` _expressionIcore
   {-# INLINE rule288 #-}
   rule288 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Expression_NegateFloat _rangeIself _expressionIself
   {-# INLINE rule289 #-}
   rule289 = \ _self ->
     _self
   {-# INLINE rule290 #-}
   rule290 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv

-- Expressions -------------------------------------------------
-- wrapper
data Inh_Expressions  = Inh_Expressions { dictionaryEnv_Inh_Expressions :: (DictionaryEnvironment) }
data Syn_Expressions  = Syn_Expressions { core_Syn_Expressions :: ( [Core.Expr] ), self_Syn_Expressions :: (Expressions) }
{-# INLINABLE wrap_Expressions #-}
wrap_Expressions :: T_Expressions  -> Inh_Expressions  -> (Syn_Expressions )
wrap_Expressions (T_Expressions act) (Inh_Expressions _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Expressions_vIn43 _lhsIdictionaryEnv
        (T_Expressions_vOut43 _lhsOcore _lhsOself) <- return (inv_Expressions_s44 sem arg)
        return (Syn_Expressions _lhsOcore _lhsOself)
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
data T_Expressions_vIn43  = T_Expressions_vIn43 (DictionaryEnvironment)
data T_Expressions_vOut43  = T_Expressions_vOut43 ( [Core.Expr] ) (Expressions)
{-# NOINLINE sem_Expressions_Cons #-}
sem_Expressions_Cons :: T_Expression  -> T_Expressions  -> T_Expressions 
sem_Expressions_Cons arg_hd_ arg_tl_ = T_Expressions (return st44) where
   {-# NOINLINE st44 #-}
   st44 = let
      v43 :: T_Expressions_v43 
      v43 = \ (T_Expressions_vIn43 _lhsIdictionaryEnv) -> ( let
         _hdX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_hd_))
         _tlX44 = Control.Monad.Identity.runIdentity (attach_T_Expressions (arg_tl_))
         (T_Expression_vOut40 _hdIcore _hdIself) = inv_Expression_s41 _hdX41 (T_Expression_vIn40 _hdOdictionaryEnv)
         (T_Expressions_vOut43 _tlIcore _tlIself) = inv_Expressions_s44 _tlX44 (T_Expressions_vIn43 _tlOdictionaryEnv)
         _lhsOcore ::  [Core.Expr] 
         _lhsOcore = rule291 _hdIcore _tlIcore
         _self = rule292 _hdIself _tlIself
         _lhsOself :: Expressions
         _lhsOself = rule293 _self
         _hdOdictionaryEnv = rule294 _lhsIdictionaryEnv
         _tlOdictionaryEnv = rule295 _lhsIdictionaryEnv
         __result_ = T_Expressions_vOut43 _lhsOcore _lhsOself
         in __result_ )
     in C_Expressions_s44 v43
   {-# INLINE rule291 #-}
   rule291 = \ ((_hdIcore) ::  Core.Expr ) ((_tlIcore) ::  [Core.Expr] ) ->
     _hdIcore  :  _tlIcore
   {-# INLINE rule292 #-}
   rule292 = \ ((_hdIself) :: Expression) ((_tlIself) :: Expressions) ->
     (:) _hdIself _tlIself
   {-# INLINE rule293 #-}
   rule293 = \ _self ->
     _self
   {-# INLINE rule294 #-}
   rule294 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule295 #-}
   rule295 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Expressions_Nil #-}
sem_Expressions_Nil ::  T_Expressions 
sem_Expressions_Nil  = T_Expressions (return st44) where
   {-# NOINLINE st44 #-}
   st44 = let
      v43 :: T_Expressions_v43 
      v43 = \ (T_Expressions_vIn43 _lhsIdictionaryEnv) -> ( let
         _lhsOcore ::  [Core.Expr] 
         _lhsOcore = rule296  ()
         _self = rule297  ()
         _lhsOself :: Expressions
         _lhsOself = rule298 _self
         __result_ = T_Expressions_vOut43 _lhsOcore _lhsOself
         in __result_ )
     in C_Expressions_s44 v43
   {-# INLINE rule296 #-}
   rule296 = \  (_ :: ()) ->
     []
   {-# INLINE rule297 #-}
   rule297 = \  (_ :: ()) ->
     []
   {-# INLINE rule298 #-}
   rule298 = \ _self ->
     _self

-- FieldDeclaration --------------------------------------------
-- wrapper
data Inh_FieldDeclaration  = Inh_FieldDeclaration {  }
data Syn_FieldDeclaration  = Syn_FieldDeclaration { self_Syn_FieldDeclaration :: (FieldDeclaration) }
{-# INLINABLE wrap_FieldDeclaration #-}
wrap_FieldDeclaration :: T_FieldDeclaration  -> Inh_FieldDeclaration  -> (Syn_FieldDeclaration )
wrap_FieldDeclaration (T_FieldDeclaration act) (Inh_FieldDeclaration ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_FieldDeclaration_vIn46 
        (T_FieldDeclaration_vOut46 _lhsOself) <- return (inv_FieldDeclaration_s47 sem arg)
        return (Syn_FieldDeclaration _lhsOself)
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
data T_FieldDeclaration_vIn46  = T_FieldDeclaration_vIn46 
data T_FieldDeclaration_vOut46  = T_FieldDeclaration_vOut46 (FieldDeclaration)
{-# NOINLINE sem_FieldDeclaration_FieldDeclaration #-}
sem_FieldDeclaration_FieldDeclaration :: T_Range  -> T_Names  -> T_AnnotatedType  -> T_FieldDeclaration 
sem_FieldDeclaration_FieldDeclaration arg_range_ arg_names_ arg_type_ = T_FieldDeclaration (return st47) where
   {-# NOINLINE st47 #-}
   st47 = let
      v46 :: T_FieldDeclaration_v46 
      v46 = \ (T_FieldDeclaration_vIn46 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _namesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_names_))
         _typeX8 = Control.Monad.Identity.runIdentity (attach_T_AnnotatedType (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _namesInames _namesIself) = inv_Names_s116 _namesX116 (T_Names_vIn115 )
         (T_AnnotatedType_vOut7 _typeIself) = inv_AnnotatedType_s8 _typeX8 (T_AnnotatedType_vIn7 )
         _self = rule299 _namesIself _rangeIself _typeIself
         _lhsOself :: FieldDeclaration
         _lhsOself = rule300 _self
         __result_ = T_FieldDeclaration_vOut46 _lhsOself
         in __result_ )
     in C_FieldDeclaration_s47 v46
   {-# INLINE rule299 #-}
   rule299 = \ ((_namesIself) :: Names) ((_rangeIself) :: Range) ((_typeIself) :: AnnotatedType) ->
     FieldDeclaration_FieldDeclaration _rangeIself _namesIself _typeIself
   {-# INLINE rule300 #-}
   rule300 = \ _self ->
     _self

-- FieldDeclarations -------------------------------------------
-- wrapper
data Inh_FieldDeclarations  = Inh_FieldDeclarations {  }
data Syn_FieldDeclarations  = Syn_FieldDeclarations { self_Syn_FieldDeclarations :: (FieldDeclarations) }
{-# INLINABLE wrap_FieldDeclarations #-}
wrap_FieldDeclarations :: T_FieldDeclarations  -> Inh_FieldDeclarations  -> (Syn_FieldDeclarations )
wrap_FieldDeclarations (T_FieldDeclarations act) (Inh_FieldDeclarations ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_FieldDeclarations_vIn49 
        (T_FieldDeclarations_vOut49 _lhsOself) <- return (inv_FieldDeclarations_s50 sem arg)
        return (Syn_FieldDeclarations _lhsOself)
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
data T_FieldDeclarations_vIn49  = T_FieldDeclarations_vIn49 
data T_FieldDeclarations_vOut49  = T_FieldDeclarations_vOut49 (FieldDeclarations)
{-# NOINLINE sem_FieldDeclarations_Cons #-}
sem_FieldDeclarations_Cons :: T_FieldDeclaration  -> T_FieldDeclarations  -> T_FieldDeclarations 
sem_FieldDeclarations_Cons arg_hd_ arg_tl_ = T_FieldDeclarations (return st50) where
   {-# NOINLINE st50 #-}
   st50 = let
      v49 :: T_FieldDeclarations_v49 
      v49 = \ (T_FieldDeclarations_vIn49 ) -> ( let
         _hdX47 = Control.Monad.Identity.runIdentity (attach_T_FieldDeclaration (arg_hd_))
         _tlX50 = Control.Monad.Identity.runIdentity (attach_T_FieldDeclarations (arg_tl_))
         (T_FieldDeclaration_vOut46 _hdIself) = inv_FieldDeclaration_s47 _hdX47 (T_FieldDeclaration_vIn46 )
         (T_FieldDeclarations_vOut49 _tlIself) = inv_FieldDeclarations_s50 _tlX50 (T_FieldDeclarations_vIn49 )
         _self = rule301 _hdIself _tlIself
         _lhsOself :: FieldDeclarations
         _lhsOself = rule302 _self
         __result_ = T_FieldDeclarations_vOut49 _lhsOself
         in __result_ )
     in C_FieldDeclarations_s50 v49
   {-# INLINE rule301 #-}
   rule301 = \ ((_hdIself) :: FieldDeclaration) ((_tlIself) :: FieldDeclarations) ->
     (:) _hdIself _tlIself
   {-# INLINE rule302 #-}
   rule302 = \ _self ->
     _self
{-# NOINLINE sem_FieldDeclarations_Nil #-}
sem_FieldDeclarations_Nil ::  T_FieldDeclarations 
sem_FieldDeclarations_Nil  = T_FieldDeclarations (return st50) where
   {-# NOINLINE st50 #-}
   st50 = let
      v49 :: T_FieldDeclarations_v49 
      v49 = \ (T_FieldDeclarations_vIn49 ) -> ( let
         _self = rule303  ()
         _lhsOself :: FieldDeclarations
         _lhsOself = rule304 _self
         __result_ = T_FieldDeclarations_vOut49 _lhsOself
         in __result_ )
     in C_FieldDeclarations_s50 v49
   {-# INLINE rule303 #-}
   rule303 = \  (_ :: ()) ->
     []
   {-# INLINE rule304 #-}
   rule304 = \ _self ->
     _self

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
         _self = rule305 _rangeIself
         _lhsOself :: Fixity
         _lhsOself = rule306 _self
         __result_ = T_Fixity_vOut52 _lhsOself
         in __result_ )
     in C_Fixity_s53 v52
   {-# INLINE rule305 #-}
   rule305 = \ ((_rangeIself) :: Range) ->
     Fixity_Infixl _rangeIself
   {-# INLINE rule306 #-}
   rule306 = \ _self ->
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
         _self = rule307 _rangeIself
         _lhsOself :: Fixity
         _lhsOself = rule308 _self
         __result_ = T_Fixity_vOut52 _lhsOself
         in __result_ )
     in C_Fixity_s53 v52
   {-# INLINE rule307 #-}
   rule307 = \ ((_rangeIself) :: Range) ->
     Fixity_Infixr _rangeIself
   {-# INLINE rule308 #-}
   rule308 = \ _self ->
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
         _self = rule309 _rangeIself
         _lhsOself :: Fixity
         _lhsOself = rule310 _self
         __result_ = T_Fixity_vOut52 _lhsOself
         in __result_ )
     in C_Fixity_s53 v52
   {-# INLINE rule309 #-}
   rule309 = \ ((_rangeIself) :: Range) ->
     Fixity_Infix _rangeIself
   {-# INLINE rule310 #-}
   rule310 = \ _self ->
     _self

-- FunctionBinding ---------------------------------------------
-- wrapper
data Inh_FunctionBinding  = Inh_FunctionBinding { dictionaryEnv_Inh_FunctionBinding :: (DictionaryEnvironment), ids_Inh_FunctionBinding :: ( [Id] ) }
data Syn_FunctionBinding  = Syn_FunctionBinding { arity_Syn_FunctionBinding :: (Int), core_Syn_FunctionBinding :: ( Core.Expr -> Core.Expr ), name_Syn_FunctionBinding :: (Name), self_Syn_FunctionBinding :: (FunctionBinding) }
{-# INLINABLE wrap_FunctionBinding #-}
wrap_FunctionBinding :: T_FunctionBinding  -> Inh_FunctionBinding  -> (Syn_FunctionBinding )
wrap_FunctionBinding (T_FunctionBinding act) (Inh_FunctionBinding _lhsIdictionaryEnv _lhsIids) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_FunctionBinding_vIn55 _lhsIdictionaryEnv _lhsIids
        (T_FunctionBinding_vOut55 _lhsOarity _lhsOcore _lhsOname _lhsOself) <- return (inv_FunctionBinding_s56 sem arg)
        return (Syn_FunctionBinding _lhsOarity _lhsOcore _lhsOname _lhsOself)
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
data T_FunctionBinding_vIn55  = T_FunctionBinding_vIn55 (DictionaryEnvironment) ( [Id] )
data T_FunctionBinding_vOut55  = T_FunctionBinding_vOut55 (Int) ( Core.Expr -> Core.Expr ) (Name) (FunctionBinding)
{-# NOINLINE sem_FunctionBinding_Hole #-}
sem_FunctionBinding_Hole :: T_Range  -> (Integer) -> T_FunctionBinding 
sem_FunctionBinding_Hole arg_range_ arg_id_ = T_FunctionBinding (return st56) where
   {-# NOINLINE st56 #-}
   st56 = let
      v55 :: T_FunctionBinding_v55 
      v55 = \ (T_FunctionBinding_vIn55 _lhsIdictionaryEnv _lhsIids) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOarity :: Int
         _lhsOarity = rule311  ()
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule312  ()
         _lhsOname :: Name
         _lhsOname = rule313  ()
         _self = rule314 _rangeIself arg_id_
         _lhsOself :: FunctionBinding
         _lhsOself = rule315 _self
         __result_ = T_FunctionBinding_vOut55 _lhsOarity _lhsOcore _lhsOname _lhsOself
         in __result_ )
     in C_FunctionBinding_s56 v55
   {-# INLINE rule311 #-}
   rule311 = \  (_ :: ()) ->
                                     0
   {-# INLINE rule312 #-}
   rule312 = \  (_ :: ()) ->
                                     internalError "ToCoreDecl" "FunctionBinding" "holes not supported"
   {-# INLINE rule313 #-}
   rule313 = \  (_ :: ()) ->
                         internalError "ToCoreName.ag" "n/a" "hole FunctionBindings"
   {-# INLINE rule314 #-}
   rule314 = \ ((_rangeIself) :: Range) id_ ->
     FunctionBinding_Hole _rangeIself id_
   {-# INLINE rule315 #-}
   rule315 = \ _self ->
     _self
{-# NOINLINE sem_FunctionBinding_Feedback #-}
sem_FunctionBinding_Feedback :: T_Range  -> (String) -> T_FunctionBinding  -> T_FunctionBinding 
sem_FunctionBinding_Feedback arg_range_ arg_feedback_ arg_functionBinding_ = T_FunctionBinding (return st56) where
   {-# NOINLINE st56 #-}
   st56 = let
      v55 :: T_FunctionBinding_v55 
      v55 = \ (T_FunctionBinding_vIn55 _lhsIdictionaryEnv _lhsIids) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _functionBindingX56 = Control.Monad.Identity.runIdentity (attach_T_FunctionBinding (arg_functionBinding_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_FunctionBinding_vOut55 _functionBindingIarity _functionBindingIcore _functionBindingIname _functionBindingIself) = inv_FunctionBinding_s56 _functionBindingX56 (T_FunctionBinding_vIn55 _functionBindingOdictionaryEnv _functionBindingOids)
         _self = rule316 _functionBindingIself _rangeIself arg_feedback_
         _lhsOself :: FunctionBinding
         _lhsOself = rule317 _self
         _lhsOarity :: Int
         _lhsOarity = rule318 _functionBindingIarity
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule319 _functionBindingIcore
         _lhsOname :: Name
         _lhsOname = rule320 _functionBindingIname
         _functionBindingOdictionaryEnv = rule321 _lhsIdictionaryEnv
         _functionBindingOids = rule322 _lhsIids
         __result_ = T_FunctionBinding_vOut55 _lhsOarity _lhsOcore _lhsOname _lhsOself
         in __result_ )
     in C_FunctionBinding_s56 v55
   {-# INLINE rule316 #-}
   rule316 = \ ((_functionBindingIself) :: FunctionBinding) ((_rangeIself) :: Range) feedback_ ->
     FunctionBinding_Feedback _rangeIself feedback_ _functionBindingIself
   {-# INLINE rule317 #-}
   rule317 = \ _self ->
     _self
   {-# INLINE rule318 #-}
   rule318 = \ ((_functionBindingIarity) :: Int) ->
     _functionBindingIarity
   {-# INLINE rule319 #-}
   rule319 = \ ((_functionBindingIcore) ::  Core.Expr -> Core.Expr ) ->
     _functionBindingIcore
   {-# INLINE rule320 #-}
   rule320 = \ ((_functionBindingIname) :: Name) ->
     _functionBindingIname
   {-# INLINE rule321 #-}
   rule321 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule322 #-}
   rule322 = \ ((_lhsIids) ::  [Id] ) ->
     _lhsIids
{-# NOINLINE sem_FunctionBinding_FunctionBinding #-}
sem_FunctionBinding_FunctionBinding :: T_Range  -> T_LeftHandSide  -> T_RightHandSide  -> T_FunctionBinding 
sem_FunctionBinding_FunctionBinding arg_range_ arg_lefthandside_ arg_righthandside_ = T_FunctionBinding (return st56) where
   {-# NOINLINE st56 #-}
   st56 = let
      v55 :: T_FunctionBinding_v55 
      v55 = \ (T_FunctionBinding_vIn55 _lhsIdictionaryEnv _lhsIids) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _lefthandsideX83 = Control.Monad.Identity.runIdentity (attach_T_LeftHandSide (arg_lefthandside_))
         _righthandsideX149 = Control.Monad.Identity.runIdentity (attach_T_RightHandSide (arg_righthandside_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_LeftHandSide_vOut82 _lefthandsideIarity _lefthandsideIname _lefthandsideIpatterns _lefthandsideIself) = inv_LeftHandSide_s83 _lefthandsideX83 (T_LeftHandSide_vIn82 )
         (T_RightHandSide_vOut148 _righthandsideIcore _righthandsideIisGuarded _righthandsideIself) = inv_RightHandSide_s149 _righthandsideX149 (T_RightHandSide_vIn148 _righthandsideOdictionaryEnv)
         _lhsOarity :: Int
         _lhsOarity = rule323 _lefthandsideIarity
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule324 _lefthandsideIpatterns _lhsIids _righthandsideIcore _righthandsideIisGuarded
         _self = rule325 _lefthandsideIself _rangeIself _righthandsideIself
         _lhsOself :: FunctionBinding
         _lhsOself = rule326 _self
         _lhsOname :: Name
         _lhsOname = rule327 _lefthandsideIname
         _righthandsideOdictionaryEnv = rule328 _lhsIdictionaryEnv
         __result_ = T_FunctionBinding_vOut55 _lhsOarity _lhsOcore _lhsOname _lhsOself
         in __result_ )
     in C_FunctionBinding_s56 v55
   {-# INLINE rule323 #-}
   rule323 = \ ((_lefthandsideIarity) :: Int) ->
                                     _lefthandsideIarity
   {-# INLINE rule324 #-}
   rule324 = \ ((_lefthandsideIpatterns) :: Patterns) ((_lhsIids) ::  [Id] ) ((_righthandsideIcore) ::  Core.Expr ) ((_righthandsideIisGuarded) :: Bool) ->
          \nextClause ->
              let thisClause =
                      patternsToCore
                          (zip _lhsIids _lefthandsideIpatterns)
                          _righthandsideIcore in
              if all patternAlwaysSucceeds _lefthandsideIpatterns
                 &&
                 not _righthandsideIisGuarded
              then
                  thisClause
              else
                  let_ nextClauseId nextClause thisClause
   {-# INLINE rule325 #-}
   rule325 = \ ((_lefthandsideIself) :: LeftHandSide) ((_rangeIself) :: Range) ((_righthandsideIself) :: RightHandSide) ->
     FunctionBinding_FunctionBinding _rangeIself _lefthandsideIself _righthandsideIself
   {-# INLINE rule326 #-}
   rule326 = \ _self ->
     _self
   {-# INLINE rule327 #-}
   rule327 = \ ((_lefthandsideIname) :: Name) ->
     _lefthandsideIname
   {-# INLINE rule328 #-}
   rule328 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv

-- FunctionBindings --------------------------------------------
-- wrapper
data Inh_FunctionBindings  = Inh_FunctionBindings { dictionaryEnv_Inh_FunctionBindings :: (DictionaryEnvironment), ids_Inh_FunctionBindings :: ( [Id] ), range_Inh_FunctionBindings :: (Range) }
data Syn_FunctionBindings  = Syn_FunctionBindings { arity_Syn_FunctionBindings :: (Int), core_Syn_FunctionBindings :: (Core.Expr), name_Syn_FunctionBindings :: (Name), self_Syn_FunctionBindings :: (FunctionBindings) }
{-# INLINABLE wrap_FunctionBindings #-}
wrap_FunctionBindings :: T_FunctionBindings  -> Inh_FunctionBindings  -> (Syn_FunctionBindings )
wrap_FunctionBindings (T_FunctionBindings act) (Inh_FunctionBindings _lhsIdictionaryEnv _lhsIids _lhsIrange) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_FunctionBindings_vIn58 _lhsIdictionaryEnv _lhsIids _lhsIrange
        (T_FunctionBindings_vOut58 _lhsOarity _lhsOcore _lhsOname _lhsOself) <- return (inv_FunctionBindings_s59 sem arg)
        return (Syn_FunctionBindings _lhsOarity _lhsOcore _lhsOname _lhsOself)
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
data T_FunctionBindings_vIn58  = T_FunctionBindings_vIn58 (DictionaryEnvironment) ( [Id] ) (Range)
data T_FunctionBindings_vOut58  = T_FunctionBindings_vOut58 (Int) (Core.Expr) (Name) (FunctionBindings)
{-# NOINLINE sem_FunctionBindings_Cons #-}
sem_FunctionBindings_Cons :: T_FunctionBinding  -> T_FunctionBindings  -> T_FunctionBindings 
sem_FunctionBindings_Cons arg_hd_ arg_tl_ = T_FunctionBindings (return st59) where
   {-# NOINLINE st59 #-}
   st59 = let
      v58 :: T_FunctionBindings_v58 
      v58 = \ (T_FunctionBindings_vIn58 _lhsIdictionaryEnv _lhsIids _lhsIrange) -> ( let
         _hdX56 = Control.Monad.Identity.runIdentity (attach_T_FunctionBinding (arg_hd_))
         _tlX59 = Control.Monad.Identity.runIdentity (attach_T_FunctionBindings (arg_tl_))
         (T_FunctionBinding_vOut55 _hdIarity _hdIcore _hdIname _hdIself) = inv_FunctionBinding_s56 _hdX56 (T_FunctionBinding_vIn55 _hdOdictionaryEnv _hdOids)
         (T_FunctionBindings_vOut58 _tlIarity _tlIcore _tlIname _tlIself) = inv_FunctionBindings_s59 _tlX59 (T_FunctionBindings_vIn58 _tlOdictionaryEnv _tlOids _tlOrange)
         _lhsOcore :: Core.Expr
         _lhsOcore = rule329 _hdIcore _tlIcore
         _lhsOarity :: Int
         _lhsOarity = rule330 _hdIarity
         _lhsOname :: Name
         _lhsOname = rule331 _hdIname
         _self = rule332 _hdIself _tlIself
         _lhsOself :: FunctionBindings
         _lhsOself = rule333 _self
         _hdOdictionaryEnv = rule334 _lhsIdictionaryEnv
         _hdOids = rule335 _lhsIids
         _tlOdictionaryEnv = rule336 _lhsIdictionaryEnv
         _tlOids = rule337 _lhsIids
         _tlOrange = rule338 _lhsIrange
         __result_ = T_FunctionBindings_vOut58 _lhsOarity _lhsOcore _lhsOname _lhsOself
         in __result_ )
     in C_FunctionBindings_s59 v58
   {-# INLINE rule329 #-}
   rule329 = \ ((_hdIcore) ::  Core.Expr -> Core.Expr ) ((_tlIcore) :: Core.Expr) ->
                                     _hdIcore _tlIcore
   {-# INLINE rule330 #-}
   rule330 = \ ((_hdIarity) :: Int) ->
                                     _hdIarity
   {-# INLINE rule331 #-}
   rule331 = \ ((_hdIname) :: Name) ->
                         _hdIname
   {-# INLINE rule332 #-}
   rule332 = \ ((_hdIself) :: FunctionBinding) ((_tlIself) :: FunctionBindings) ->
     (:) _hdIself _tlIself
   {-# INLINE rule333 #-}
   rule333 = \ _self ->
     _self
   {-# INLINE rule334 #-}
   rule334 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule335 #-}
   rule335 = \ ((_lhsIids) ::  [Id] ) ->
     _lhsIids
   {-# INLINE rule336 #-}
   rule336 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule337 #-}
   rule337 = \ ((_lhsIids) ::  [Id] ) ->
     _lhsIids
   {-# INLINE rule338 #-}
   rule338 = \ ((_lhsIrange) :: Range) ->
     _lhsIrange
{-# NOINLINE sem_FunctionBindings_Nil #-}
sem_FunctionBindings_Nil ::  T_FunctionBindings 
sem_FunctionBindings_Nil  = T_FunctionBindings (return st59) where
   {-# NOINLINE st59 #-}
   st59 = let
      v58 :: T_FunctionBindings_v58 
      v58 = \ (T_FunctionBindings_vIn58 _lhsIdictionaryEnv _lhsIids _lhsIrange) -> ( let
         _lhsOcore :: Core.Expr
         _lhsOcore = rule339 _lhsIrange
         _lhsOarity :: Int
         _lhsOarity = rule340  ()
         _lhsOname :: Name
         _lhsOname = rule341  ()
         _self = rule342  ()
         _lhsOself :: FunctionBindings
         _lhsOself = rule343 _self
         __result_ = T_FunctionBindings_vOut58 _lhsOarity _lhsOcore _lhsOname _lhsOself
         in __result_ )
     in C_FunctionBindings_s59 v58
   {-# INLINE rule339 #-}
   rule339 = \ ((_lhsIrange) :: Range) ->
                                     patternMatchFail "function bindings" _lhsIrange
   {-# INLINE rule340 #-}
   rule340 = \  (_ :: ()) ->
                                     internalError "ToCoreDecl" "FunctionBindings" "arity: empty list of function bindings"
   {-# INLINE rule341 #-}
   rule341 = \  (_ :: ()) ->
                         internalError "ToCoreName.ag" "n/a" "empty FunctionBindings"
   {-# INLINE rule342 #-}
   rule342 = \  (_ :: ()) ->
     []
   {-# INLINE rule343 #-}
   rule343 = \ _self ->
     _self

-- GuardedExpression -------------------------------------------
-- wrapper
data Inh_GuardedExpression  = Inh_GuardedExpression { dictionaryEnv_Inh_GuardedExpression :: (DictionaryEnvironment) }
data Syn_GuardedExpression  = Syn_GuardedExpression { core_Syn_GuardedExpression :: ( Core.Expr -> Core.Expr ), self_Syn_GuardedExpression :: (GuardedExpression) }
{-# INLINABLE wrap_GuardedExpression #-}
wrap_GuardedExpression :: T_GuardedExpression  -> Inh_GuardedExpression  -> (Syn_GuardedExpression )
wrap_GuardedExpression (T_GuardedExpression act) (Inh_GuardedExpression _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_GuardedExpression_vIn61 _lhsIdictionaryEnv
        (T_GuardedExpression_vOut61 _lhsOcore _lhsOself) <- return (inv_GuardedExpression_s62 sem arg)
        return (Syn_GuardedExpression _lhsOcore _lhsOself)
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
data T_GuardedExpression_vIn61  = T_GuardedExpression_vIn61 (DictionaryEnvironment)
data T_GuardedExpression_vOut61  = T_GuardedExpression_vOut61 ( Core.Expr -> Core.Expr ) (GuardedExpression)
{-# NOINLINE sem_GuardedExpression_GuardedExpression #-}
sem_GuardedExpression_GuardedExpression :: T_Range  -> T_Expression  -> T_Expression  -> T_GuardedExpression 
sem_GuardedExpression_GuardedExpression arg_range_ arg_guard_ arg_expression_ = T_GuardedExpression (return st62) where
   {-# NOINLINE st62 #-}
   st62 = let
      v61 :: T_GuardedExpression_v61 
      v61 = \ (T_GuardedExpression_vIn61 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_guard_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _guardIcore _guardIself) = inv_Expression_s41 _guardX41 (T_Expression_vIn40 _guardOdictionaryEnv)
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule344 _expressionIcore _guardIcore
         _self = rule345 _expressionIself _guardIself _rangeIself
         _lhsOself :: GuardedExpression
         _lhsOself = rule346 _self
         _guardOdictionaryEnv = rule347 _lhsIdictionaryEnv
         _expressionOdictionaryEnv = rule348 _lhsIdictionaryEnv
         __result_ = T_GuardedExpression_vOut61 _lhsOcore _lhsOself
         in __result_ )
     in C_GuardedExpression_s62 v61
   {-# INLINE rule344 #-}
   rule344 = \ ((_expressionIcore) ::  Core.Expr ) ((_guardIcore) ::  Core.Expr ) ->
          \fail' -> if_ _guardIcore _expressionIcore fail'
   {-# INLINE rule345 #-}
   rule345 = \ ((_expressionIself) :: Expression) ((_guardIself) :: Expression) ((_rangeIself) :: Range) ->
     GuardedExpression_GuardedExpression _rangeIself _guardIself _expressionIself
   {-# INLINE rule346 #-}
   rule346 = \ _self ->
     _self
   {-# INLINE rule347 #-}
   rule347 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule348 #-}
   rule348 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv

-- GuardedExpressions ------------------------------------------
-- wrapper
data Inh_GuardedExpressions  = Inh_GuardedExpressions { dictionaryEnv_Inh_GuardedExpressions :: (DictionaryEnvironment) }
data Syn_GuardedExpressions  = Syn_GuardedExpressions { core_Syn_GuardedExpressions :: ( [Core.Expr -> Core.Expr] ), self_Syn_GuardedExpressions :: (GuardedExpressions) }
{-# INLINABLE wrap_GuardedExpressions #-}
wrap_GuardedExpressions :: T_GuardedExpressions  -> Inh_GuardedExpressions  -> (Syn_GuardedExpressions )
wrap_GuardedExpressions (T_GuardedExpressions act) (Inh_GuardedExpressions _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_GuardedExpressions_vIn64 _lhsIdictionaryEnv
        (T_GuardedExpressions_vOut64 _lhsOcore _lhsOself) <- return (inv_GuardedExpressions_s65 sem arg)
        return (Syn_GuardedExpressions _lhsOcore _lhsOself)
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
data T_GuardedExpressions_vIn64  = T_GuardedExpressions_vIn64 (DictionaryEnvironment)
data T_GuardedExpressions_vOut64  = T_GuardedExpressions_vOut64 ( [Core.Expr -> Core.Expr] ) (GuardedExpressions)
{-# NOINLINE sem_GuardedExpressions_Cons #-}
sem_GuardedExpressions_Cons :: T_GuardedExpression  -> T_GuardedExpressions  -> T_GuardedExpressions 
sem_GuardedExpressions_Cons arg_hd_ arg_tl_ = T_GuardedExpressions (return st65) where
   {-# NOINLINE st65 #-}
   st65 = let
      v64 :: T_GuardedExpressions_v64 
      v64 = \ (T_GuardedExpressions_vIn64 _lhsIdictionaryEnv) -> ( let
         _hdX62 = Control.Monad.Identity.runIdentity (attach_T_GuardedExpression (arg_hd_))
         _tlX65 = Control.Monad.Identity.runIdentity (attach_T_GuardedExpressions (arg_tl_))
         (T_GuardedExpression_vOut61 _hdIcore _hdIself) = inv_GuardedExpression_s62 _hdX62 (T_GuardedExpression_vIn61 _hdOdictionaryEnv)
         (T_GuardedExpressions_vOut64 _tlIcore _tlIself) = inv_GuardedExpressions_s65 _tlX65 (T_GuardedExpressions_vIn64 _tlOdictionaryEnv)
         _lhsOcore ::  [Core.Expr -> Core.Expr] 
         _lhsOcore = rule349 _hdIcore _tlIcore
         _self = rule350 _hdIself _tlIself
         _lhsOself :: GuardedExpressions
         _lhsOself = rule351 _self
         _hdOdictionaryEnv = rule352 _lhsIdictionaryEnv
         _tlOdictionaryEnv = rule353 _lhsIdictionaryEnv
         __result_ = T_GuardedExpressions_vOut64 _lhsOcore _lhsOself
         in __result_ )
     in C_GuardedExpressions_s65 v64
   {-# INLINE rule349 #-}
   rule349 = \ ((_hdIcore) ::  Core.Expr -> Core.Expr ) ((_tlIcore) ::  [Core.Expr -> Core.Expr] ) ->
     _hdIcore  :  _tlIcore
   {-# INLINE rule350 #-}
   rule350 = \ ((_hdIself) :: GuardedExpression) ((_tlIself) :: GuardedExpressions) ->
     (:) _hdIself _tlIself
   {-# INLINE rule351 #-}
   rule351 = \ _self ->
     _self
   {-# INLINE rule352 #-}
   rule352 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule353 #-}
   rule353 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_GuardedExpressions_Nil #-}
sem_GuardedExpressions_Nil ::  T_GuardedExpressions 
sem_GuardedExpressions_Nil  = T_GuardedExpressions (return st65) where
   {-# NOINLINE st65 #-}
   st65 = let
      v64 :: T_GuardedExpressions_v64 
      v64 = \ (T_GuardedExpressions_vIn64 _lhsIdictionaryEnv) -> ( let
         _lhsOcore ::  [Core.Expr -> Core.Expr] 
         _lhsOcore = rule354  ()
         _self = rule355  ()
         _lhsOself :: GuardedExpressions
         _lhsOself = rule356 _self
         __result_ = T_GuardedExpressions_vOut64 _lhsOcore _lhsOself
         in __result_ )
     in C_GuardedExpressions_s65 v64
   {-# INLINE rule354 #-}
   rule354 = \  (_ :: ()) ->
     []
   {-# INLINE rule355 #-}
   rule355 = \  (_ :: ()) ->
     []
   {-# INLINE rule356 #-}
   rule356 = \ _self ->
     _self

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
         _self = rule357 _nameIself _rangeIself
         _lhsOself :: Import
         _lhsOself = rule358 _self
         __result_ = T_Import_vOut67 _lhsOself
         in __result_ )
     in C_Import_s68 v67
   {-# INLINE rule357 #-}
   rule357 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Import_Variable _rangeIself _nameIself
   {-# INLINE rule358 #-}
   rule358 = \ _self ->
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
         (T_MaybeNames_vOut106 _namesInames _namesIself) = inv_MaybeNames_s107 _namesX107 (T_MaybeNames_vIn106 )
         _self = rule359 _nameIself _namesIself _rangeIself
         _lhsOself :: Import
         _lhsOself = rule360 _self
         __result_ = T_Import_vOut67 _lhsOself
         in __result_ )
     in C_Import_s68 v67
   {-# INLINE rule359 #-}
   rule359 = \ ((_nameIself) :: Name) ((_namesIself) :: MaybeNames) ((_rangeIself) :: Range) ->
     Import_TypeOrClass _rangeIself _nameIself _namesIself
   {-# INLINE rule360 #-}
   rule360 = \ _self ->
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
         _self = rule361 _nameIself _rangeIself
         _lhsOself :: Import
         _lhsOself = rule362 _self
         __result_ = T_Import_vOut67 _lhsOself
         in __result_ )
     in C_Import_s68 v67
   {-# INLINE rule361 #-}
   rule361 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Import_TypeOrClassComplete _rangeIself _nameIself
   {-# INLINE rule362 #-}
   rule362 = \ _self ->
     _self

-- ImportDeclaration -------------------------------------------
-- wrapper
data Inh_ImportDeclaration  = Inh_ImportDeclaration {  }
data Syn_ImportDeclaration  = Syn_ImportDeclaration { self_Syn_ImportDeclaration :: (ImportDeclaration) }
{-# INLINABLE wrap_ImportDeclaration #-}
wrap_ImportDeclaration :: T_ImportDeclaration  -> Inh_ImportDeclaration  -> (Syn_ImportDeclaration )
wrap_ImportDeclaration (T_ImportDeclaration act) (Inh_ImportDeclaration ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_ImportDeclaration_vIn70 
        (T_ImportDeclaration_vOut70 _lhsOself) <- return (inv_ImportDeclaration_s71 sem arg)
        return (Syn_ImportDeclaration _lhsOself)
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
data T_ImportDeclaration_vIn70  = T_ImportDeclaration_vIn70 
data T_ImportDeclaration_vOut70  = T_ImportDeclaration_vOut70 (ImportDeclaration)
{-# NOINLINE sem_ImportDeclaration_Import #-}
sem_ImportDeclaration_Import :: T_Range  -> (Bool) -> T_Name  -> T_MaybeName  -> T_MaybeImportSpecification  -> T_ImportDeclaration 
sem_ImportDeclaration_Import arg_range_ arg_qualified_ arg_name_ arg_asname_ arg_importspecification_ = T_ImportDeclaration (return st71) where
   {-# NOINLINE st71 #-}
   st71 = let
      v70 :: T_ImportDeclaration_v70 
      v70 = \ (T_ImportDeclaration_vIn70 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _asnameX104 = Control.Monad.Identity.runIdentity (attach_T_MaybeName (arg_asname_))
         _importspecificationX98 = Control.Monad.Identity.runIdentity (attach_T_MaybeImportSpecification (arg_importspecification_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_MaybeName_vOut103 _asnameIisNothing _asnameIname _asnameIself) = inv_MaybeName_s104 _asnameX104 (T_MaybeName_vIn103 )
         (T_MaybeImportSpecification_vOut97 _importspecificationIself) = inv_MaybeImportSpecification_s98 _importspecificationX98 (T_MaybeImportSpecification_vIn97 )
         _self = rule363 _asnameIself _importspecificationIself _nameIself _rangeIself arg_qualified_
         _lhsOself :: ImportDeclaration
         _lhsOself = rule364 _self
         __result_ = T_ImportDeclaration_vOut70 _lhsOself
         in __result_ )
     in C_ImportDeclaration_s71 v70
   {-# INLINE rule363 #-}
   rule363 = \ ((_asnameIself) :: MaybeName) ((_importspecificationIself) :: MaybeImportSpecification) ((_nameIself) :: Name) ((_rangeIself) :: Range) qualified_ ->
     ImportDeclaration_Import _rangeIself qualified_ _nameIself _asnameIself _importspecificationIself
   {-# INLINE rule364 #-}
   rule364 = \ _self ->
     _self
{-# NOINLINE sem_ImportDeclaration_Empty #-}
sem_ImportDeclaration_Empty :: T_Range  -> T_ImportDeclaration 
sem_ImportDeclaration_Empty arg_range_ = T_ImportDeclaration (return st71) where
   {-# NOINLINE st71 #-}
   st71 = let
      v70 :: T_ImportDeclaration_v70 
      v70 = \ (T_ImportDeclaration_vIn70 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _self = rule365 _rangeIself
         _lhsOself :: ImportDeclaration
         _lhsOself = rule366 _self
         __result_ = T_ImportDeclaration_vOut70 _lhsOself
         in __result_ )
     in C_ImportDeclaration_s71 v70
   {-# INLINE rule365 #-}
   rule365 = \ ((_rangeIself) :: Range) ->
     ImportDeclaration_Empty _rangeIself
   {-# INLINE rule366 #-}
   rule366 = \ _self ->
     _self

-- ImportDeclarations ------------------------------------------
-- wrapper
data Inh_ImportDeclarations  = Inh_ImportDeclarations {  }
data Syn_ImportDeclarations  = Syn_ImportDeclarations { self_Syn_ImportDeclarations :: (ImportDeclarations) }
{-# INLINABLE wrap_ImportDeclarations #-}
wrap_ImportDeclarations :: T_ImportDeclarations  -> Inh_ImportDeclarations  -> (Syn_ImportDeclarations )
wrap_ImportDeclarations (T_ImportDeclarations act) (Inh_ImportDeclarations ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_ImportDeclarations_vIn73 
        (T_ImportDeclarations_vOut73 _lhsOself) <- return (inv_ImportDeclarations_s74 sem arg)
        return (Syn_ImportDeclarations _lhsOself)
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
data T_ImportDeclarations_vIn73  = T_ImportDeclarations_vIn73 
data T_ImportDeclarations_vOut73  = T_ImportDeclarations_vOut73 (ImportDeclarations)
{-# NOINLINE sem_ImportDeclarations_Cons #-}
sem_ImportDeclarations_Cons :: T_ImportDeclaration  -> T_ImportDeclarations  -> T_ImportDeclarations 
sem_ImportDeclarations_Cons arg_hd_ arg_tl_ = T_ImportDeclarations (return st74) where
   {-# NOINLINE st74 #-}
   st74 = let
      v73 :: T_ImportDeclarations_v73 
      v73 = \ (T_ImportDeclarations_vIn73 ) -> ( let
         _hdX71 = Control.Monad.Identity.runIdentity (attach_T_ImportDeclaration (arg_hd_))
         _tlX74 = Control.Monad.Identity.runIdentity (attach_T_ImportDeclarations (arg_tl_))
         (T_ImportDeclaration_vOut70 _hdIself) = inv_ImportDeclaration_s71 _hdX71 (T_ImportDeclaration_vIn70 )
         (T_ImportDeclarations_vOut73 _tlIself) = inv_ImportDeclarations_s74 _tlX74 (T_ImportDeclarations_vIn73 )
         _self = rule367 _hdIself _tlIself
         _lhsOself :: ImportDeclarations
         _lhsOself = rule368 _self
         __result_ = T_ImportDeclarations_vOut73 _lhsOself
         in __result_ )
     in C_ImportDeclarations_s74 v73
   {-# INLINE rule367 #-}
   rule367 = \ ((_hdIself) :: ImportDeclaration) ((_tlIself) :: ImportDeclarations) ->
     (:) _hdIself _tlIself
   {-# INLINE rule368 #-}
   rule368 = \ _self ->
     _self
{-# NOINLINE sem_ImportDeclarations_Nil #-}
sem_ImportDeclarations_Nil ::  T_ImportDeclarations 
sem_ImportDeclarations_Nil  = T_ImportDeclarations (return st74) where
   {-# NOINLINE st74 #-}
   st74 = let
      v73 :: T_ImportDeclarations_v73 
      v73 = \ (T_ImportDeclarations_vIn73 ) -> ( let
         _self = rule369  ()
         _lhsOself :: ImportDeclarations
         _lhsOself = rule370 _self
         __result_ = T_ImportDeclarations_vOut73 _lhsOself
         in __result_ )
     in C_ImportDeclarations_s74 v73
   {-# INLINE rule369 #-}
   rule369 = \  (_ :: ()) ->
     []
   {-# INLINE rule370 #-}
   rule370 = \ _self ->
     _self

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
         _self = rule371 _importsIself _rangeIself arg_hiding_
         _lhsOself :: ImportSpecification
         _lhsOself = rule372 _self
         __result_ = T_ImportSpecification_vOut76 _lhsOself
         in __result_ )
     in C_ImportSpecification_s77 v76
   {-# INLINE rule371 #-}
   rule371 = \ ((_importsIself) :: Imports) ((_rangeIself) :: Range) hiding_ ->
     ImportSpecification_Import _rangeIself hiding_ _importsIself
   {-# INLINE rule372 #-}
   rule372 = \ _self ->
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
         _self = rule373 _hdIself _tlIself
         _lhsOself :: Imports
         _lhsOself = rule374 _self
         __result_ = T_Imports_vOut79 _lhsOself
         in __result_ )
     in C_Imports_s80 v79
   {-# INLINE rule373 #-}
   rule373 = \ ((_hdIself) :: Import) ((_tlIself) :: Imports) ->
     (:) _hdIself _tlIself
   {-# INLINE rule374 #-}
   rule374 = \ _self ->
     _self
{-# NOINLINE sem_Imports_Nil #-}
sem_Imports_Nil ::  T_Imports 
sem_Imports_Nil  = T_Imports (return st80) where
   {-# NOINLINE st80 #-}
   st80 = let
      v79 :: T_Imports_v79 
      v79 = \ (T_Imports_vIn79 ) -> ( let
         _self = rule375  ()
         _lhsOself :: Imports
         _lhsOself = rule376 _self
         __result_ = T_Imports_vOut79 _lhsOself
         in __result_ )
     in C_Imports_s80 v79
   {-# INLINE rule375 #-}
   rule375 = \  (_ :: ()) ->
     []
   {-# INLINE rule376 #-}
   rule376 = \ _self ->
     _self

-- LeftHandSide ------------------------------------------------
-- wrapper
data Inh_LeftHandSide  = Inh_LeftHandSide {  }
data Syn_LeftHandSide  = Syn_LeftHandSide { arity_Syn_LeftHandSide :: (Int), name_Syn_LeftHandSide :: (Name), patterns_Syn_LeftHandSide :: (Patterns), self_Syn_LeftHandSide :: (LeftHandSide) }
{-# INLINABLE wrap_LeftHandSide #-}
wrap_LeftHandSide :: T_LeftHandSide  -> Inh_LeftHandSide  -> (Syn_LeftHandSide )
wrap_LeftHandSide (T_LeftHandSide act) (Inh_LeftHandSide ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_LeftHandSide_vIn82 
        (T_LeftHandSide_vOut82 _lhsOarity _lhsOname _lhsOpatterns _lhsOself) <- return (inv_LeftHandSide_s83 sem arg)
        return (Syn_LeftHandSide _lhsOarity _lhsOname _lhsOpatterns _lhsOself)
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
data T_LeftHandSide_vIn82  = T_LeftHandSide_vIn82 
data T_LeftHandSide_vOut82  = T_LeftHandSide_vOut82 (Int) (Name) (Patterns) (LeftHandSide)
{-# NOINLINE sem_LeftHandSide_Function #-}
sem_LeftHandSide_Function :: T_Range  -> T_Name  -> T_Patterns  -> T_LeftHandSide 
sem_LeftHandSide_Function arg_range_ arg_name_ arg_patterns_ = T_LeftHandSide (return st83) where
   {-# NOINLINE st83 #-}
   st83 = let
      v82 :: T_LeftHandSide_v82 
      v82 = \ (T_LeftHandSide_vIn82 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Patterns_vOut121 _patternsIlength _patternsIself _patternsIvars) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         _lhsOarity :: Int
         _lhsOarity = rule377 _patternsIlength
         _lhsOpatterns :: Patterns
         _lhsOpatterns = rule378 _patternsIself
         _lhsOname :: Name
         _lhsOname = rule379 _nameIself
         _self = rule380 _nameIself _patternsIself _rangeIself
         _lhsOself :: LeftHandSide
         _lhsOself = rule381 _self
         __result_ = T_LeftHandSide_vOut82 _lhsOarity _lhsOname _lhsOpatterns _lhsOself
         in __result_ )
     in C_LeftHandSide_s83 v82
   {-# INLINE rule377 #-}
   rule377 = \ ((_patternsIlength) :: Int) ->
                                     _patternsIlength
   {-# INLINE rule378 #-}
   rule378 = \ ((_patternsIself) :: Patterns) ->
                                        _patternsIself
   {-# INLINE rule379 #-}
   rule379 = \ ((_nameIself) :: Name) ->
                             _nameIself
   {-# INLINE rule380 #-}
   rule380 = \ ((_nameIself) :: Name) ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     LeftHandSide_Function _rangeIself _nameIself _patternsIself
   {-# INLINE rule381 #-}
   rule381 = \ _self ->
     _self
{-# NOINLINE sem_LeftHandSide_Infix #-}
sem_LeftHandSide_Infix :: T_Range  -> T_Pattern  -> T_Name  -> T_Pattern  -> T_LeftHandSide 
sem_LeftHandSide_Infix arg_range_ arg_leftPattern_ arg_operator_ arg_rightPattern_ = T_LeftHandSide (return st83) where
   {-# NOINLINE st83 #-}
   st83 = let
      v82 :: T_LeftHandSide_v82 
      v82 = \ (T_LeftHandSide_vIn82 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_leftPattern_))
         _operatorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_operator_))
         _rightPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_rightPattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _leftPatternIself _leftPatternIvars) = inv_Pattern_s119 _leftPatternX119 (T_Pattern_vIn118 )
         (T_Name_vOut112 _operatorIself) = inv_Name_s113 _operatorX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _rightPatternIself _rightPatternIvars) = inv_Pattern_s119 _rightPatternX119 (T_Pattern_vIn118 )
         _lhsOarity :: Int
         _lhsOarity = rule382  ()
         _lhsOpatterns :: Patterns
         _lhsOpatterns = rule383 _leftPatternIself _rightPatternIself
         _lhsOname :: Name
         _lhsOname = rule384 _operatorIself
         _self = rule385 _leftPatternIself _operatorIself _rangeIself _rightPatternIself
         _lhsOself :: LeftHandSide
         _lhsOself = rule386 _self
         __result_ = T_LeftHandSide_vOut82 _lhsOarity _lhsOname _lhsOpatterns _lhsOself
         in __result_ )
     in C_LeftHandSide_s83 v82
   {-# INLINE rule382 #-}
   rule382 = \  (_ :: ()) ->
                                     2
   {-# INLINE rule383 #-}
   rule383 = \ ((_leftPatternIself) :: Pattern) ((_rightPatternIself) :: Pattern) ->
                                        [_leftPatternIself, _rightPatternIself ]
   {-# INLINE rule384 #-}
   rule384 = \ ((_operatorIself) :: Name) ->
                             _operatorIself
   {-# INLINE rule385 #-}
   rule385 = \ ((_leftPatternIself) :: Pattern) ((_operatorIself) :: Name) ((_rangeIself) :: Range) ((_rightPatternIself) :: Pattern) ->
     LeftHandSide_Infix _rangeIself _leftPatternIself _operatorIself _rightPatternIself
   {-# INLINE rule386 #-}
   rule386 = \ _self ->
     _self
{-# NOINLINE sem_LeftHandSide_Parenthesized #-}
sem_LeftHandSide_Parenthesized :: T_Range  -> T_LeftHandSide  -> T_Patterns  -> T_LeftHandSide 
sem_LeftHandSide_Parenthesized arg_range_ arg_lefthandside_ arg_patterns_ = T_LeftHandSide (return st83) where
   {-# NOINLINE st83 #-}
   st83 = let
      v82 :: T_LeftHandSide_v82 
      v82 = \ (T_LeftHandSide_vIn82 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _lefthandsideX83 = Control.Monad.Identity.runIdentity (attach_T_LeftHandSide (arg_lefthandside_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_LeftHandSide_vOut82 _lefthandsideIarity _lefthandsideIname _lefthandsideIpatterns _lefthandsideIself) = inv_LeftHandSide_s83 _lefthandsideX83 (T_LeftHandSide_vIn82 )
         (T_Patterns_vOut121 _patternsIlength _patternsIself _patternsIvars) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         _lhsOarity :: Int
         _lhsOarity = rule387 _lefthandsideIarity _patternsIlength
         _lhsOpatterns :: Patterns
         _lhsOpatterns = rule388 _lefthandsideIpatterns _patternsIself
         _self = rule389 _lefthandsideIself _patternsIself _rangeIself
         _lhsOself :: LeftHandSide
         _lhsOself = rule390 _self
         _lhsOname :: Name
         _lhsOname = rule391 _lefthandsideIname
         __result_ = T_LeftHandSide_vOut82 _lhsOarity _lhsOname _lhsOpatterns _lhsOself
         in __result_ )
     in C_LeftHandSide_s83 v82
   {-# INLINE rule387 #-}
   rule387 = \ ((_lefthandsideIarity) :: Int) ((_patternsIlength) :: Int) ->
                                     _lefthandsideIarity + _patternsIlength
   {-# INLINE rule388 #-}
   rule388 = \ ((_lefthandsideIpatterns) :: Patterns) ((_patternsIself) :: Patterns) ->
                                        _lefthandsideIpatterns ++ _patternsIself
   {-# INLINE rule389 #-}
   rule389 = \ ((_lefthandsideIself) :: LeftHandSide) ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     LeftHandSide_Parenthesized _rangeIself _lefthandsideIself _patternsIself
   {-# INLINE rule390 #-}
   rule390 = \ _self ->
     _self
   {-# INLINE rule391 #-}
   rule391 = \ ((_lefthandsideIname) :: Name) ->
     _lefthandsideIname

-- Literal -----------------------------------------------------
-- wrapper
data Inh_Literal  = Inh_Literal {  }
data Syn_Literal  = Syn_Literal { core_Syn_Literal :: ( Core.Expr ), self_Syn_Literal :: (Literal) }
{-# INLINABLE wrap_Literal #-}
wrap_Literal :: T_Literal  -> Inh_Literal  -> (Syn_Literal )
wrap_Literal (T_Literal act) (Inh_Literal ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Literal_vIn85 
        (T_Literal_vOut85 _lhsOcore _lhsOself) <- return (inv_Literal_s86 sem arg)
        return (Syn_Literal _lhsOcore _lhsOself)
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
data T_Literal_vIn85  = T_Literal_vIn85 
data T_Literal_vOut85  = T_Literal_vOut85 ( Core.Expr ) (Literal)
{-# NOINLINE sem_Literal_Int #-}
sem_Literal_Int :: T_Range  -> (String) -> T_Literal 
sem_Literal_Int arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule392 arg_value_
         _self = rule393 _rangeIself arg_value_
         _lhsOself :: Literal
         _lhsOself = rule394 _self
         __result_ = T_Literal_vOut85 _lhsOcore _lhsOself
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule392 #-}
   rule392 = \ value_ ->
                                         Core.Lit (Core.LitInt (read value_))
   {-# INLINE rule393 #-}
   rule393 = \ ((_rangeIself) :: Range) value_ ->
     Literal_Int _rangeIself value_
   {-# INLINE rule394 #-}
   rule394 = \ _self ->
     _self
{-# NOINLINE sem_Literal_Char #-}
sem_Literal_Char :: T_Range  -> (String) -> T_Literal 
sem_Literal_Char arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule395 arg_value_
         _self = rule396 _rangeIself arg_value_
         _lhsOself :: Literal
         _lhsOself = rule397 _self
         __result_ = T_Literal_vOut85 _lhsOcore _lhsOself
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule395 #-}
   rule395 = \ value_ ->
              Core.Lit (Core.LitInt (ord
                  (read ("'" ++ value_ ++ "'"))))
   {-# INLINE rule396 #-}
   rule396 = \ ((_rangeIself) :: Range) value_ ->
     Literal_Char _rangeIself value_
   {-# INLINE rule397 #-}
   rule397 = \ _self ->
     _self
{-# NOINLINE sem_Literal_Float #-}
sem_Literal_Float :: T_Range  -> (String) -> T_Literal 
sem_Literal_Float arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule398 arg_value_
         _self = rule399 _rangeIself arg_value_
         _lhsOself :: Literal
         _lhsOself = rule400 _self
         __result_ = T_Literal_vOut85 _lhsOcore _lhsOself
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule398 #-}
   rule398 = \ value_ ->
                                         float value_
   {-# INLINE rule399 #-}
   rule399 = \ ((_rangeIself) :: Range) value_ ->
     Literal_Float _rangeIself value_
   {-# INLINE rule400 #-}
   rule400 = \ _self ->
     _self
{-# NOINLINE sem_Literal_String #-}
sem_Literal_String :: T_Range  -> (String) -> T_Literal 
sem_Literal_String arg_range_ arg_value_ = T_Literal (return st86) where
   {-# NOINLINE st86 #-}
   st86 = let
      v85 :: T_Literal_v85 
      v85 = \ (T_Literal_vIn85 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule401 arg_value_
         _self = rule402 _rangeIself arg_value_
         _lhsOself :: Literal
         _lhsOself = rule403 _self
         __result_ = T_Literal_vOut85 _lhsOcore _lhsOself
         in __result_ )
     in C_Literal_s86 v85
   {-# INLINE rule401 #-}
   rule401 = \ value_ ->
          var "$primPackedToString" `app_`
              packedString (read ("\"" ++ value_ ++ "\""))
   {-# INLINE rule402 #-}
   rule402 = \ ((_rangeIself) :: Range) value_ ->
     Literal_String _rangeIself value_
   {-# INLINE rule403 #-}
   rule403 = \ _self ->
     _self

-- MaybeDeclarations -------------------------------------------
-- wrapper
data Inh_MaybeDeclarations  = Inh_MaybeDeclarations { dictionaryEnv_Inh_MaybeDeclarations :: (DictionaryEnvironment) }
data Syn_MaybeDeclarations  = Syn_MaybeDeclarations { core_Syn_MaybeDeclarations :: ( Core.Expr -> Core.Expr ), self_Syn_MaybeDeclarations :: (MaybeDeclarations) }
{-# INLINABLE wrap_MaybeDeclarations #-}
wrap_MaybeDeclarations :: T_MaybeDeclarations  -> Inh_MaybeDeclarations  -> (Syn_MaybeDeclarations )
wrap_MaybeDeclarations (T_MaybeDeclarations act) (Inh_MaybeDeclarations _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeDeclarations_vIn88 _lhsIdictionaryEnv
        (T_MaybeDeclarations_vOut88 _lhsOcore _lhsOself) <- return (inv_MaybeDeclarations_s89 sem arg)
        return (Syn_MaybeDeclarations _lhsOcore _lhsOself)
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
data T_MaybeDeclarations_vIn88  = T_MaybeDeclarations_vIn88 (DictionaryEnvironment)
data T_MaybeDeclarations_vOut88  = T_MaybeDeclarations_vOut88 ( Core.Expr -> Core.Expr ) (MaybeDeclarations)
{-# NOINLINE sem_MaybeDeclarations_Nothing #-}
sem_MaybeDeclarations_Nothing ::  T_MaybeDeclarations 
sem_MaybeDeclarations_Nothing  = T_MaybeDeclarations (return st89) where
   {-# NOINLINE st89 #-}
   st89 = let
      v88 :: T_MaybeDeclarations_v88 
      v88 = \ (T_MaybeDeclarations_vIn88 _lhsIdictionaryEnv) -> ( let
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule404  ()
         _self = rule405  ()
         _lhsOself :: MaybeDeclarations
         _lhsOself = rule406 _self
         __result_ = T_MaybeDeclarations_vOut88 _lhsOcore _lhsOself
         in __result_ )
     in C_MaybeDeclarations_s89 v88
   {-# INLINE rule404 #-}
   rule404 = \  (_ :: ()) ->
                               \continue -> continue
   {-# INLINE rule405 #-}
   rule405 = \  (_ :: ()) ->
     MaybeDeclarations_Nothing
   {-# INLINE rule406 #-}
   rule406 = \ _self ->
     _self
{-# NOINLINE sem_MaybeDeclarations_Just #-}
sem_MaybeDeclarations_Just :: T_Declarations  -> T_MaybeDeclarations 
sem_MaybeDeclarations_Just arg_declarations_ = T_MaybeDeclarations (return st89) where
   {-# NOINLINE st89 #-}
   st89 = let
      v88 :: T_MaybeDeclarations_v88 
      v88 = \ (T_MaybeDeclarations_vIn88 _lhsIdictionaryEnv) -> ( let
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Declarations_vOut31 _declarationsIdecls _declarationsIpatBindNr _declarationsIself) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 _declarationsOdictionaryEnv _declarationsOimportEnv _declarationsOisTopLevel _declarationsOpatBindNr)
         _importEnv = rule407  ()
         _declarationsOpatBindNr = rule408  ()
         _declarationsOisTopLevel = rule409  ()
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule410 _declarationsIdecls
         _self = rule411 _declarationsIself
         _lhsOself :: MaybeDeclarations
         _lhsOself = rule412 _self
         _declarationsOdictionaryEnv = rule413 _lhsIdictionaryEnv
         _declarationsOimportEnv = rule414 _importEnv
         __result_ = T_MaybeDeclarations_vOut88 _lhsOcore _lhsOself
         in __result_ )
     in C_MaybeDeclarations_s89 v88
   {-# INLINE rule407 #-}
   rule407 = \  (_ :: ()) ->
                                               internalError "CodeGeneration.ag" "MaybeDeclarations.Just" ""
   {-# INLINE rule408 #-}
   rule408 = \  (_ :: ()) ->
                                             0
   {-# INLINE rule409 #-}
   rule409 = \  (_ :: ()) ->
                                              False
   {-# INLINE rule410 #-}
   rule410 = \ ((_declarationsIdecls) ::  [CoreDecl] ) ->
                               \continue -> letrec_ _declarationsIdecls continue
   {-# INLINE rule411 #-}
   rule411 = \ ((_declarationsIself) :: Declarations) ->
     MaybeDeclarations_Just _declarationsIself
   {-# INLINE rule412 #-}
   rule412 = \ _self ->
     _self
   {-# INLINE rule413 #-}
   rule413 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule414 #-}
   rule414 = \ _importEnv ->
     _importEnv

-- MaybeExports ------------------------------------------------
-- wrapper
data Inh_MaybeExports  = Inh_MaybeExports {  }
data Syn_MaybeExports  = Syn_MaybeExports { cons_Syn_MaybeExports :: (IdSet), mods_Syn_MaybeExports :: (IdSet), self_Syn_MaybeExports :: (MaybeExports), types_Syn_MaybeExports :: (IdSet), values_Syn_MaybeExports :: (IdSet) }
{-# INLINABLE wrap_MaybeExports #-}
wrap_MaybeExports :: T_MaybeExports  -> Inh_MaybeExports  -> (Syn_MaybeExports )
wrap_MaybeExports (T_MaybeExports act) (Inh_MaybeExports ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeExports_vIn91 
        (T_MaybeExports_vOut91 _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues) <- return (inv_MaybeExports_s92 sem arg)
        return (Syn_MaybeExports _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues)
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
data T_MaybeExports_vIn91  = T_MaybeExports_vIn91 
data T_MaybeExports_vOut91  = T_MaybeExports_vOut91 (IdSet) (IdSet) (MaybeExports) (IdSet) (IdSet)
{-# NOINLINE sem_MaybeExports_Nothing #-}
sem_MaybeExports_Nothing ::  T_MaybeExports 
sem_MaybeExports_Nothing  = T_MaybeExports (return st92) where
   {-# NOINLINE st92 #-}
   st92 = let
      v91 :: T_MaybeExports_v91 
      v91 = \ (T_MaybeExports_vIn91 ) -> ( let
         _lhsOcons :: IdSet
         _lhsOcons = rule415  ()
         _lhsOmods :: IdSet
         _lhsOmods = rule416  ()
         _lhsOtypes :: IdSet
         _lhsOtypes = rule417  ()
         _lhsOvalues :: IdSet
         _lhsOvalues = rule418  ()
         _self = rule419  ()
         _lhsOself :: MaybeExports
         _lhsOself = rule420 _self
         __result_ = T_MaybeExports_vOut91 _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues
         in __result_ )
     in C_MaybeExports_s92 v91
   {-# INLINE rule415 #-}
   rule415 = \  (_ :: ()) ->
     emptySet
   {-# INLINE rule416 #-}
   rule416 = \  (_ :: ()) ->
     emptySet
   {-# INLINE rule417 #-}
   rule417 = \  (_ :: ()) ->
     emptySet
   {-# INLINE rule418 #-}
   rule418 = \  (_ :: ()) ->
     emptySet
   {-# INLINE rule419 #-}
   rule419 = \  (_ :: ()) ->
     MaybeExports_Nothing
   {-# INLINE rule420 #-}
   rule420 = \ _self ->
     _self
{-# NOINLINE sem_MaybeExports_Just #-}
sem_MaybeExports_Just :: T_Exports  -> T_MaybeExports 
sem_MaybeExports_Just arg_exports_ = T_MaybeExports (return st92) where
   {-# NOINLINE st92 #-}
   st92 = let
      v91 :: T_MaybeExports_v91 
      v91 = \ (T_MaybeExports_vIn91 ) -> ( let
         _exportsX38 = Control.Monad.Identity.runIdentity (attach_T_Exports (arg_exports_))
         (T_Exports_vOut37 _exportsIcons _exportsImods _exportsIself _exportsItypes _exportsIvalues) = inv_Exports_s38 _exportsX38 (T_Exports_vIn37 )
         _lhsOcons :: IdSet
         _lhsOcons = rule421 _exportsIcons
         _lhsOmods :: IdSet
         _lhsOmods = rule422 _exportsImods
         _lhsOtypes :: IdSet
         _lhsOtypes = rule423 _exportsItypes
         _lhsOvalues :: IdSet
         _lhsOvalues = rule424 _exportsIvalues
         _self = rule425 _exportsIself
         _lhsOself :: MaybeExports
         _lhsOself = rule426 _self
         __result_ = T_MaybeExports_vOut91 _lhsOcons _lhsOmods _lhsOself _lhsOtypes _lhsOvalues
         in __result_ )
     in C_MaybeExports_s92 v91
   {-# INLINE rule421 #-}
   rule421 = \ ((_exportsIcons) :: IdSet) ->
     _exportsIcons
   {-# INLINE rule422 #-}
   rule422 = \ ((_exportsImods) :: IdSet) ->
     _exportsImods
   {-# INLINE rule423 #-}
   rule423 = \ ((_exportsItypes) :: IdSet) ->
     _exportsItypes
   {-# INLINE rule424 #-}
   rule424 = \ ((_exportsIvalues) :: IdSet) ->
     _exportsIvalues
   {-# INLINE rule425 #-}
   rule425 = \ ((_exportsIself) :: Exports) ->
     MaybeExports_Just _exportsIself
   {-# INLINE rule426 #-}
   rule426 = \ _self ->
     _self

-- MaybeExpression ---------------------------------------------
-- wrapper
data Inh_MaybeExpression  = Inh_MaybeExpression { dictionaryEnv_Inh_MaybeExpression :: (DictionaryEnvironment) }
data Syn_MaybeExpression  = Syn_MaybeExpression { core_Syn_MaybeExpression :: ( Maybe Core.Expr ), self_Syn_MaybeExpression :: (MaybeExpression) }
{-# INLINABLE wrap_MaybeExpression #-}
wrap_MaybeExpression :: T_MaybeExpression  -> Inh_MaybeExpression  -> (Syn_MaybeExpression )
wrap_MaybeExpression (T_MaybeExpression act) (Inh_MaybeExpression _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeExpression_vIn94 _lhsIdictionaryEnv
        (T_MaybeExpression_vOut94 _lhsOcore _lhsOself) <- return (inv_MaybeExpression_s95 sem arg)
        return (Syn_MaybeExpression _lhsOcore _lhsOself)
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
data T_MaybeExpression_vIn94  = T_MaybeExpression_vIn94 (DictionaryEnvironment)
data T_MaybeExpression_vOut94  = T_MaybeExpression_vOut94 ( Maybe Core.Expr ) (MaybeExpression)
{-# NOINLINE sem_MaybeExpression_Nothing #-}
sem_MaybeExpression_Nothing ::  T_MaybeExpression 
sem_MaybeExpression_Nothing  = T_MaybeExpression (return st95) where
   {-# NOINLINE st95 #-}
   st95 = let
      v94 :: T_MaybeExpression_v94 
      v94 = \ (T_MaybeExpression_vIn94 _lhsIdictionaryEnv) -> ( let
         _lhsOcore ::  Maybe Core.Expr 
         _lhsOcore = rule427  ()
         _self = rule428  ()
         _lhsOself :: MaybeExpression
         _lhsOself = rule429 _self
         __result_ = T_MaybeExpression_vOut94 _lhsOcore _lhsOself
         in __result_ )
     in C_MaybeExpression_s95 v94
   {-# INLINE rule427 #-}
   rule427 = \  (_ :: ()) ->
                                 Nothing
   {-# INLINE rule428 #-}
   rule428 = \  (_ :: ()) ->
     MaybeExpression_Nothing
   {-# INLINE rule429 #-}
   rule429 = \ _self ->
     _self
{-# NOINLINE sem_MaybeExpression_Just #-}
sem_MaybeExpression_Just :: T_Expression  -> T_MaybeExpression 
sem_MaybeExpression_Just arg_expression_ = T_MaybeExpression (return st95) where
   {-# NOINLINE st95 #-}
   st95 = let
      v94 :: T_MaybeExpression_v94 
      v94 = \ (T_MaybeExpression_vIn94 _lhsIdictionaryEnv) -> ( let
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _lhsOcore ::  Maybe Core.Expr 
         _lhsOcore = rule430 _expressionIcore
         _self = rule431 _expressionIself
         _lhsOself :: MaybeExpression
         _lhsOself = rule432 _self
         _expressionOdictionaryEnv = rule433 _lhsIdictionaryEnv
         __result_ = T_MaybeExpression_vOut94 _lhsOcore _lhsOself
         in __result_ )
     in C_MaybeExpression_s95 v94
   {-# INLINE rule430 #-}
   rule430 = \ ((_expressionIcore) ::  Core.Expr ) ->
                                 Just _expressionIcore
   {-# INLINE rule431 #-}
   rule431 = \ ((_expressionIself) :: Expression) ->
     MaybeExpression_Just _expressionIself
   {-# INLINE rule432 #-}
   rule432 = \ _self ->
     _self
   {-# INLINE rule433 #-}
   rule433 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv

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
         _self = rule434  ()
         _lhsOself :: MaybeImportSpecification
         _lhsOself = rule435 _self
         __result_ = T_MaybeImportSpecification_vOut97 _lhsOself
         in __result_ )
     in C_MaybeImportSpecification_s98 v97
   {-# INLINE rule434 #-}
   rule434 = \  (_ :: ()) ->
     MaybeImportSpecification_Nothing
   {-# INLINE rule435 #-}
   rule435 = \ _self ->
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
         _self = rule436 _importspecificationIself
         _lhsOself :: MaybeImportSpecification
         _lhsOself = rule437 _self
         __result_ = T_MaybeImportSpecification_vOut97 _lhsOself
         in __result_ )
     in C_MaybeImportSpecification_s98 v97
   {-# INLINE rule436 #-}
   rule436 = \ ((_importspecificationIself) :: ImportSpecification) ->
     MaybeImportSpecification_Just _importspecificationIself
   {-# INLINE rule437 #-}
   rule437 = \ _self ->
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
         _self = rule438  ()
         _lhsOself :: MaybeInt
         _lhsOself = rule439 _self
         __result_ = T_MaybeInt_vOut100 _lhsOself
         in __result_ )
     in C_MaybeInt_s101 v100
   {-# INLINE rule438 #-}
   rule438 = \  (_ :: ()) ->
     MaybeInt_Nothing
   {-# INLINE rule439 #-}
   rule439 = \ _self ->
     _self
{-# NOINLINE sem_MaybeInt_Just #-}
sem_MaybeInt_Just :: (Int) -> T_MaybeInt 
sem_MaybeInt_Just arg_int_ = T_MaybeInt (return st101) where
   {-# NOINLINE st101 #-}
   st101 = let
      v100 :: T_MaybeInt_v100 
      v100 = \ (T_MaybeInt_vIn100 ) -> ( let
         _self = rule440 arg_int_
         _lhsOself :: MaybeInt
         _lhsOself = rule441 _self
         __result_ = T_MaybeInt_vOut100 _lhsOself
         in __result_ )
     in C_MaybeInt_s101 v100
   {-# INLINE rule440 #-}
   rule440 = \ int_ ->
     MaybeInt_Just int_
   {-# INLINE rule441 #-}
   rule441 = \ _self ->
     _self

-- MaybeName ---------------------------------------------------
-- wrapper
data Inh_MaybeName  = Inh_MaybeName {  }
data Syn_MaybeName  = Syn_MaybeName { isNothing_Syn_MaybeName :: (Bool), name_Syn_MaybeName :: ( Maybe Name ), self_Syn_MaybeName :: (MaybeName) }
{-# INLINABLE wrap_MaybeName #-}
wrap_MaybeName :: T_MaybeName  -> Inh_MaybeName  -> (Syn_MaybeName )
wrap_MaybeName (T_MaybeName act) (Inh_MaybeName ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeName_vIn103 
        (T_MaybeName_vOut103 _lhsOisNothing _lhsOname _lhsOself) <- return (inv_MaybeName_s104 sem arg)
        return (Syn_MaybeName _lhsOisNothing _lhsOname _lhsOself)
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
data T_MaybeName_vOut103  = T_MaybeName_vOut103 (Bool) ( Maybe Name ) (MaybeName)
{-# NOINLINE sem_MaybeName_Nothing #-}
sem_MaybeName_Nothing ::  T_MaybeName 
sem_MaybeName_Nothing  = T_MaybeName (return st104) where
   {-# NOINLINE st104 #-}
   st104 = let
      v103 :: T_MaybeName_v103 
      v103 = \ (T_MaybeName_vIn103 ) -> ( let
         _lhsOisNothing :: Bool
         _lhsOisNothing = rule442  ()
         _lhsOname ::  Maybe Name 
         _lhsOname = rule443  ()
         _self = rule444  ()
         _lhsOself :: MaybeName
         _lhsOself = rule445 _self
         __result_ = T_MaybeName_vOut103 _lhsOisNothing _lhsOname _lhsOself
         in __result_ )
     in C_MaybeName_s104 v103
   {-# INLINE rule442 #-}
   rule442 = \  (_ :: ()) ->
                                            True
   {-# INLINE rule443 #-}
   rule443 = \  (_ :: ()) ->
                                            Nothing
   {-# INLINE rule444 #-}
   rule444 = \  (_ :: ()) ->
     MaybeName_Nothing
   {-# INLINE rule445 #-}
   rule445 = \ _self ->
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
         _lhsOisNothing :: Bool
         _lhsOisNothing = rule446  ()
         _lhsOname ::  Maybe Name 
         _lhsOname = rule447 _nameIself
         _self = rule448 _nameIself
         _lhsOself :: MaybeName
         _lhsOself = rule449 _self
         __result_ = T_MaybeName_vOut103 _lhsOisNothing _lhsOname _lhsOself
         in __result_ )
     in C_MaybeName_s104 v103
   {-# INLINE rule446 #-}
   rule446 = \  (_ :: ()) ->
                                            False
   {-# INLINE rule447 #-}
   rule447 = \ ((_nameIself) :: Name) ->
                                            Just _nameIself
   {-# INLINE rule448 #-}
   rule448 = \ ((_nameIself) :: Name) ->
     MaybeName_Just _nameIself
   {-# INLINE rule449 #-}
   rule449 = \ _self ->
     _self

-- MaybeNames --------------------------------------------------
-- wrapper
data Inh_MaybeNames  = Inh_MaybeNames {  }
data Syn_MaybeNames  = Syn_MaybeNames { names_Syn_MaybeNames :: ( Maybe [Name] ), self_Syn_MaybeNames :: (MaybeNames) }
{-# INLINABLE wrap_MaybeNames #-}
wrap_MaybeNames :: T_MaybeNames  -> Inh_MaybeNames  -> (Syn_MaybeNames )
wrap_MaybeNames (T_MaybeNames act) (Inh_MaybeNames ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_MaybeNames_vIn106 
        (T_MaybeNames_vOut106 _lhsOnames _lhsOself) <- return (inv_MaybeNames_s107 sem arg)
        return (Syn_MaybeNames _lhsOnames _lhsOself)
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
data T_MaybeNames_vOut106  = T_MaybeNames_vOut106 ( Maybe [Name] ) (MaybeNames)
{-# NOINLINE sem_MaybeNames_Nothing #-}
sem_MaybeNames_Nothing ::  T_MaybeNames 
sem_MaybeNames_Nothing  = T_MaybeNames (return st107) where
   {-# NOINLINE st107 #-}
   st107 = let
      v106 :: T_MaybeNames_v106 
      v106 = \ (T_MaybeNames_vIn106 ) -> ( let
         _lhsOnames ::  Maybe [Name] 
         _lhsOnames = rule450  ()
         _self = rule451  ()
         _lhsOself :: MaybeNames
         _lhsOself = rule452 _self
         __result_ = T_MaybeNames_vOut106 _lhsOnames _lhsOself
         in __result_ )
     in C_MaybeNames_s107 v106
   {-# INLINE rule450 #-}
   rule450 = \  (_ :: ()) ->
                                        Nothing
   {-# INLINE rule451 #-}
   rule451 = \  (_ :: ()) ->
     MaybeNames_Nothing
   {-# INLINE rule452 #-}
   rule452 = \ _self ->
     _self
{-# NOINLINE sem_MaybeNames_Just #-}
sem_MaybeNames_Just :: T_Names  -> T_MaybeNames 
sem_MaybeNames_Just arg_names_ = T_MaybeNames (return st107) where
   {-# NOINLINE st107 #-}
   st107 = let
      v106 :: T_MaybeNames_v106 
      v106 = \ (T_MaybeNames_vIn106 ) -> ( let
         _namesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_names_))
         (T_Names_vOut115 _namesInames _namesIself) = inv_Names_s116 _namesX116 (T_Names_vIn115 )
         _lhsOnames ::  Maybe [Name] 
         _lhsOnames = rule453 _namesInames
         _self = rule454 _namesIself
         _lhsOself :: MaybeNames
         _lhsOself = rule455 _self
         __result_ = T_MaybeNames_vOut106 _lhsOnames _lhsOself
         in __result_ )
     in C_MaybeNames_s107 v106
   {-# INLINE rule453 #-}
   rule453 = \ ((_namesInames) :: [Name]) ->
                                        Just _namesInames
   {-# INLINE rule454 #-}
   rule454 = \ ((_namesIself) :: Names) ->
     MaybeNames_Just _namesIself
   {-# INLINE rule455 #-}
   rule455 = \ _self ->
     _self

-- Module ------------------------------------------------------
-- wrapper
data Inh_Module  = Inh_Module { dictionaryEnv_Inh_Module :: (DictionaryEnvironment), extraDecls_Inh_Module :: ( [Core.CoreDecl] ), importEnv_Inh_Module :: (ImportEnvironment), toplevelTypes_Inh_Module :: (TypeEnvironment) }
data Syn_Module  = Syn_Module { core_Syn_Module :: ( Core.CoreModule ), self_Syn_Module :: (Module) }
{-# INLINABLE wrap_Module #-}
wrap_Module :: T_Module  -> Inh_Module  -> (Syn_Module )
wrap_Module (T_Module act) (Inh_Module _lhsIdictionaryEnv _lhsIextraDecls _lhsIimportEnv _lhsItoplevelTypes) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Module_vIn109 _lhsIdictionaryEnv _lhsIextraDecls _lhsIimportEnv _lhsItoplevelTypes
        (T_Module_vOut109 _lhsOcore _lhsOself) <- return (inv_Module_s110 sem arg)
        return (Syn_Module _lhsOcore _lhsOself)
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
data T_Module_vIn109  = T_Module_vIn109 (DictionaryEnvironment) ( [Core.CoreDecl] ) (ImportEnvironment) (TypeEnvironment)
data T_Module_vOut109  = T_Module_vOut109 ( Core.CoreModule ) (Module)
{-# NOINLINE sem_Module_Module #-}
sem_Module_Module :: T_Range  -> T_MaybeName  -> T_MaybeExports  -> T_Body  -> T_Module 
sem_Module_Module arg_range_ arg_name_ arg_exports_ arg_body_ = T_Module (return st110) where
   {-# NOINLINE st110 #-}
   st110 = let
      v109 :: T_Module_v109 
      v109 = \ (T_Module_vIn109 _lhsIdictionaryEnv _lhsIextraDecls _lhsIimportEnv _lhsItoplevelTypes) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX104 = Control.Monad.Identity.runIdentity (attach_T_MaybeName (arg_name_))
         _exportsX92 = Control.Monad.Identity.runIdentity (attach_T_MaybeExports (arg_exports_))
         _bodyX14 = Control.Monad.Identity.runIdentity (attach_T_Body (arg_body_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_MaybeName_vOut103 _nameIisNothing _nameIname _nameIself) = inv_MaybeName_s104 _nameX104 (T_MaybeName_vIn103 )
         (T_MaybeExports_vOut91 _exportsIcons _exportsImods _exportsIself _exportsItypes _exportsIvalues) = inv_MaybeExports_s92 _exportsX92 (T_MaybeExports_vIn91 )
         (T_Body_vOut13 _bodyIdecls _bodyIself) = inv_Body_s14 _bodyX14 (T_Body_vIn13 _bodyOdictionaryEnv _bodyOimportEnv)
         _lhsOcore ::  Core.CoreModule 
         _lhsOcore = rule456 _lhsItoplevelTypes _module_
         _module_ = rule457 _bodyIdecls _lhsIextraDecls _nameIname
         _self = rule458 _bodyIself _exportsIself _nameIself _rangeIself
         _lhsOself :: Module
         _lhsOself = rule459 _self
         _bodyOdictionaryEnv = rule460 _lhsIdictionaryEnv
         _bodyOimportEnv = rule461 _lhsIimportEnv
         __result_ = T_Module_vOut109 _lhsOcore _lhsOself
         in __result_ )
     in C_Module_s110 v109
   {-# INLINE rule456 #-}
   rule456 = \ ((_lhsItoplevelTypes) :: TypeEnvironment) _module_ ->
                             _module_ { Module.moduleDecls =
                                  insertedMain _lhsItoplevelTypes : Module.moduleDecls _module_ }
   {-# INLINE rule457 #-}
   rule457 = \ ((_bodyIdecls) ::  [CoreDecl] ) ((_lhsIextraDecls) ::  [Core.CoreDecl] ) ((_nameIname) ::  Maybe Name ) ->
                      everythingPublicButPrelude
                          (makeCoreModule (fmap idFromName _nameIname)
                              ( _bodyIdecls ++ _lhsIextraDecls
                              ))
   {-# INLINE rule458 #-}
   rule458 = \ ((_bodyIself) :: Body) ((_exportsIself) :: MaybeExports) ((_nameIself) :: MaybeName) ((_rangeIself) :: Range) ->
     Module_Module _rangeIself _nameIself _exportsIself _bodyIself
   {-# INLINE rule459 #-}
   rule459 = \ _self ->
     _self
   {-# INLINE rule460 #-}
   rule460 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule461 #-}
   rule461 = \ ((_lhsIimportEnv) :: ImportEnvironment) ->
     _lhsIimportEnv

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
         _self = rule462 _moduleIself _rangeIself arg_name_
         _lhsOself :: Name
         _lhsOself = rule463 _self
         __result_ = T_Name_vOut112 _lhsOself
         in __result_ )
     in C_Name_s113 v112
   {-# INLINE rule462 #-}
   rule462 = \ ((_moduleIself) :: Strings) ((_rangeIself) :: Range) name_ ->
     Name_Identifier _rangeIself _moduleIself name_
   {-# INLINE rule463 #-}
   rule463 = \ _self ->
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
         _self = rule464 _moduleIself _rangeIself arg_name_
         _lhsOself :: Name
         _lhsOself = rule465 _self
         __result_ = T_Name_vOut112 _lhsOself
         in __result_ )
     in C_Name_s113 v112
   {-# INLINE rule464 #-}
   rule464 = \ ((_moduleIself) :: Strings) ((_rangeIself) :: Range) name_ ->
     Name_Operator _rangeIself _moduleIself name_
   {-# INLINE rule465 #-}
   rule465 = \ _self ->
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
         _self = rule466 _moduleIself _rangeIself arg_name_
         _lhsOself :: Name
         _lhsOself = rule467 _self
         __result_ = T_Name_vOut112 _lhsOself
         in __result_ )
     in C_Name_s113 v112
   {-# INLINE rule466 #-}
   rule466 = \ ((_moduleIself) :: Strings) ((_rangeIself) :: Range) name_ ->
     Name_Special _rangeIself _moduleIself name_
   {-# INLINE rule467 #-}
   rule467 = \ _self ->
     _self

-- Names -------------------------------------------------------
-- wrapper
data Inh_Names  = Inh_Names {  }
data Syn_Names  = Syn_Names { names_Syn_Names :: ([Name]), self_Syn_Names :: (Names) }
{-# INLINABLE wrap_Names #-}
wrap_Names :: T_Names  -> Inh_Names  -> (Syn_Names )
wrap_Names (T_Names act) (Inh_Names ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Names_vIn115 
        (T_Names_vOut115 _lhsOnames _lhsOself) <- return (inv_Names_s116 sem arg)
        return (Syn_Names _lhsOnames _lhsOself)
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
data T_Names_vOut115  = T_Names_vOut115 ([Name]) (Names)
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
         (T_Names_vOut115 _tlInames _tlIself) = inv_Names_s116 _tlX116 (T_Names_vIn115 )
         _lhsOnames :: [Name]
         _lhsOnames = rule468 _hdIself _tlInames
         _self = rule469 _hdIself _tlIself
         _lhsOself :: Names
         _lhsOself = rule470 _self
         __result_ = T_Names_vOut115 _lhsOnames _lhsOself
         in __result_ )
     in C_Names_s116 v115
   {-# INLINE rule468 #-}
   rule468 = \ ((_hdIself) :: Name) ((_tlInames) :: [Name]) ->
                             _hdIself : _tlInames
   {-# INLINE rule469 #-}
   rule469 = \ ((_hdIself) :: Name) ((_tlIself) :: Names) ->
     (:) _hdIself _tlIself
   {-# INLINE rule470 #-}
   rule470 = \ _self ->
     _self
{-# NOINLINE sem_Names_Nil #-}
sem_Names_Nil ::  T_Names 
sem_Names_Nil  = T_Names (return st116) where
   {-# NOINLINE st116 #-}
   st116 = let
      v115 :: T_Names_v115 
      v115 = \ (T_Names_vIn115 ) -> ( let
         _lhsOnames :: [Name]
         _lhsOnames = rule471  ()
         _self = rule472  ()
         _lhsOself :: Names
         _lhsOself = rule473 _self
         __result_ = T_Names_vOut115 _lhsOnames _lhsOself
         in __result_ )
     in C_Names_s116 v115
   {-# INLINE rule471 #-}
   rule471 = \  (_ :: ()) ->
                             []
   {-# INLINE rule472 #-}
   rule472 = \  (_ :: ()) ->
     []
   {-# INLINE rule473 #-}
   rule473 = \ _self ->
     _self

-- Pattern -----------------------------------------------------
-- wrapper
data Inh_Pattern  = Inh_Pattern {  }
data Syn_Pattern  = Syn_Pattern { self_Syn_Pattern :: (Pattern), vars_Syn_Pattern :: ( [Name] ) }
{-# INLINABLE wrap_Pattern #-}
wrap_Pattern :: T_Pattern  -> Inh_Pattern  -> (Syn_Pattern )
wrap_Pattern (T_Pattern act) (Inh_Pattern ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Pattern_vIn118 
        (T_Pattern_vOut118 _lhsOself _lhsOvars) <- return (inv_Pattern_s119 sem arg)
        return (Syn_Pattern _lhsOself _lhsOvars)
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
data T_Pattern_vIn118  = T_Pattern_vIn118 
data T_Pattern_vOut118  = T_Pattern_vOut118 (Pattern) ( [Name] )
{-# NOINLINE sem_Pattern_Hole #-}
sem_Pattern_Hole :: T_Range  -> (Integer) -> T_Pattern 
sem_Pattern_Hole arg_range_ arg_id_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule474  ()
         _self = rule475 _rangeIself arg_id_
         _lhsOself :: Pattern
         _lhsOself = rule476 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule474 #-}
   rule474 = \  (_ :: ()) ->
     []
   {-# INLINE rule475 #-}
   rule475 = \ ((_rangeIself) :: Range) id_ ->
     Pattern_Hole _rangeIself id_
   {-# INLINE rule476 #-}
   rule476 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_Literal #-}
sem_Pattern_Literal :: T_Range  -> T_Literal  -> T_Pattern 
sem_Pattern_Literal arg_range_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalIcore _literalIself) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule477  ()
         _self = rule478 _literalIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule479 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule477 #-}
   rule477 = \  (_ :: ()) ->
     []
   {-# INLINE rule478 #-}
   rule478 = \ ((_literalIself) :: Literal) ((_rangeIself) :: Range) ->
     Pattern_Literal _rangeIself _literalIself
   {-# INLINE rule479 #-}
   rule479 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_Variable #-}
sem_Pattern_Variable :: T_Range  -> T_Name  -> T_Pattern 
sem_Pattern_Variable arg_range_ arg_name_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule480 _nameIself
         _self = rule481 _nameIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule482 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule480 #-}
   rule480 = \ ((_nameIself) :: Name) ->
                                            [ _nameIself ]
   {-# INLINE rule481 #-}
   rule481 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Pattern_Variable _rangeIself _nameIself
   {-# INLINE rule482 #-}
   rule482 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_Constructor #-}
sem_Pattern_Constructor :: T_Range  -> T_Name  -> T_Patterns  -> T_Pattern 
sem_Pattern_Constructor arg_range_ arg_name_ arg_patterns_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Patterns_vOut121 _patternsIlength _patternsIself _patternsIvars) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule483 _patternsIvars
         _self = rule484 _nameIself _patternsIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule485 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule483 #-}
   rule483 = \ ((_patternsIvars) ::  [Name] ) ->
     _patternsIvars
   {-# INLINE rule484 #-}
   rule484 = \ ((_nameIself) :: Name) ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     Pattern_Constructor _rangeIself _nameIself _patternsIself
   {-# INLINE rule485 #-}
   rule485 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_Parenthesized #-}
sem_Pattern_Parenthesized :: T_Range  -> T_Pattern  -> T_Pattern 
sem_Pattern_Parenthesized arg_range_ arg_pattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIself _patternIvars) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule486 _patternIvars
         _self = rule487 _patternIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule488 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule486 #-}
   rule486 = \ ((_patternIvars) ::  [Name] ) ->
     _patternIvars
   {-# INLINE rule487 #-}
   rule487 = \ ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     Pattern_Parenthesized _rangeIself _patternIself
   {-# INLINE rule488 #-}
   rule488 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_InfixConstructor #-}
sem_Pattern_InfixConstructor :: T_Range  -> T_Pattern  -> T_Name  -> T_Pattern  -> T_Pattern 
sem_Pattern_InfixConstructor arg_range_ arg_leftPattern_ arg_constructorOperator_ arg_rightPattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _leftPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_leftPattern_))
         _constructorOperatorX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_constructorOperator_))
         _rightPatternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_rightPattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _leftPatternIself _leftPatternIvars) = inv_Pattern_s119 _leftPatternX119 (T_Pattern_vIn118 )
         (T_Name_vOut112 _constructorOperatorIself) = inv_Name_s113 _constructorOperatorX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _rightPatternIself _rightPatternIvars) = inv_Pattern_s119 _rightPatternX119 (T_Pattern_vIn118 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule489 _leftPatternIvars _rightPatternIvars
         _self = rule490 _constructorOperatorIself _leftPatternIself _rangeIself _rightPatternIself
         _lhsOself :: Pattern
         _lhsOself = rule491 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule489 #-}
   rule489 = \ ((_leftPatternIvars) ::  [Name] ) ((_rightPatternIvars) ::  [Name] ) ->
     _leftPatternIvars  ++  _rightPatternIvars
   {-# INLINE rule490 #-}
   rule490 = \ ((_constructorOperatorIself) :: Name) ((_leftPatternIself) :: Pattern) ((_rangeIself) :: Range) ((_rightPatternIself) :: Pattern) ->
     Pattern_InfixConstructor _rangeIself _leftPatternIself _constructorOperatorIself _rightPatternIself
   {-# INLINE rule491 #-}
   rule491 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_List #-}
sem_Pattern_List :: T_Range  -> T_Patterns  -> T_Pattern 
sem_Pattern_List arg_range_ arg_patterns_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Patterns_vOut121 _patternsIlength _patternsIself _patternsIvars) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule492 _patternsIvars
         _self = rule493 _patternsIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule494 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule492 #-}
   rule492 = \ ((_patternsIvars) ::  [Name] ) ->
     _patternsIvars
   {-# INLINE rule493 #-}
   rule493 = \ ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     Pattern_List _rangeIself _patternsIself
   {-# INLINE rule494 #-}
   rule494 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_Tuple #-}
sem_Pattern_Tuple :: T_Range  -> T_Patterns  -> T_Pattern 
sem_Pattern_Tuple arg_range_ arg_patterns_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternsX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_patterns_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Patterns_vOut121 _patternsIlength _patternsIself _patternsIvars) = inv_Patterns_s122 _patternsX122 (T_Patterns_vIn121 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule495 _patternsIvars
         _self = rule496 _patternsIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule497 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule495 #-}
   rule495 = \ ((_patternsIvars) ::  [Name] ) ->
     _patternsIvars
   {-# INLINE rule496 #-}
   rule496 = \ ((_patternsIself) :: Patterns) ((_rangeIself) :: Range) ->
     Pattern_Tuple _rangeIself _patternsIself
   {-# INLINE rule497 #-}
   rule497 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_Record #-}
sem_Pattern_Record :: T_Range  -> T_Name  -> T_RecordPatternBindings  -> T_Pattern 
sem_Pattern_Record arg_range_ arg_name_ arg_recordPatternBindings_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _recordPatternBindingsX146 = Control.Monad.Identity.runIdentity (attach_T_RecordPatternBindings (arg_recordPatternBindings_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_RecordPatternBindings_vOut145 _recordPatternBindingsIself) = inv_RecordPatternBindings_s146 _recordPatternBindingsX146 (T_RecordPatternBindings_vIn145 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule498  ()
         _self = rule499 _nameIself _rangeIself _recordPatternBindingsIself
         _lhsOself :: Pattern
         _lhsOself = rule500 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule498 #-}
   rule498 = \  (_ :: ()) ->
     []
   {-# INLINE rule499 #-}
   rule499 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ((_recordPatternBindingsIself) :: RecordPatternBindings) ->
     Pattern_Record _rangeIself _nameIself _recordPatternBindingsIself
   {-# INLINE rule500 #-}
   rule500 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_Negate #-}
sem_Pattern_Negate :: T_Range  -> T_Literal  -> T_Pattern 
sem_Pattern_Negate arg_range_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalIcore _literalIself) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule501  ()
         _self = rule502 _literalIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule503 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule501 #-}
   rule501 = \  (_ :: ()) ->
     []
   {-# INLINE rule502 #-}
   rule502 = \ ((_literalIself) :: Literal) ((_rangeIself) :: Range) ->
     Pattern_Negate _rangeIself _literalIself
   {-# INLINE rule503 #-}
   rule503 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_As #-}
sem_Pattern_As :: T_Range  -> T_Name  -> T_Pattern  -> T_Pattern 
sem_Pattern_As arg_range_ arg_name_ arg_pattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _patternIself _patternIvars) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule504 _nameIself _patternIvars
         _self = rule505 _nameIself _patternIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule506 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule504 #-}
   rule504 = \ ((_nameIself) :: Name) ((_patternIvars) ::  [Name] ) ->
                                            _nameIself : _patternIvars
   {-# INLINE rule505 #-}
   rule505 = \ ((_nameIself) :: Name) ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     Pattern_As _rangeIself _nameIself _patternIself
   {-# INLINE rule506 #-}
   rule506 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_Wildcard #-}
sem_Pattern_Wildcard :: T_Range  -> T_Pattern 
sem_Pattern_Wildcard arg_range_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule507  ()
         _self = rule508 _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule509 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule507 #-}
   rule507 = \  (_ :: ()) ->
     []
   {-# INLINE rule508 #-}
   rule508 = \ ((_rangeIself) :: Range) ->
     Pattern_Wildcard _rangeIself
   {-# INLINE rule509 #-}
   rule509 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_Irrefutable #-}
sem_Pattern_Irrefutable :: T_Range  -> T_Pattern  -> T_Pattern 
sem_Pattern_Irrefutable arg_range_ arg_pattern_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIself _patternIvars) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule510 _patternIvars
         _self = rule511 _patternIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule512 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule510 #-}
   rule510 = \ ((_patternIvars) ::  [Name] ) ->
     _patternIvars
   {-# INLINE rule511 #-}
   rule511 = \ ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     Pattern_Irrefutable _rangeIself _patternIself
   {-# INLINE rule512 #-}
   rule512 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_Successor #-}
sem_Pattern_Successor :: T_Range  -> T_Name  -> T_Literal  -> T_Pattern 
sem_Pattern_Successor arg_range_ arg_name_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Literal_vOut85 _literalIcore _literalIself) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule513  ()
         _self = rule514 _literalIself _nameIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule515 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule513 #-}
   rule513 = \  (_ :: ()) ->
     []
   {-# INLINE rule514 #-}
   rule514 = \ ((_literalIself) :: Literal) ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Pattern_Successor _rangeIself _nameIself _literalIself
   {-# INLINE rule515 #-}
   rule515 = \ _self ->
     _self
{-# NOINLINE sem_Pattern_NegateFloat #-}
sem_Pattern_NegateFloat :: T_Range  -> T_Literal  -> T_Pattern 
sem_Pattern_NegateFloat arg_range_ arg_literal_ = T_Pattern (return st119) where
   {-# NOINLINE st119 #-}
   st119 = let
      v118 :: T_Pattern_v118 
      v118 = \ (T_Pattern_vIn118 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _literalX86 = Control.Monad.Identity.runIdentity (attach_T_Literal (arg_literal_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Literal_vOut85 _literalIcore _literalIself) = inv_Literal_s86 _literalX86 (T_Literal_vIn85 )
         _lhsOvars ::  [Name] 
         _lhsOvars = rule516  ()
         _self = rule517 _literalIself _rangeIself
         _lhsOself :: Pattern
         _lhsOself = rule518 _self
         __result_ = T_Pattern_vOut118 _lhsOself _lhsOvars
         in __result_ )
     in C_Pattern_s119 v118
   {-# INLINE rule516 #-}
   rule516 = \  (_ :: ()) ->
     []
   {-# INLINE rule517 #-}
   rule517 = \ ((_literalIself) :: Literal) ((_rangeIself) :: Range) ->
     Pattern_NegateFloat _rangeIself _literalIself
   {-# INLINE rule518 #-}
   rule518 = \ _self ->
     _self

-- Patterns ----------------------------------------------------
-- wrapper
data Inh_Patterns  = Inh_Patterns {  }
data Syn_Patterns  = Syn_Patterns { length_Syn_Patterns :: (Int), self_Syn_Patterns :: (Patterns), vars_Syn_Patterns :: ( [Name] ) }
{-# INLINABLE wrap_Patterns #-}
wrap_Patterns :: T_Patterns  -> Inh_Patterns  -> (Syn_Patterns )
wrap_Patterns (T_Patterns act) (Inh_Patterns ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Patterns_vIn121 
        (T_Patterns_vOut121 _lhsOlength _lhsOself _lhsOvars) <- return (inv_Patterns_s122 sem arg)
        return (Syn_Patterns _lhsOlength _lhsOself _lhsOvars)
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
data T_Patterns_vIn121  = T_Patterns_vIn121 
data T_Patterns_vOut121  = T_Patterns_vOut121 (Int) (Patterns) ( [Name] )
{-# NOINLINE sem_Patterns_Cons #-}
sem_Patterns_Cons :: T_Pattern  -> T_Patterns  -> T_Patterns 
sem_Patterns_Cons arg_hd_ arg_tl_ = T_Patterns (return st122) where
   {-# NOINLINE st122 #-}
   st122 = let
      v121 :: T_Patterns_v121 
      v121 = \ (T_Patterns_vIn121 ) -> ( let
         _hdX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_hd_))
         _tlX122 = Control.Monad.Identity.runIdentity (attach_T_Patterns (arg_tl_))
         (T_Pattern_vOut118 _hdIself _hdIvars) = inv_Pattern_s119 _hdX119 (T_Pattern_vIn118 )
         (T_Patterns_vOut121 _tlIlength _tlIself _tlIvars) = inv_Patterns_s122 _tlX122 (T_Patterns_vIn121 )
         _lhsOlength :: Int
         _lhsOlength = rule519 _tlIlength
         _lhsOvars ::  [Name] 
         _lhsOvars = rule520 _hdIvars _tlIvars
         _self = rule521 _hdIself _tlIself
         _lhsOself :: Patterns
         _lhsOself = rule522 _self
         __result_ = T_Patterns_vOut121 _lhsOlength _lhsOself _lhsOvars
         in __result_ )
     in C_Patterns_s122 v121
   {-# INLINE rule519 #-}
   rule519 = \ ((_tlIlength) :: Int) ->
                          1 + _tlIlength
   {-# INLINE rule520 #-}
   rule520 = \ ((_hdIvars) ::  [Name] ) ((_tlIvars) ::  [Name] ) ->
     _hdIvars  ++  _tlIvars
   {-# INLINE rule521 #-}
   rule521 = \ ((_hdIself) :: Pattern) ((_tlIself) :: Patterns) ->
     (:) _hdIself _tlIself
   {-# INLINE rule522 #-}
   rule522 = \ _self ->
     _self
{-# NOINLINE sem_Patterns_Nil #-}
sem_Patterns_Nil ::  T_Patterns 
sem_Patterns_Nil  = T_Patterns (return st122) where
   {-# NOINLINE st122 #-}
   st122 = let
      v121 :: T_Patterns_v121 
      v121 = \ (T_Patterns_vIn121 ) -> ( let
         _lhsOlength :: Int
         _lhsOlength = rule523  ()
         _lhsOvars ::  [Name] 
         _lhsOvars = rule524  ()
         _self = rule525  ()
         _lhsOself :: Patterns
         _lhsOself = rule526 _self
         __result_ = T_Patterns_vOut121 _lhsOlength _lhsOself _lhsOvars
         in __result_ )
     in C_Patterns_s122 v121
   {-# INLINE rule523 #-}
   rule523 = \  (_ :: ()) ->
                          0
   {-# INLINE rule524 #-}
   rule524 = \  (_ :: ()) ->
     []
   {-# INLINE rule525 #-}
   rule525 = \  (_ :: ()) ->
     []
   {-# INLINE rule526 #-}
   rule526 = \ _self ->
     _self

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
         _self = rule527 arg_column_ arg_filename_ arg_line_
         _lhsOself :: Position
         _lhsOself = rule528 _self
         __result_ = T_Position_vOut124 _lhsOself
         in __result_ )
     in C_Position_s125 v124
   {-# INLINE rule527 #-}
   rule527 = \ column_ filename_ line_ ->
     Position_Position filename_ line_ column_
   {-# INLINE rule528 #-}
   rule528 = \ _self ->
     _self
{-# NOINLINE sem_Position_Unknown #-}
sem_Position_Unknown ::  T_Position 
sem_Position_Unknown  = T_Position (return st125) where
   {-# NOINLINE st125 #-}
   st125 = let
      v124 :: T_Position_v124 
      v124 = \ (T_Position_vIn124 ) -> ( let
         _self = rule529  ()
         _lhsOself :: Position
         _lhsOself = rule530 _self
         __result_ = T_Position_vOut124 _lhsOself
         in __result_ )
     in C_Position_s125 v124
   {-# INLINE rule529 #-}
   rule529 = \  (_ :: ()) ->
     Position_Unknown
   {-# INLINE rule530 #-}
   rule530 = \ _self ->
     _self

-- Qualifier ---------------------------------------------------
-- wrapper
data Inh_Qualifier  = Inh_Qualifier { dictionaryEnv_Inh_Qualifier :: (DictionaryEnvironment) }
data Syn_Qualifier  = Syn_Qualifier { core_Syn_Qualifier :: ( Core.Expr -> Core.Expr ), self_Syn_Qualifier :: (Qualifier) }
{-# INLINABLE wrap_Qualifier #-}
wrap_Qualifier :: T_Qualifier  -> Inh_Qualifier  -> (Syn_Qualifier )
wrap_Qualifier (T_Qualifier act) (Inh_Qualifier _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Qualifier_vIn127 _lhsIdictionaryEnv
        (T_Qualifier_vOut127 _lhsOcore _lhsOself) <- return (inv_Qualifier_s128 sem arg)
        return (Syn_Qualifier _lhsOcore _lhsOself)
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
data T_Qualifier_vIn127  = T_Qualifier_vIn127 (DictionaryEnvironment)
data T_Qualifier_vOut127  = T_Qualifier_vOut127 ( Core.Expr -> Core.Expr ) (Qualifier)
{-# NOINLINE sem_Qualifier_Guard #-}
sem_Qualifier_Guard :: T_Range  -> T_Expression  -> T_Qualifier 
sem_Qualifier_Guard arg_range_ arg_guard_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_guard_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _guardIcore _guardIself) = inv_Expression_s41 _guardX41 (T_Expression_vIn40 _guardOdictionaryEnv)
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule531 _guardIcore
         _self = rule532 _guardIself _rangeIself
         _lhsOself :: Qualifier
         _lhsOself = rule533 _self
         _guardOdictionaryEnv = rule534 _lhsIdictionaryEnv
         __result_ = T_Qualifier_vOut127 _lhsOcore _lhsOself
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule531 #-}
   rule531 = \ ((_guardIcore) ::  Core.Expr ) ->
                                       \continue -> if_ _guardIcore continue nil
   {-# INLINE rule532 #-}
   rule532 = \ ((_guardIself) :: Expression) ((_rangeIself) :: Range) ->
     Qualifier_Guard _rangeIself _guardIself
   {-# INLINE rule533 #-}
   rule533 = \ _self ->
     _self
   {-# INLINE rule534 #-}
   rule534 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Qualifier_Let #-}
sem_Qualifier_Let :: T_Range  -> T_Declarations  -> T_Qualifier 
sem_Qualifier_Let arg_range_ arg_declarations_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Declarations_vOut31 _declarationsIdecls _declarationsIpatBindNr _declarationsIself) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 _declarationsOdictionaryEnv _declarationsOimportEnv _declarationsOisTopLevel _declarationsOpatBindNr)
         _importEnv = rule535  ()
         _declarationsOpatBindNr = rule536  ()
         _declarationsOisTopLevel = rule537  ()
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule538 _declarationsIdecls
         _self = rule539 _declarationsIself _rangeIself
         _lhsOself :: Qualifier
         _lhsOself = rule540 _self
         _declarationsOdictionaryEnv = rule541 _lhsIdictionaryEnv
         _declarationsOimportEnv = rule542 _importEnv
         __result_ = T_Qualifier_vOut127 _lhsOcore _lhsOself
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule535 #-}
   rule535 = \  (_ :: ()) ->
                                               internalError "CodeGeneration.ag" "Qualifier.Let" ""
   {-# INLINE rule536 #-}
   rule536 = \  (_ :: ()) ->
                                                     0
   {-# INLINE rule537 #-}
   rule537 = \  (_ :: ()) ->
                                                      False
   {-# INLINE rule538 #-}
   rule538 = \ ((_declarationsIdecls) ::  [CoreDecl] ) ->
                                       \continue -> letrec_ _declarationsIdecls continue
   {-# INLINE rule539 #-}
   rule539 = \ ((_declarationsIself) :: Declarations) ((_rangeIself) :: Range) ->
     Qualifier_Let _rangeIself _declarationsIself
   {-# INLINE rule540 #-}
   rule540 = \ _self ->
     _self
   {-# INLINE rule541 #-}
   rule541 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule542 #-}
   rule542 = \ _importEnv ->
     _importEnv
{-# NOINLINE sem_Qualifier_Generator #-}
sem_Qualifier_Generator :: T_Range  -> T_Pattern  -> T_Expression  -> T_Qualifier 
sem_Qualifier_Generator arg_range_ arg_pattern_ arg_expression_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIself _patternIvars) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule543 _expressionIcore _patternIself
         _self = rule544 _expressionIself _patternIself _rangeIself
         _lhsOself :: Qualifier
         _lhsOself = rule545 _self
         _expressionOdictionaryEnv = rule546 _lhsIdictionaryEnv
         __result_ = T_Qualifier_vOut127 _lhsOcore _lhsOself
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule543 #-}
   rule543 = \ ((_expressionIcore) ::  Core.Expr ) ((_patternIself) :: Pattern) ->
          \continue ->
              let_ nextClauseId nil
                  (let_
                      okId
                      (Core.Lam parameterId
                          (patternToCore (parameterId, _patternIself) continue)
                      )
                      (var "$primConcatMap"
                          `app_` Core.Var okId
                          `app_` _expressionIcore
                      )
                  )
   {-# INLINE rule544 #-}
   rule544 = \ ((_expressionIself) :: Expression) ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     Qualifier_Generator _rangeIself _patternIself _expressionIself
   {-# INLINE rule545 #-}
   rule545 = \ _self ->
     _self
   {-# INLINE rule546 #-}
   rule546 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Qualifier_Empty #-}
sem_Qualifier_Empty :: T_Range  -> T_Qualifier 
sem_Qualifier_Empty arg_range_ = T_Qualifier (return st128) where
   {-# NOINLINE st128 #-}
   st128 = let
      v127 :: T_Qualifier_v127 
      v127 = \ (T_Qualifier_vIn127 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcore ::  Core.Expr -> Core.Expr 
         _lhsOcore = rule547  ()
         _self = rule548 _rangeIself
         _lhsOself :: Qualifier
         _lhsOself = rule549 _self
         __result_ = T_Qualifier_vOut127 _lhsOcore _lhsOself
         in __result_ )
     in C_Qualifier_s128 v127
   {-# INLINE rule547 #-}
   rule547 = \  (_ :: ()) ->
                                       internalError "ToCoreExpr" "Qualifier" "empty qualifiers not supported"
   {-# INLINE rule548 #-}
   rule548 = \ ((_rangeIself) :: Range) ->
     Qualifier_Empty _rangeIself
   {-# INLINE rule549 #-}
   rule549 = \ _self ->
     _self

-- Qualifiers --------------------------------------------------
-- wrapper
data Inh_Qualifiers  = Inh_Qualifiers { dictionaryEnv_Inh_Qualifiers :: (DictionaryEnvironment) }
data Syn_Qualifiers  = Syn_Qualifiers { core_Syn_Qualifiers :: ( [Core.Expr -> Core.Expr] ), self_Syn_Qualifiers :: (Qualifiers) }
{-# INLINABLE wrap_Qualifiers #-}
wrap_Qualifiers :: T_Qualifiers  -> Inh_Qualifiers  -> (Syn_Qualifiers )
wrap_Qualifiers (T_Qualifiers act) (Inh_Qualifiers _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Qualifiers_vIn130 _lhsIdictionaryEnv
        (T_Qualifiers_vOut130 _lhsOcore _lhsOself) <- return (inv_Qualifiers_s131 sem arg)
        return (Syn_Qualifiers _lhsOcore _lhsOself)
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
data T_Qualifiers_vIn130  = T_Qualifiers_vIn130 (DictionaryEnvironment)
data T_Qualifiers_vOut130  = T_Qualifiers_vOut130 ( [Core.Expr -> Core.Expr] ) (Qualifiers)
{-# NOINLINE sem_Qualifiers_Cons #-}
sem_Qualifiers_Cons :: T_Qualifier  -> T_Qualifiers  -> T_Qualifiers 
sem_Qualifiers_Cons arg_hd_ arg_tl_ = T_Qualifiers (return st131) where
   {-# NOINLINE st131 #-}
   st131 = let
      v130 :: T_Qualifiers_v130 
      v130 = \ (T_Qualifiers_vIn130 _lhsIdictionaryEnv) -> ( let
         _hdX128 = Control.Monad.Identity.runIdentity (attach_T_Qualifier (arg_hd_))
         _tlX131 = Control.Monad.Identity.runIdentity (attach_T_Qualifiers (arg_tl_))
         (T_Qualifier_vOut127 _hdIcore _hdIself) = inv_Qualifier_s128 _hdX128 (T_Qualifier_vIn127 _hdOdictionaryEnv)
         (T_Qualifiers_vOut130 _tlIcore _tlIself) = inv_Qualifiers_s131 _tlX131 (T_Qualifiers_vIn130 _tlOdictionaryEnv)
         _lhsOcore ::  [Core.Expr -> Core.Expr] 
         _lhsOcore = rule550 _hdIcore _tlIcore
         _self = rule551 _hdIself _tlIself
         _lhsOself :: Qualifiers
         _lhsOself = rule552 _self
         _hdOdictionaryEnv = rule553 _lhsIdictionaryEnv
         _tlOdictionaryEnv = rule554 _lhsIdictionaryEnv
         __result_ = T_Qualifiers_vOut130 _lhsOcore _lhsOself
         in __result_ )
     in C_Qualifiers_s131 v130
   {-# INLINE rule550 #-}
   rule550 = \ ((_hdIcore) ::  Core.Expr -> Core.Expr ) ((_tlIcore) ::  [Core.Expr -> Core.Expr] ) ->
     _hdIcore  :  _tlIcore
   {-# INLINE rule551 #-}
   rule551 = \ ((_hdIself) :: Qualifier) ((_tlIself) :: Qualifiers) ->
     (:) _hdIself _tlIself
   {-# INLINE rule552 #-}
   rule552 = \ _self ->
     _self
   {-# INLINE rule553 #-}
   rule553 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule554 #-}
   rule554 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Qualifiers_Nil #-}
sem_Qualifiers_Nil ::  T_Qualifiers 
sem_Qualifiers_Nil  = T_Qualifiers (return st131) where
   {-# NOINLINE st131 #-}
   st131 = let
      v130 :: T_Qualifiers_v130 
      v130 = \ (T_Qualifiers_vIn130 _lhsIdictionaryEnv) -> ( let
         _lhsOcore ::  [Core.Expr -> Core.Expr] 
         _lhsOcore = rule555  ()
         _self = rule556  ()
         _lhsOself :: Qualifiers
         _lhsOself = rule557 _self
         __result_ = T_Qualifiers_vOut130 _lhsOcore _lhsOself
         in __result_ )
     in C_Qualifiers_s131 v130
   {-# INLINE rule555 #-}
   rule555 = \  (_ :: ()) ->
     []
   {-# INLINE rule556 #-}
   rule556 = \  (_ :: ()) ->
     []
   {-# INLINE rule557 #-}
   rule557 = \ _self ->
     _self

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
         _self = rule558 _startIself _stopIself
         _lhsOself :: Range
         _lhsOself = rule559 _self
         __result_ = T_Range_vOut133 _lhsOself
         in __result_ )
     in C_Range_s134 v133
   {-# INLINE rule558 #-}
   rule558 = \ ((_startIself) :: Position) ((_stopIself) :: Position) ->
     Range_Range _startIself _stopIself
   {-# INLINE rule559 #-}
   rule559 = \ _self ->
     _self

-- RecordExpressionBinding -------------------------------------
-- wrapper
data Inh_RecordExpressionBinding  = Inh_RecordExpressionBinding { dictionaryEnv_Inh_RecordExpressionBinding :: (DictionaryEnvironment) }
data Syn_RecordExpressionBinding  = Syn_RecordExpressionBinding { self_Syn_RecordExpressionBinding :: (RecordExpressionBinding) }
{-# INLINABLE wrap_RecordExpressionBinding #-}
wrap_RecordExpressionBinding :: T_RecordExpressionBinding  -> Inh_RecordExpressionBinding  -> (Syn_RecordExpressionBinding )
wrap_RecordExpressionBinding (T_RecordExpressionBinding act) (Inh_RecordExpressionBinding _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_RecordExpressionBinding_vIn136 _lhsIdictionaryEnv
        (T_RecordExpressionBinding_vOut136 _lhsOself) <- return (inv_RecordExpressionBinding_s137 sem arg)
        return (Syn_RecordExpressionBinding _lhsOself)
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
data T_RecordExpressionBinding_vIn136  = T_RecordExpressionBinding_vIn136 (DictionaryEnvironment)
data T_RecordExpressionBinding_vOut136  = T_RecordExpressionBinding_vOut136 (RecordExpressionBinding)
{-# NOINLINE sem_RecordExpressionBinding_RecordExpressionBinding #-}
sem_RecordExpressionBinding_RecordExpressionBinding :: T_Range  -> T_Name  -> T_Expression  -> T_RecordExpressionBinding 
sem_RecordExpressionBinding_RecordExpressionBinding arg_range_ arg_name_ arg_expression_ = T_RecordExpressionBinding (return st137) where
   {-# NOINLINE st137 #-}
   st137 = let
      v136 :: T_RecordExpressionBinding_v136 
      v136 = \ (T_RecordExpressionBinding_vIn136 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _self = rule560 _expressionIself _nameIself _rangeIself
         _lhsOself :: RecordExpressionBinding
         _lhsOself = rule561 _self
         _expressionOdictionaryEnv = rule562 _lhsIdictionaryEnv
         __result_ = T_RecordExpressionBinding_vOut136 _lhsOself
         in __result_ )
     in C_RecordExpressionBinding_s137 v136
   {-# INLINE rule560 #-}
   rule560 = \ ((_expressionIself) :: Expression) ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     RecordExpressionBinding_RecordExpressionBinding _rangeIself _nameIself _expressionIself
   {-# INLINE rule561 #-}
   rule561 = \ _self ->
     _self
   {-# INLINE rule562 #-}
   rule562 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv

-- RecordExpressionBindings ------------------------------------
-- wrapper
data Inh_RecordExpressionBindings  = Inh_RecordExpressionBindings { dictionaryEnv_Inh_RecordExpressionBindings :: (DictionaryEnvironment) }
data Syn_RecordExpressionBindings  = Syn_RecordExpressionBindings { self_Syn_RecordExpressionBindings :: (RecordExpressionBindings) }
{-# INLINABLE wrap_RecordExpressionBindings #-}
wrap_RecordExpressionBindings :: T_RecordExpressionBindings  -> Inh_RecordExpressionBindings  -> (Syn_RecordExpressionBindings )
wrap_RecordExpressionBindings (T_RecordExpressionBindings act) (Inh_RecordExpressionBindings _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_RecordExpressionBindings_vIn139 _lhsIdictionaryEnv
        (T_RecordExpressionBindings_vOut139 _lhsOself) <- return (inv_RecordExpressionBindings_s140 sem arg)
        return (Syn_RecordExpressionBindings _lhsOself)
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
data T_RecordExpressionBindings_vIn139  = T_RecordExpressionBindings_vIn139 (DictionaryEnvironment)
data T_RecordExpressionBindings_vOut139  = T_RecordExpressionBindings_vOut139 (RecordExpressionBindings)
{-# NOINLINE sem_RecordExpressionBindings_Cons #-}
sem_RecordExpressionBindings_Cons :: T_RecordExpressionBinding  -> T_RecordExpressionBindings  -> T_RecordExpressionBindings 
sem_RecordExpressionBindings_Cons arg_hd_ arg_tl_ = T_RecordExpressionBindings (return st140) where
   {-# NOINLINE st140 #-}
   st140 = let
      v139 :: T_RecordExpressionBindings_v139 
      v139 = \ (T_RecordExpressionBindings_vIn139 _lhsIdictionaryEnv) -> ( let
         _hdX137 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBinding (arg_hd_))
         _tlX140 = Control.Monad.Identity.runIdentity (attach_T_RecordExpressionBindings (arg_tl_))
         (T_RecordExpressionBinding_vOut136 _hdIself) = inv_RecordExpressionBinding_s137 _hdX137 (T_RecordExpressionBinding_vIn136 _hdOdictionaryEnv)
         (T_RecordExpressionBindings_vOut139 _tlIself) = inv_RecordExpressionBindings_s140 _tlX140 (T_RecordExpressionBindings_vIn139 _tlOdictionaryEnv)
         _self = rule563 _hdIself _tlIself
         _lhsOself :: RecordExpressionBindings
         _lhsOself = rule564 _self
         _hdOdictionaryEnv = rule565 _lhsIdictionaryEnv
         _tlOdictionaryEnv = rule566 _lhsIdictionaryEnv
         __result_ = T_RecordExpressionBindings_vOut139 _lhsOself
         in __result_ )
     in C_RecordExpressionBindings_s140 v139
   {-# INLINE rule563 #-}
   rule563 = \ ((_hdIself) :: RecordExpressionBinding) ((_tlIself) :: RecordExpressionBindings) ->
     (:) _hdIself _tlIself
   {-# INLINE rule564 #-}
   rule564 = \ _self ->
     _self
   {-# INLINE rule565 #-}
   rule565 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule566 #-}
   rule566 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_RecordExpressionBindings_Nil #-}
sem_RecordExpressionBindings_Nil ::  T_RecordExpressionBindings 
sem_RecordExpressionBindings_Nil  = T_RecordExpressionBindings (return st140) where
   {-# NOINLINE st140 #-}
   st140 = let
      v139 :: T_RecordExpressionBindings_v139 
      v139 = \ (T_RecordExpressionBindings_vIn139 _lhsIdictionaryEnv) -> ( let
         _self = rule567  ()
         _lhsOself :: RecordExpressionBindings
         _lhsOself = rule568 _self
         __result_ = T_RecordExpressionBindings_vOut139 _lhsOself
         in __result_ )
     in C_RecordExpressionBindings_s140 v139
   {-# INLINE rule567 #-}
   rule567 = \  (_ :: ()) ->
     []
   {-# INLINE rule568 #-}
   rule568 = \ _self ->
     _self

-- RecordPatternBinding ----------------------------------------
-- wrapper
data Inh_RecordPatternBinding  = Inh_RecordPatternBinding {  }
data Syn_RecordPatternBinding  = Syn_RecordPatternBinding { self_Syn_RecordPatternBinding :: (RecordPatternBinding) }
{-# INLINABLE wrap_RecordPatternBinding #-}
wrap_RecordPatternBinding :: T_RecordPatternBinding  -> Inh_RecordPatternBinding  -> (Syn_RecordPatternBinding )
wrap_RecordPatternBinding (T_RecordPatternBinding act) (Inh_RecordPatternBinding ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_RecordPatternBinding_vIn142 
        (T_RecordPatternBinding_vOut142 _lhsOself) <- return (inv_RecordPatternBinding_s143 sem arg)
        return (Syn_RecordPatternBinding _lhsOself)
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
data T_RecordPatternBinding_vIn142  = T_RecordPatternBinding_vIn142 
data T_RecordPatternBinding_vOut142  = T_RecordPatternBinding_vOut142 (RecordPatternBinding)
{-# NOINLINE sem_RecordPatternBinding_RecordPatternBinding #-}
sem_RecordPatternBinding_RecordPatternBinding :: T_Range  -> T_Name  -> T_Pattern  -> T_RecordPatternBinding 
sem_RecordPatternBinding_RecordPatternBinding arg_range_ arg_name_ arg_pattern_ = T_RecordPatternBinding (return st143) where
   {-# NOINLINE st143 #-}
   st143 = let
      v142 :: T_RecordPatternBinding_v142 
      v142 = \ (T_RecordPatternBinding_vIn142 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         (T_Pattern_vOut118 _patternIself _patternIvars) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         _self = rule569 _nameIself _patternIself _rangeIself
         _lhsOself :: RecordPatternBinding
         _lhsOself = rule570 _self
         __result_ = T_RecordPatternBinding_vOut142 _lhsOself
         in __result_ )
     in C_RecordPatternBinding_s143 v142
   {-# INLINE rule569 #-}
   rule569 = \ ((_nameIself) :: Name) ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     RecordPatternBinding_RecordPatternBinding _rangeIself _nameIself _patternIself
   {-# INLINE rule570 #-}
   rule570 = \ _self ->
     _self

-- RecordPatternBindings ---------------------------------------
-- wrapper
data Inh_RecordPatternBindings  = Inh_RecordPatternBindings {  }
data Syn_RecordPatternBindings  = Syn_RecordPatternBindings { self_Syn_RecordPatternBindings :: (RecordPatternBindings) }
{-# INLINABLE wrap_RecordPatternBindings #-}
wrap_RecordPatternBindings :: T_RecordPatternBindings  -> Inh_RecordPatternBindings  -> (Syn_RecordPatternBindings )
wrap_RecordPatternBindings (T_RecordPatternBindings act) (Inh_RecordPatternBindings ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_RecordPatternBindings_vIn145 
        (T_RecordPatternBindings_vOut145 _lhsOself) <- return (inv_RecordPatternBindings_s146 sem arg)
        return (Syn_RecordPatternBindings _lhsOself)
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
data T_RecordPatternBindings_vIn145  = T_RecordPatternBindings_vIn145 
data T_RecordPatternBindings_vOut145  = T_RecordPatternBindings_vOut145 (RecordPatternBindings)
{-# NOINLINE sem_RecordPatternBindings_Cons #-}
sem_RecordPatternBindings_Cons :: T_RecordPatternBinding  -> T_RecordPatternBindings  -> T_RecordPatternBindings 
sem_RecordPatternBindings_Cons arg_hd_ arg_tl_ = T_RecordPatternBindings (return st146) where
   {-# NOINLINE st146 #-}
   st146 = let
      v145 :: T_RecordPatternBindings_v145 
      v145 = \ (T_RecordPatternBindings_vIn145 ) -> ( let
         _hdX143 = Control.Monad.Identity.runIdentity (attach_T_RecordPatternBinding (arg_hd_))
         _tlX146 = Control.Monad.Identity.runIdentity (attach_T_RecordPatternBindings (arg_tl_))
         (T_RecordPatternBinding_vOut142 _hdIself) = inv_RecordPatternBinding_s143 _hdX143 (T_RecordPatternBinding_vIn142 )
         (T_RecordPatternBindings_vOut145 _tlIself) = inv_RecordPatternBindings_s146 _tlX146 (T_RecordPatternBindings_vIn145 )
         _self = rule571 _hdIself _tlIself
         _lhsOself :: RecordPatternBindings
         _lhsOself = rule572 _self
         __result_ = T_RecordPatternBindings_vOut145 _lhsOself
         in __result_ )
     in C_RecordPatternBindings_s146 v145
   {-# INLINE rule571 #-}
   rule571 = \ ((_hdIself) :: RecordPatternBinding) ((_tlIself) :: RecordPatternBindings) ->
     (:) _hdIself _tlIself
   {-# INLINE rule572 #-}
   rule572 = \ _self ->
     _self
{-# NOINLINE sem_RecordPatternBindings_Nil #-}
sem_RecordPatternBindings_Nil ::  T_RecordPatternBindings 
sem_RecordPatternBindings_Nil  = T_RecordPatternBindings (return st146) where
   {-# NOINLINE st146 #-}
   st146 = let
      v145 :: T_RecordPatternBindings_v145 
      v145 = \ (T_RecordPatternBindings_vIn145 ) -> ( let
         _self = rule573  ()
         _lhsOself :: RecordPatternBindings
         _lhsOself = rule574 _self
         __result_ = T_RecordPatternBindings_vOut145 _lhsOself
         in __result_ )
     in C_RecordPatternBindings_s146 v145
   {-# INLINE rule573 #-}
   rule573 = \  (_ :: ()) ->
     []
   {-# INLINE rule574 #-}
   rule574 = \ _self ->
     _self

-- RightHandSide -----------------------------------------------
-- wrapper
data Inh_RightHandSide  = Inh_RightHandSide { dictionaryEnv_Inh_RightHandSide :: (DictionaryEnvironment) }
data Syn_RightHandSide  = Syn_RightHandSide { core_Syn_RightHandSide :: ( Core.Expr ), isGuarded_Syn_RightHandSide :: (Bool), self_Syn_RightHandSide :: (RightHandSide) }
{-# INLINABLE wrap_RightHandSide #-}
wrap_RightHandSide :: T_RightHandSide  -> Inh_RightHandSide  -> (Syn_RightHandSide )
wrap_RightHandSide (T_RightHandSide act) (Inh_RightHandSide _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_RightHandSide_vIn148 _lhsIdictionaryEnv
        (T_RightHandSide_vOut148 _lhsOcore _lhsOisGuarded _lhsOself) <- return (inv_RightHandSide_s149 sem arg)
        return (Syn_RightHandSide _lhsOcore _lhsOisGuarded _lhsOself)
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
data T_RightHandSide_vIn148  = T_RightHandSide_vIn148 (DictionaryEnvironment)
data T_RightHandSide_vOut148  = T_RightHandSide_vOut148 ( Core.Expr ) (Bool) (RightHandSide)
{-# NOINLINE sem_RightHandSide_Expression #-}
sem_RightHandSide_Expression :: T_Range  -> T_Expression  -> T_MaybeDeclarations  -> T_RightHandSide 
sem_RightHandSide_Expression arg_range_ arg_expression_ arg_where_ = T_RightHandSide (return st149) where
   {-# NOINLINE st149 #-}
   st149 = let
      v148 :: T_RightHandSide_v148 
      v148 = \ (T_RightHandSide_vIn148 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         (T_MaybeDeclarations_vOut88 _whereIcore _whereIself) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 _whereOdictionaryEnv)
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule575 _expressionIcore _whereIcore
         _lhsOisGuarded :: Bool
         _lhsOisGuarded = rule576  ()
         _self = rule577 _expressionIself _rangeIself _whereIself
         _lhsOself :: RightHandSide
         _lhsOself = rule578 _self
         _expressionOdictionaryEnv = rule579 _lhsIdictionaryEnv
         _whereOdictionaryEnv = rule580 _lhsIdictionaryEnv
         __result_ = T_RightHandSide_vOut148 _lhsOcore _lhsOisGuarded _lhsOself
         in __result_ )
     in C_RightHandSide_s149 v148
   {-# INLINE rule575 #-}
   rule575 = \ ((_expressionIcore) ::  Core.Expr ) ((_whereIcore) ::  Core.Expr -> Core.Expr ) ->
                                   _whereIcore _expressionIcore
   {-# INLINE rule576 #-}
   rule576 = \  (_ :: ()) ->
                                        False
   {-# INLINE rule577 #-}
   rule577 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ((_whereIself) :: MaybeDeclarations) ->
     RightHandSide_Expression _rangeIself _expressionIself _whereIself
   {-# INLINE rule578 #-}
   rule578 = \ _self ->
     _self
   {-# INLINE rule579 #-}
   rule579 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule580 #-}
   rule580 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_RightHandSide_Guarded #-}
sem_RightHandSide_Guarded :: T_Range  -> T_GuardedExpressions  -> T_MaybeDeclarations  -> T_RightHandSide 
sem_RightHandSide_Guarded arg_range_ arg_guardedexpressions_ arg_where_ = T_RightHandSide (return st149) where
   {-# NOINLINE st149 #-}
   st149 = let
      v148 :: T_RightHandSide_v148 
      v148 = \ (T_RightHandSide_vIn148 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _guardedexpressionsX65 = Control.Monad.Identity.runIdentity (attach_T_GuardedExpressions (arg_guardedexpressions_))
         _whereX89 = Control.Monad.Identity.runIdentity (attach_T_MaybeDeclarations (arg_where_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_GuardedExpressions_vOut64 _guardedexpressionsIcore _guardedexpressionsIself) = inv_GuardedExpressions_s65 _guardedexpressionsX65 (T_GuardedExpressions_vIn64 _guardedexpressionsOdictionaryEnv)
         (T_MaybeDeclarations_vOut88 _whereIcore _whereIself) = inv_MaybeDeclarations_s89 _whereX89 (T_MaybeDeclarations_vIn88 _whereOdictionaryEnv)
         _lhsOisGuarded :: Bool
         _lhsOisGuarded = rule581  ()
         _lhsOcore ::  Core.Expr 
         _lhsOcore = rule582 _guardedexpressionsIcore _whereIcore
         _self = rule583 _guardedexpressionsIself _rangeIself _whereIself
         _lhsOself :: RightHandSide
         _lhsOself = rule584 _self
         _guardedexpressionsOdictionaryEnv = rule585 _lhsIdictionaryEnv
         _whereOdictionaryEnv = rule586 _lhsIdictionaryEnv
         __result_ = T_RightHandSide_vOut148 _lhsOcore _lhsOisGuarded _lhsOself
         in __result_ )
     in C_RightHandSide_s149 v148
   {-# INLINE rule581 #-}
   rule581 = \  (_ :: ()) ->
                                        True
   {-# INLINE rule582 #-}
   rule582 = \ ((_guardedexpressionsIcore) ::  [Core.Expr -> Core.Expr] ) ((_whereIcore) ::  Core.Expr -> Core.Expr ) ->
          _whereIcore (foldr ($) (Core.Var nextClauseId) _guardedexpressionsIcore)
   {-# INLINE rule583 #-}
   rule583 = \ ((_guardedexpressionsIself) :: GuardedExpressions) ((_rangeIself) :: Range) ((_whereIself) :: MaybeDeclarations) ->
     RightHandSide_Guarded _rangeIself _guardedexpressionsIself _whereIself
   {-# INLINE rule584 #-}
   rule584 = \ _self ->
     _self
   {-# INLINE rule585 #-}
   rule585 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule586 #-}
   rule586 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv

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
         (T_Names_vOut115 _typevariablesInames _typevariablesIself) = inv_Names_s116 _typevariablesX116 (T_Names_vIn115 )
         _lhsOname :: Name
         _lhsOname = rule587 _nameIself
         _lhsOtypevariables :: Names
         _lhsOtypevariables = rule588 _typevariablesIself
         _self = rule589 _nameIself _rangeIself _typevariablesIself
         _lhsOself :: SimpleType
         _lhsOself = rule590 _self
         __result_ = T_SimpleType_vOut151 _lhsOname _lhsOself _lhsOtypevariables
         in __result_ )
     in C_SimpleType_s152 v151
   {-# INLINE rule587 #-}
   rule587 = \ ((_nameIself) :: Name) ->
                                        _nameIself
   {-# INLINE rule588 #-}
   rule588 = \ ((_typevariablesIself) :: Names) ->
                                        _typevariablesIself
   {-# INLINE rule589 #-}
   rule589 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ((_typevariablesIself) :: Names) ->
     SimpleType_SimpleType _rangeIself _nameIself _typevariablesIself
   {-# INLINE rule590 #-}
   rule590 = \ _self ->
     _self

-- Statement ---------------------------------------------------
-- wrapper
data Inh_Statement  = Inh_Statement { dictionaryEnv_Inh_Statement :: (DictionaryEnvironment) }
data Syn_Statement  = Syn_Statement { core_Syn_Statement :: ( Maybe Core.Expr -> Core.Expr ), self_Syn_Statement :: (Statement) }
{-# INLINABLE wrap_Statement #-}
wrap_Statement :: T_Statement  -> Inh_Statement  -> (Syn_Statement )
wrap_Statement (T_Statement act) (Inh_Statement _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Statement_vIn154 _lhsIdictionaryEnv
        (T_Statement_vOut154 _lhsOcore _lhsOself) <- return (inv_Statement_s155 sem arg)
        return (Syn_Statement _lhsOcore _lhsOself)
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
data T_Statement_vIn154  = T_Statement_vIn154 (DictionaryEnvironment)
data T_Statement_vOut154  = T_Statement_vOut154 ( Maybe Core.Expr -> Core.Expr ) (Statement)
{-# NOINLINE sem_Statement_Expression #-}
sem_Statement_Expression :: T_Range  -> T_Expression  -> T_Statement 
sem_Statement_Expression arg_range_ arg_expression_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _lhsOcore ::  Maybe Core.Expr -> Core.Expr 
         _lhsOcore = rule591 _expressionIcore
         _self = rule592 _expressionIself _rangeIself
         _lhsOself :: Statement
         _lhsOself = rule593 _self
         _expressionOdictionaryEnv = rule594 _lhsIdictionaryEnv
         __result_ = T_Statement_vOut154 _lhsOcore _lhsOself
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule591 #-}
   rule591 = \ ((_expressionIcore) ::  Core.Expr ) ->
              \theRest ->
                  case theRest of
                      Nothing   -> _expressionIcore
                      Just rest -> bind _expressionIcore (Core.Lam dummyId rest)
   {-# INLINE rule592 #-}
   rule592 = \ ((_expressionIself) :: Expression) ((_rangeIself) :: Range) ->
     Statement_Expression _rangeIself _expressionIself
   {-# INLINE rule593 #-}
   rule593 = \ _self ->
     _self
   {-# INLINE rule594 #-}
   rule594 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Statement_Let #-}
sem_Statement_Let :: T_Range  -> T_Declarations  -> T_Statement 
sem_Statement_Let arg_range_ arg_declarations_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _declarationsX32 = Control.Monad.Identity.runIdentity (attach_T_Declarations (arg_declarations_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Declarations_vOut31 _declarationsIdecls _declarationsIpatBindNr _declarationsIself) = inv_Declarations_s32 _declarationsX32 (T_Declarations_vIn31 _declarationsOdictionaryEnv _declarationsOimportEnv _declarationsOisTopLevel _declarationsOpatBindNr)
         _importEnv = rule595  ()
         _declarationsOpatBindNr = rule596  ()
         _declarationsOisTopLevel = rule597  ()
         _lhsOcore ::  Maybe Core.Expr -> Core.Expr 
         _lhsOcore = rule598 _declarationsIdecls
         _self = rule599 _declarationsIself _rangeIself
         _lhsOself :: Statement
         _lhsOself = rule600 _self
         _declarationsOdictionaryEnv = rule601 _lhsIdictionaryEnv
         _declarationsOimportEnv = rule602 _importEnv
         __result_ = T_Statement_vOut154 _lhsOcore _lhsOself
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule595 #-}
   rule595 = \  (_ :: ()) ->
                                               internalError "CodeGeneration.ag" "Statement.Let" ""
   {-# INLINE rule596 #-}
   rule596 = \  (_ :: ()) ->
                                                     0
   {-# INLINE rule597 #-}
   rule597 = \  (_ :: ()) ->
                                                      False
   {-# INLINE rule598 #-}
   rule598 = \ ((_declarationsIdecls) ::  [CoreDecl] ) ->
              \theRest ->
                  case theRest of
                      Nothing   -> internalError "ToCoreExpr" "Statement" "'let' can't be last in 'do'"
                      Just rest -> letrec_ _declarationsIdecls rest
   {-# INLINE rule599 #-}
   rule599 = \ ((_declarationsIself) :: Declarations) ((_rangeIself) :: Range) ->
     Statement_Let _rangeIself _declarationsIself
   {-# INLINE rule600 #-}
   rule600 = \ _self ->
     _self
   {-# INLINE rule601 #-}
   rule601 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule602 #-}
   rule602 = \ _importEnv ->
     _importEnv
{-# NOINLINE sem_Statement_Generator #-}
sem_Statement_Generator :: T_Range  -> T_Pattern  -> T_Expression  -> T_Statement 
sem_Statement_Generator arg_range_ arg_pattern_ arg_expression_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _patternX119 = Control.Monad.Identity.runIdentity (attach_T_Pattern (arg_pattern_))
         _expressionX41 = Control.Monad.Identity.runIdentity (attach_T_Expression (arg_expression_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Pattern_vOut118 _patternIself _patternIvars) = inv_Pattern_s119 _patternX119 (T_Pattern_vIn118 )
         (T_Expression_vOut40 _expressionIcore _expressionIself) = inv_Expression_s41 _expressionX41 (T_Expression_vIn40 _expressionOdictionaryEnv)
         _lhsOcore ::  Maybe Core.Expr -> Core.Expr 
         _lhsOcore = rule603 _expressionIcore _patternIself _rangeIself
         _self = rule604 _expressionIself _patternIself _rangeIself
         _lhsOself :: Statement
         _lhsOself = rule605 _self
         _expressionOdictionaryEnv = rule606 _lhsIdictionaryEnv
         __result_ = T_Statement_vOut154 _lhsOcore _lhsOself
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule603 #-}
   rule603 = \ ((_expressionIcore) ::  Core.Expr ) ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
          \theRest -> case theRest of
              Nothing   -> internalError "ToCoreExpr" "Statement" "generator can't be last in 'do'"
              Just rest ->
                  let_ nextClauseId (patternMatchFail "generator" _rangeIself)
                      (let_
                          okId
                          (Core.Lam parameterId
                              (patternToCore (parameterId, _patternIself) rest)
                          )
                          (_expressionIcore `bind` Core.Var okId)
                      )
   {-# INLINE rule604 #-}
   rule604 = \ ((_expressionIself) :: Expression) ((_patternIself) :: Pattern) ((_rangeIself) :: Range) ->
     Statement_Generator _rangeIself _patternIself _expressionIself
   {-# INLINE rule605 #-}
   rule605 = \ _self ->
     _self
   {-# INLINE rule606 #-}
   rule606 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Statement_Empty #-}
sem_Statement_Empty :: T_Range  -> T_Statement 
sem_Statement_Empty arg_range_ = T_Statement (return st155) where
   {-# NOINLINE st155 #-}
   st155 = let
      v154 :: T_Statement_v154 
      v154 = \ (T_Statement_vIn154 _lhsIdictionaryEnv) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         _lhsOcore ::  Maybe Core.Expr -> Core.Expr 
         _lhsOcore = rule607  ()
         _self = rule608 _rangeIself
         _lhsOself :: Statement
         _lhsOself = rule609 _self
         __result_ = T_Statement_vOut154 _lhsOcore _lhsOself
         in __result_ )
     in C_Statement_s155 v154
   {-# INLINE rule607 #-}
   rule607 = \  (_ :: ()) ->
              \theRest ->
                  case theRest of
                      Nothing   -> internalError "ToCoreExpr" "Statement" "empty statements not supported"
                      Just rest -> rest
   {-# INLINE rule608 #-}
   rule608 = \ ((_rangeIself) :: Range) ->
     Statement_Empty _rangeIself
   {-# INLINE rule609 #-}
   rule609 = \ _self ->
     _self

-- Statements --------------------------------------------------
-- wrapper
data Inh_Statements  = Inh_Statements { dictionaryEnv_Inh_Statements :: (DictionaryEnvironment) }
data Syn_Statements  = Syn_Statements { core_Syn_Statements :: ( [Maybe Core.Expr -> Core.Expr] ), self_Syn_Statements :: (Statements) }
{-# INLINABLE wrap_Statements #-}
wrap_Statements :: T_Statements  -> Inh_Statements  -> (Syn_Statements )
wrap_Statements (T_Statements act) (Inh_Statements _lhsIdictionaryEnv) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Statements_vIn157 _lhsIdictionaryEnv
        (T_Statements_vOut157 _lhsOcore _lhsOself) <- return (inv_Statements_s158 sem arg)
        return (Syn_Statements _lhsOcore _lhsOself)
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
data T_Statements_vIn157  = T_Statements_vIn157 (DictionaryEnvironment)
data T_Statements_vOut157  = T_Statements_vOut157 ( [Maybe Core.Expr -> Core.Expr] ) (Statements)
{-# NOINLINE sem_Statements_Cons #-}
sem_Statements_Cons :: T_Statement  -> T_Statements  -> T_Statements 
sem_Statements_Cons arg_hd_ arg_tl_ = T_Statements (return st158) where
   {-# NOINLINE st158 #-}
   st158 = let
      v157 :: T_Statements_v157 
      v157 = \ (T_Statements_vIn157 _lhsIdictionaryEnv) -> ( let
         _hdX155 = Control.Monad.Identity.runIdentity (attach_T_Statement (arg_hd_))
         _tlX158 = Control.Monad.Identity.runIdentity (attach_T_Statements (arg_tl_))
         (T_Statement_vOut154 _hdIcore _hdIself) = inv_Statement_s155 _hdX155 (T_Statement_vIn154 _hdOdictionaryEnv)
         (T_Statements_vOut157 _tlIcore _tlIself) = inv_Statements_s158 _tlX158 (T_Statements_vIn157 _tlOdictionaryEnv)
         _lhsOcore ::  [Maybe Core.Expr -> Core.Expr] 
         _lhsOcore = rule610 _hdIcore _tlIcore
         _self = rule611 _hdIself _tlIself
         _lhsOself :: Statements
         _lhsOself = rule612 _self
         _hdOdictionaryEnv = rule613 _lhsIdictionaryEnv
         _tlOdictionaryEnv = rule614 _lhsIdictionaryEnv
         __result_ = T_Statements_vOut157 _lhsOcore _lhsOself
         in __result_ )
     in C_Statements_s158 v157
   {-# INLINE rule610 #-}
   rule610 = \ ((_hdIcore) ::  Maybe Core.Expr -> Core.Expr ) ((_tlIcore) ::  [Maybe Core.Expr -> Core.Expr] ) ->
     _hdIcore  :  _tlIcore
   {-# INLINE rule611 #-}
   rule611 = \ ((_hdIself) :: Statement) ((_tlIself) :: Statements) ->
     (:) _hdIself _tlIself
   {-# INLINE rule612 #-}
   rule612 = \ _self ->
     _self
   {-# INLINE rule613 #-}
   rule613 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
   {-# INLINE rule614 #-}
   rule614 = \ ((_lhsIdictionaryEnv) :: DictionaryEnvironment) ->
     _lhsIdictionaryEnv
{-# NOINLINE sem_Statements_Nil #-}
sem_Statements_Nil ::  T_Statements 
sem_Statements_Nil  = T_Statements (return st158) where
   {-# NOINLINE st158 #-}
   st158 = let
      v157 :: T_Statements_v157 
      v157 = \ (T_Statements_vIn157 _lhsIdictionaryEnv) -> ( let
         _lhsOcore ::  [Maybe Core.Expr -> Core.Expr] 
         _lhsOcore = rule615  ()
         _self = rule616  ()
         _lhsOself :: Statements
         _lhsOself = rule617 _self
         __result_ = T_Statements_vOut157 _lhsOcore _lhsOself
         in __result_ )
     in C_Statements_s158 v157
   {-# INLINE rule615 #-}
   rule615 = \  (_ :: ()) ->
     []
   {-# INLINE rule616 #-}
   rule616 = \  (_ :: ()) ->
     []
   {-# INLINE rule617 #-}
   rule617 = \ _self ->
     _self

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
         _self = rule618 _tlIself arg_hd_
         _lhsOself :: Strings
         _lhsOself = rule619 _self
         __result_ = T_Strings_vOut160 _lhsOself
         in __result_ )
     in C_Strings_s161 v160
   {-# INLINE rule618 #-}
   rule618 = \ ((_tlIself) :: Strings) hd_ ->
     (:) hd_ _tlIself
   {-# INLINE rule619 #-}
   rule619 = \ _self ->
     _self
{-# NOINLINE sem_Strings_Nil #-}
sem_Strings_Nil ::  T_Strings 
sem_Strings_Nil  = T_Strings (return st161) where
   {-# NOINLINE st161 #-}
   st161 = let
      v160 :: T_Strings_v160 
      v160 = \ (T_Strings_vIn160 ) -> ( let
         _self = rule620  ()
         _lhsOself :: Strings
         _lhsOself = rule621 _self
         __result_ = T_Strings_vOut160 _lhsOself
         in __result_ )
     in C_Strings_s161 v160
   {-# INLINE rule620 #-}
   rule620 = \  (_ :: ()) ->
     []
   {-# INLINE rule621 #-}
   rule621 = \ _self ->
     _self

-- Type --------------------------------------------------------
-- wrapper
data Inh_Type  = Inh_Type {  }
data Syn_Type  = Syn_Type { self_Syn_Type :: (Type) }
{-# INLINABLE wrap_Type #-}
wrap_Type :: T_Type  -> Inh_Type  -> (Syn_Type )
wrap_Type (T_Type act) (Inh_Type ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Type_vIn163 
        (T_Type_vOut163 _lhsOself) <- return (inv_Type_s164 sem arg)
        return (Syn_Type _lhsOself)
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
data T_Type_vIn163  = T_Type_vIn163 
data T_Type_vOut163  = T_Type_vOut163 (Type)
{-# NOINLINE sem_Type_Application #-}
sem_Type_Application :: T_Range  -> (Bool) -> T_Type  -> T_Types  -> T_Type 
sem_Type_Application arg_range_ arg_prefix_ arg_function_ arg_arguments_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _functionX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_function_))
         _argumentsX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_arguments_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Type_vOut163 _functionIself) = inv_Type_s164 _functionX164 (T_Type_vIn163 )
         (T_Types_vOut166 _argumentsIself) = inv_Types_s167 _argumentsX167 (T_Types_vIn166 )
         _self = rule622 _argumentsIself _functionIself _rangeIself arg_prefix_
         _lhsOself :: Type
         _lhsOself = rule623 _self
         __result_ = T_Type_vOut163 _lhsOself
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule622 #-}
   rule622 = \ ((_argumentsIself) :: Types) ((_functionIself) :: Type) ((_rangeIself) :: Range) prefix_ ->
     Type_Application _rangeIself prefix_ _functionIself _argumentsIself
   {-# INLINE rule623 #-}
   rule623 = \ _self ->
     _self
{-# NOINLINE sem_Type_Variable #-}
sem_Type_Variable :: T_Range  -> T_Name  -> T_Type 
sem_Type_Variable arg_range_ arg_name_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _self = rule624 _nameIself _rangeIself
         _lhsOself :: Type
         _lhsOself = rule625 _self
         __result_ = T_Type_vOut163 _lhsOself
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule624 #-}
   rule624 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Type_Variable _rangeIself _nameIself
   {-# INLINE rule625 #-}
   rule625 = \ _self ->
     _self
{-# NOINLINE sem_Type_Constructor #-}
sem_Type_Constructor :: T_Range  -> T_Name  -> T_Type 
sem_Type_Constructor arg_range_ arg_name_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _nameX113 = Control.Monad.Identity.runIdentity (attach_T_Name (arg_name_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Name_vOut112 _nameIself) = inv_Name_s113 _nameX113 (T_Name_vIn112 )
         _self = rule626 _nameIself _rangeIself
         _lhsOself :: Type
         _lhsOself = rule627 _self
         __result_ = T_Type_vOut163 _lhsOself
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule626 #-}
   rule626 = \ ((_nameIself) :: Name) ((_rangeIself) :: Range) ->
     Type_Constructor _rangeIself _nameIself
   {-# INLINE rule627 #-}
   rule627 = \ _self ->
     _self
{-# NOINLINE sem_Type_Qualified #-}
sem_Type_Qualified :: T_Range  -> T_ContextItems  -> T_Type  -> T_Type 
sem_Type_Qualified arg_range_ arg_context_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _contextX26 = Control.Monad.Identity.runIdentity (attach_T_ContextItems (arg_context_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_ContextItems_vOut25 _contextIself) = inv_ContextItems_s26 _contextX26 (T_ContextItems_vIn25 )
         (T_Type_vOut163 _typeIself) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _self = rule628 _contextIself _rangeIself _typeIself
         _lhsOself :: Type
         _lhsOself = rule629 _self
         __result_ = T_Type_vOut163 _lhsOself
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule628 #-}
   rule628 = \ ((_contextIself) :: ContextItems) ((_rangeIself) :: Range) ((_typeIself) :: Type) ->
     Type_Qualified _rangeIself _contextIself _typeIself
   {-# INLINE rule629 #-}
   rule629 = \ _self ->
     _self
{-# NOINLINE sem_Type_Forall #-}
sem_Type_Forall :: T_Range  -> T_Names  -> T_Type  -> T_Type 
sem_Type_Forall arg_range_ arg_typevariables_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typevariablesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_typevariables_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _typevariablesInames _typevariablesIself) = inv_Names_s116 _typevariablesX116 (T_Names_vIn115 )
         (T_Type_vOut163 _typeIself) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _self = rule630 _rangeIself _typeIself _typevariablesIself
         _lhsOself :: Type
         _lhsOself = rule631 _self
         __result_ = T_Type_vOut163 _lhsOself
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule630 #-}
   rule630 = \ ((_rangeIself) :: Range) ((_typeIself) :: Type) ((_typevariablesIself) :: Names) ->
     Type_Forall _rangeIself _typevariablesIself _typeIself
   {-# INLINE rule631 #-}
   rule631 = \ _self ->
     _self
{-# NOINLINE sem_Type_Exists #-}
sem_Type_Exists :: T_Range  -> T_Names  -> T_Type  -> T_Type 
sem_Type_Exists arg_range_ arg_typevariables_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typevariablesX116 = Control.Monad.Identity.runIdentity (attach_T_Names (arg_typevariables_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Names_vOut115 _typevariablesInames _typevariablesIself) = inv_Names_s116 _typevariablesX116 (T_Names_vIn115 )
         (T_Type_vOut163 _typeIself) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _self = rule632 _rangeIself _typeIself _typevariablesIself
         _lhsOself :: Type
         _lhsOself = rule633 _self
         __result_ = T_Type_vOut163 _lhsOself
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule632 #-}
   rule632 = \ ((_rangeIself) :: Range) ((_typeIself) :: Type) ((_typevariablesIself) :: Names) ->
     Type_Exists _rangeIself _typevariablesIself _typeIself
   {-# INLINE rule633 #-}
   rule633 = \ _self ->
     _self
{-# NOINLINE sem_Type_Parenthesized #-}
sem_Type_Parenthesized :: T_Range  -> T_Type  -> T_Type 
sem_Type_Parenthesized arg_range_ arg_type_ = T_Type (return st164) where
   {-# NOINLINE st164 #-}
   st164 = let
      v163 :: T_Type_v163 
      v163 = \ (T_Type_vIn163 ) -> ( let
         _rangeX134 = Control.Monad.Identity.runIdentity (attach_T_Range (arg_range_))
         _typeX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_type_))
         (T_Range_vOut133 _rangeIself) = inv_Range_s134 _rangeX134 (T_Range_vIn133 )
         (T_Type_vOut163 _typeIself) = inv_Type_s164 _typeX164 (T_Type_vIn163 )
         _self = rule634 _rangeIself _typeIself
         _lhsOself :: Type
         _lhsOself = rule635 _self
         __result_ = T_Type_vOut163 _lhsOself
         in __result_ )
     in C_Type_s164 v163
   {-# INLINE rule634 #-}
   rule634 = \ ((_rangeIself) :: Range) ((_typeIself) :: Type) ->
     Type_Parenthesized _rangeIself _typeIself
   {-# INLINE rule635 #-}
   rule635 = \ _self ->
     _self

-- Types -------------------------------------------------------
-- wrapper
data Inh_Types  = Inh_Types {  }
data Syn_Types  = Syn_Types { self_Syn_Types :: (Types) }
{-# INLINABLE wrap_Types #-}
wrap_Types :: T_Types  -> Inh_Types  -> (Syn_Types )
wrap_Types (T_Types act) (Inh_Types ) =
   Control.Monad.Identity.runIdentity (
     do sem <- act
        let arg = T_Types_vIn166 
        (T_Types_vOut166 _lhsOself) <- return (inv_Types_s167 sem arg)
        return (Syn_Types _lhsOself)
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
data T_Types_vIn166  = T_Types_vIn166 
data T_Types_vOut166  = T_Types_vOut166 (Types)
{-# NOINLINE sem_Types_Cons #-}
sem_Types_Cons :: T_Type  -> T_Types  -> T_Types 
sem_Types_Cons arg_hd_ arg_tl_ = T_Types (return st167) where
   {-# NOINLINE st167 #-}
   st167 = let
      v166 :: T_Types_v166 
      v166 = \ (T_Types_vIn166 ) -> ( let
         _hdX164 = Control.Monad.Identity.runIdentity (attach_T_Type (arg_hd_))
         _tlX167 = Control.Monad.Identity.runIdentity (attach_T_Types (arg_tl_))
         (T_Type_vOut163 _hdIself) = inv_Type_s164 _hdX164 (T_Type_vIn163 )
         (T_Types_vOut166 _tlIself) = inv_Types_s167 _tlX167 (T_Types_vIn166 )
         _self = rule636 _hdIself _tlIself
         _lhsOself :: Types
         _lhsOself = rule637 _self
         __result_ = T_Types_vOut166 _lhsOself
         in __result_ )
     in C_Types_s167 v166
   {-# INLINE rule636 #-}
   rule636 = \ ((_hdIself) :: Type) ((_tlIself) :: Types) ->
     (:) _hdIself _tlIself
   {-# INLINE rule637 #-}
   rule637 = \ _self ->
     _self
{-# NOINLINE sem_Types_Nil #-}
sem_Types_Nil ::  T_Types 
sem_Types_Nil  = T_Types (return st167) where
   {-# NOINLINE st167 #-}
   st167 = let
      v166 :: T_Types_v166 
      v166 = \ (T_Types_vIn166 ) -> ( let
         _self = rule638  ()
         _lhsOself :: Types
         _lhsOself = rule639 _self
         __result_ = T_Types_vOut166 _lhsOself
         in __result_ )
     in C_Types_s167 v166
   {-# INLINE rule638 #-}
   rule638 = \  (_ :: ()) ->
     []
   {-# INLINE rule639 #-}
   rule639 = \ _self ->
     _self
