

-- UUAGC 0.9.40.3 (StaticAnalysis/Inferencers/KindInferencing.ag)
module StaticAnalysis.Inferencers.KindInferencing where

import Top.Types
import Top.Solver.Greedy
import Top.Solver
import Top.Constraint.Information
import StaticAnalysis.Miscellaneous.TypeConstraints
import Syntax.UHA_Syntax
import Main.Args
import qualified Data.Map as M

import StaticAnalysis.Miscellaneous.TypeConstraints
import Utils.Utils (internalError)
import ModuleSystem.ImportEnvironment hiding (setTypeSynonyms)
import StaticAnalysis.Messages.KindErrors
import Data.Char (isLower)
import StaticAnalysis.Inferencers.BindingGroupAnalysis (Assumptions, PatternAssumptions, noAssumptions, combine, single, topSort) 


type KindEnvironment = M.Map Name TpScheme
type KindConstraint  = TypeConstraint  KindError
type KindConstraints = TypeConstraints KindError

type BindingGroups = [BindingGroup]
type BindingGroup  = (PatternAssumptions,Assumptions,KindConstraints)

combineBindingGroup :: BindingGroup -> BindingGroup -> BindingGroup
combineBindingGroup (e1,a1,c1) (e2,a2,c2) = (e1 `M.union` e2,a1 `combine` a2,c1++c2)

concatBindingGroups :: BindingGroups -> BindingGroup
concatBindingGroups = foldr combineBindingGroup emptyBindingGroup

emptyBindingGroup :: BindingGroup
emptyBindingGroup = (noAssumptions, noAssumptions, [])

performBindingGroup :: BindingGroups -> (PatternAssumptions, Assumptions, KindConstraints)
performBindingGroup = glueGroups . bindingGroupAnalysis    
   where   
      bindingGroupAnalysis :: BindingGroups -> BindingGroups
      bindingGroupAnalysis cs
         = let indexMap = concat (zipWith f cs [0..])
               f (env,_,_) i = [ (n,i) | n <- M.keys env ]
               edges    = concat (zipWith f' cs [0..])
               f' (_,ass,_) i = [ (i,j)| n <- M.keys ass, (n',j) <- indexMap, n==n' ]
               list = topSort (length cs-1) edges
           in map (concatBindingGroups . map (cs !!)) list
           
      glueGroups :: BindingGroups -> (PatternAssumptions, Assumptions, KindConstraints)
      glueGroups = foldr op (noAssumptions, noAssumptions, []) 
         where
            op (env, aset, cset) (environment, assumptions, constraints) = 
               let (cset1,aset')        = (env .===. aset)            (\n -> unexpected $ "BindingGroup.same "++show n)
                   (cset2,assumptions') = (!<==!) [] env assumptions  (\n -> unexpected $ "BindingGroup.instance "++show n)
               in ( env `M.union` environment
                  , aset' `combine` assumptions'
                  , cset1 ++ cset ++ cset2 ++ constraints
                  )             

getKindsFromImportEnvironment :: ImportEnvironment -> KindEnvironment
getKindsFromImportEnvironment = M.map f . typeConstructors
   where f i = generalizeAll ([] .=>. foldr (.->.) star (replicate i star))

getTypeVariables :: Assumptions -> Names
getTypeVariables = filter p . M.keys
   where p n = case show n of
                  []  -> False
                  c:_ -> isLower c

unexpected :: String -> KindError
unexpected msg = 
   internalError "KindInferencing.ag" "unexpected" ("unexpected kind error: "++msg)

instance TypeConstraintInfo KindError
instance PolyTypeConstraintInfo KindError

(<==>) :: Kind -> Kind -> ((Kind, Kind) -> KindError) -> KindConstraint
(k1 <==> k2) info = (k1 .==. k2) (info (k1, k2))
-- Alternative -------------------------------------------------
-- cata
sem_Alternative :: Alternative ->
                   T_Alternative
sem_Alternative (Alternative_Alternative _range _pattern _righthandside) =
    (sem_Alternative_Alternative (sem_Range _range) (sem_Pattern _pattern) (sem_RightHandSide _righthandside))
sem_Alternative (Alternative_Empty _range) =
    (sem_Alternative_Empty (sem_Range _range))
sem_Alternative (Alternative_Feedback _range _feedback _alternative) =
    (sem_Alternative_Feedback (sem_Range _range) _feedback (sem_Alternative _alternative))
sem_Alternative (Alternative_Hole _range _id) =
    (sem_Alternative_Hole (sem_Range _range) _id)
-- semantic domain
type T_Alternative = BindingGroups ->
                     Int ->
                     ( BindingGroups,Int,Alternative)
sem_Alternative_Alternative :: T_Range ->
                               T_Pattern ->
                               T_RightHandSide ->
                               T_Alternative
sem_Alternative_Alternative range_ pattern_ righthandside_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Alternative
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _righthandsideObindingGroups :: BindingGroups
              _righthandsideOkappaUnique :: Int
              _rangeIself :: Range
              _patternIself :: Pattern
              _righthandsideIbindingGroups :: BindingGroups
              _righthandsideIkappaUnique :: Int
              _righthandsideIself :: RightHandSide
              _self =
                  Alternative_Alternative _rangeIself _patternIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _righthandsideIbindingGroups
              _lhsOkappaUnique =
                  _righthandsideIkappaUnique
              _righthandsideObindingGroups =
                  _lhsIbindingGroups
              _righthandsideOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _patternIself) =
                  pattern_
              ( _righthandsideIbindingGroups,_righthandsideIkappaUnique,_righthandsideIself) =
                  righthandside_ _righthandsideObindingGroups _righthandsideOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Alternative_Empty :: T_Range ->
                         T_Alternative
sem_Alternative_Empty range_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Alternative
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _self =
                  Alternative_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Alternative_Feedback :: T_Range ->
                            String ->
                            T_Alternative ->
                            T_Alternative
sem_Alternative_Feedback range_ feedback_ alternative_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Alternative
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _alternativeObindingGroups :: BindingGroups
              _alternativeOkappaUnique :: Int
              _rangeIself :: Range
              _alternativeIbindingGroups :: BindingGroups
              _alternativeIkappaUnique :: Int
              _alternativeIself :: Alternative
              _self =
                  Alternative_Feedback _rangeIself feedback_ _alternativeIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _alternativeIbindingGroups
              _lhsOkappaUnique =
                  _alternativeIkappaUnique
              _alternativeObindingGroups =
                  _lhsIbindingGroups
              _alternativeOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _alternativeIbindingGroups,_alternativeIkappaUnique,_alternativeIself) =
                  alternative_ _alternativeObindingGroups _alternativeOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Alternative_Hole :: T_Range ->
                        Integer ->
                        T_Alternative
sem_Alternative_Hole range_ id_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Alternative
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _self =
                  Alternative_Hole _rangeIself id_
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- Alternatives ------------------------------------------------
-- cata
sem_Alternatives :: Alternatives ->
                    T_Alternatives
sem_Alternatives list =
    (Prelude.foldr sem_Alternatives_Cons sem_Alternatives_Nil (Prelude.map sem_Alternative list))
-- semantic domain
type T_Alternatives = BindingGroups ->
                      Int ->
                      ( BindingGroups,Int,Alternatives)
sem_Alternatives_Cons :: T_Alternative ->
                         T_Alternatives ->
                         T_Alternatives
sem_Alternatives_Cons hd_ tl_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Alternatives
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _hdObindingGroups :: BindingGroups
              _hdOkappaUnique :: Int
              _tlObindingGroups :: BindingGroups
              _tlOkappaUnique :: Int
              _hdIbindingGroups :: BindingGroups
              _hdIkappaUnique :: Int
              _hdIself :: Alternative
              _tlIbindingGroups :: BindingGroups
              _tlIkappaUnique :: Int
              _tlIself :: Alternatives
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _tlIbindingGroups
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdObindingGroups =
                  _lhsIbindingGroups
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlObindingGroups =
                  _hdIbindingGroups
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIbindingGroups,_hdIkappaUnique,_hdIself) =
                  hd_ _hdObindingGroups _hdOkappaUnique
              ( _tlIbindingGroups,_tlIkappaUnique,_tlIself) =
                  tl_ _tlObindingGroups _tlOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Alternatives_Nil :: T_Alternatives
sem_Alternatives_Nil =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Alternatives
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- AnnotatedType -----------------------------------------------
-- cata
sem_AnnotatedType :: AnnotatedType ->
                     T_AnnotatedType
sem_AnnotatedType (AnnotatedType_AnnotatedType _range _strict _type) =
    (sem_AnnotatedType_AnnotatedType (sem_Range _range) _strict (sem_Type _type))
-- semantic domain
type T_AnnotatedType = KindConstraints ->
                       Int ->
                       ( Assumptions,KindConstraints,Kind,Int,AnnotatedType)
sem_AnnotatedType_AnnotatedType :: T_Range ->
                                   Bool ->
                                   T_Type ->
                                   T_AnnotatedType
sem_AnnotatedType_AnnotatedType range_ strict_ type_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOconstraints :: KindConstraints
              _lhsOself :: AnnotatedType
              _lhsOassumptions :: Assumptions
              _lhsOkappa :: Kind
              _lhsOkappaUnique :: Int
              _typeOconstraints :: KindConstraints
              _typeOkappaUnique :: Int
              _rangeIself :: Range
              _typeIassumptions :: Assumptions
              _typeIconstraints :: KindConstraints
              _typeIkappa :: Kind
              _typeIkappaUnique :: Int
              _typeIself :: Type
              _lhsOconstraints =
                  _typeIconstraints ++ [_newConstraint]
              _newConstraint =
                  (_typeIkappa <==> star) (mustBeStar _rangeIself "data type declaration" _typeIself)
              _self =
                  AnnotatedType_AnnotatedType _rangeIself strict_ _typeIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _typeIassumptions
              _lhsOkappa =
                  _typeIkappa
              _lhsOkappaUnique =
                  _typeIkappaUnique
              _typeOconstraints =
                  _lhsIconstraints
              _typeOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _typeIassumptions,_typeIconstraints,_typeIkappa,_typeIkappaUnique,_typeIself) =
                  type_ _typeOconstraints _typeOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappa,_lhsOkappaUnique,_lhsOself)))
-- AnnotatedTypes ----------------------------------------------
-- cata
sem_AnnotatedTypes :: AnnotatedTypes ->
                      T_AnnotatedTypes
sem_AnnotatedTypes list =
    (Prelude.foldr sem_AnnotatedTypes_Cons sem_AnnotatedTypes_Nil (Prelude.map sem_AnnotatedType list))
-- semantic domain
type T_AnnotatedTypes = KindConstraints ->
                        Int ->
                        ( Assumptions,KindConstraints,Int,Kinds,AnnotatedTypes)
sem_AnnotatedTypes_Cons :: T_AnnotatedType ->
                           T_AnnotatedTypes ->
                           T_AnnotatedTypes
sem_AnnotatedTypes_Cons hd_ tl_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOkappas :: Kinds
              _lhsOself :: AnnotatedTypes
              _lhsOconstraints :: KindConstraints
              _lhsOkappaUnique :: Int
              _hdOconstraints :: KindConstraints
              _hdOkappaUnique :: Int
              _tlOconstraints :: KindConstraints
              _tlOkappaUnique :: Int
              _hdIassumptions :: Assumptions
              _hdIconstraints :: KindConstraints
              _hdIkappa :: Kind
              _hdIkappaUnique :: Int
              _hdIself :: AnnotatedType
              _tlIassumptions :: Assumptions
              _tlIconstraints :: KindConstraints
              _tlIkappaUnique :: Int
              _tlIkappas :: Kinds
              _tlIself :: AnnotatedTypes
              _lhsOassumptions =
                  _hdIassumptions `combine` _tlIassumptions
              _lhsOkappas =
                  _hdIkappa : _tlIkappas
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOconstraints =
                  _tlIconstraints
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdOconstraints =
                  _lhsIconstraints
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlOconstraints =
                  _hdIconstraints
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIassumptions,_hdIconstraints,_hdIkappa,_hdIkappaUnique,_hdIself) =
                  hd_ _hdOconstraints _hdOkappaUnique
              ( _tlIassumptions,_tlIconstraints,_tlIkappaUnique,_tlIkappas,_tlIself) =
                  tl_ _tlOconstraints _tlOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappaUnique,_lhsOkappas,_lhsOself)))
sem_AnnotatedTypes_Nil :: T_AnnotatedTypes
sem_AnnotatedTypes_Nil =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOkappas :: Kinds
              _lhsOself :: AnnotatedTypes
              _lhsOconstraints :: KindConstraints
              _lhsOkappaUnique :: Int
              _lhsOassumptions =
                  noAssumptions
              _lhsOkappas =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOconstraints =
                  _lhsIconstraints
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappaUnique,_lhsOkappas,_lhsOself)))
-- Body --------------------------------------------------------
-- cata
sem_Body :: Body ->
            T_Body
sem_Body (Body_Body _range _importdeclarations _declarations) =
    (sem_Body_Body (sem_Range _range) (sem_ImportDeclarations _importdeclarations) (sem_Declarations _declarations))
sem_Body (Body_Hole _range _id) =
    (sem_Body_Hole (sem_Range _range) _id)
-- semantic domain
type T_Body = ImportEnvironment ->
              Int ->
              ( KindConstraints,PatternAssumptions,Int,Body)
sem_Body_Body :: T_Range ->
                 T_ImportDeclarations ->
                 T_Declarations ->
                 T_Body
sem_Body_Body range_ importdeclarations_ declarations_ =
    (\ _lhsIimportEnvironment
       _lhsIkappaUnique ->
         (let _declarationsObindingGroups :: BindingGroups
              _lhsOconstraints :: KindConstraints
              _lhsOself :: Body
              _lhsOenvironment :: PatternAssumptions
              _lhsOkappaUnique :: Int
              _declarationsOkappaUnique :: Int
              _rangeIself :: Range
              _importdeclarationsIself :: ImportDeclarations
              _declarationsIbindingGroups :: BindingGroups
              _declarationsIkappaUnique :: Int
              _declarationsIself :: Declarations
              _declarationsObindingGroups =
                  []
              _lhsOconstraints =
                  _newConstraints ++ _cs
              (_environment,_aset,_cs) =
                  performBindingGroup _declarationsIbindingGroups
              _newConstraints =
                  fst $ (_kindEnvironment .:::. _aset) (\n -> unexpected $ "Body.Body " ++ show n)
              _kindEnvironment =
                  getKindsFromImportEnvironment _lhsIimportEnvironment
              _self =
                  Body_Body _rangeIself _importdeclarationsIself _declarationsIself
              _lhsOself =
                  _self
              _lhsOenvironment =
                  _environment
              _lhsOkappaUnique =
                  _declarationsIkappaUnique
              _declarationsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _importdeclarationsIself) =
                  importdeclarations_
              ( _declarationsIbindingGroups,_declarationsIkappaUnique,_declarationsIself) =
                  declarations_ _declarationsObindingGroups _declarationsOkappaUnique
          in  ( _lhsOconstraints,_lhsOenvironment,_lhsOkappaUnique,_lhsOself)))
sem_Body_Hole :: T_Range ->
                 Integer ->
                 T_Body
sem_Body_Hole range_ id_ =
    (\ _lhsIimportEnvironment
       _lhsIkappaUnique ->
         (let _lhsOconstraints :: KindConstraints
              _lhsOenvironment :: PatternAssumptions
              _lhsOself :: Body
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _lhsOconstraints =
                  []
              _lhsOenvironment =
                  noAssumptions
              _self =
                  Body_Hole _rangeIself id_
              _lhsOself =
                  _self
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
          in  ( _lhsOconstraints,_lhsOenvironment,_lhsOkappaUnique,_lhsOself)))
-- Constructor -------------------------------------------------
-- cata
sem_Constructor :: Constructor ->
                   T_Constructor
sem_Constructor (Constructor_Constructor _range _constructor _types) =
    (sem_Constructor_Constructor (sem_Range _range) (sem_Name _constructor) (sem_AnnotatedTypes _types))
sem_Constructor (Constructor_Infix _range _leftType _constructorOperator _rightType) =
    (sem_Constructor_Infix (sem_Range _range) (sem_AnnotatedType _leftType) (sem_Name _constructorOperator) (sem_AnnotatedType _rightType))
sem_Constructor (Constructor_Record _range _constructor _fieldDeclarations) =
    (sem_Constructor_Record (sem_Range _range) (sem_Name _constructor) (sem_FieldDeclarations _fieldDeclarations))
-- semantic domain
type T_Constructor = KindConstraints ->
                     Int ->
                     ( Assumptions,KindConstraints,Int,Constructor)
sem_Constructor_Constructor :: T_Range ->
                               T_Name ->
                               T_AnnotatedTypes ->
                               T_Constructor
sem_Constructor_Constructor range_ constructor_ types_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOself :: Constructor
              _lhsOassumptions :: Assumptions
              _lhsOconstraints :: KindConstraints
              _lhsOkappaUnique :: Int
              _typesOconstraints :: KindConstraints
              _typesOkappaUnique :: Int
              _rangeIself :: Range
              _constructorIself :: Name
              _typesIassumptions :: Assumptions
              _typesIconstraints :: KindConstraints
              _typesIkappaUnique :: Int
              _typesIkappas :: Kinds
              _typesIself :: AnnotatedTypes
              _self =
                  Constructor_Constructor _rangeIself _constructorIself _typesIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _typesIassumptions
              _lhsOconstraints =
                  _typesIconstraints
              _lhsOkappaUnique =
                  _typesIkappaUnique
              _typesOconstraints =
                  _lhsIconstraints
              _typesOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _constructorIself) =
                  constructor_
              ( _typesIassumptions,_typesIconstraints,_typesIkappaUnique,_typesIkappas,_typesIself) =
                  types_ _typesOconstraints _typesOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappaUnique,_lhsOself)))
sem_Constructor_Infix :: T_Range ->
                         T_AnnotatedType ->
                         T_Name ->
                         T_AnnotatedType ->
                         T_Constructor
sem_Constructor_Infix range_ leftType_ constructorOperator_ rightType_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOself :: Constructor
              _lhsOconstraints :: KindConstraints
              _lhsOkappaUnique :: Int
              _leftTypeOconstraints :: KindConstraints
              _leftTypeOkappaUnique :: Int
              _rightTypeOconstraints :: KindConstraints
              _rightTypeOkappaUnique :: Int
              _rangeIself :: Range
              _leftTypeIassumptions :: Assumptions
              _leftTypeIconstraints :: KindConstraints
              _leftTypeIkappa :: Kind
              _leftTypeIkappaUnique :: Int
              _leftTypeIself :: AnnotatedType
              _constructorOperatorIself :: Name
              _rightTypeIassumptions :: Assumptions
              _rightTypeIconstraints :: KindConstraints
              _rightTypeIkappa :: Kind
              _rightTypeIkappaUnique :: Int
              _rightTypeIself :: AnnotatedType
              _lhsOassumptions =
                  _leftTypeIassumptions `combine` _rightTypeIassumptions
              _self =
                  Constructor_Infix _rangeIself _leftTypeIself _constructorOperatorIself _rightTypeIself
              _lhsOself =
                  _self
              _lhsOconstraints =
                  _rightTypeIconstraints
              _lhsOkappaUnique =
                  _rightTypeIkappaUnique
              _leftTypeOconstraints =
                  _lhsIconstraints
              _leftTypeOkappaUnique =
                  _lhsIkappaUnique
              _rightTypeOconstraints =
                  _leftTypeIconstraints
              _rightTypeOkappaUnique =
                  _leftTypeIkappaUnique
              ( _rangeIself) =
                  range_
              ( _leftTypeIassumptions,_leftTypeIconstraints,_leftTypeIkappa,_leftTypeIkappaUnique,_leftTypeIself) =
                  leftType_ _leftTypeOconstraints _leftTypeOkappaUnique
              ( _constructorOperatorIself) =
                  constructorOperator_
              ( _rightTypeIassumptions,_rightTypeIconstraints,_rightTypeIkappa,_rightTypeIkappaUnique,_rightTypeIself) =
                  rightType_ _rightTypeOconstraints _rightTypeOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappaUnique,_lhsOself)))
sem_Constructor_Record :: T_Range ->
                          T_Name ->
                          T_FieldDeclarations ->
                          T_Constructor
sem_Constructor_Record range_ constructor_ fieldDeclarations_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOself :: Constructor
              _lhsOconstraints :: KindConstraints
              _lhsOkappaUnique :: Int
              _fieldDeclarationsOkappaUnique :: Int
              _rangeIself :: Range
              _constructorIself :: Name
              _fieldDeclarationsIkappaUnique :: Int
              _fieldDeclarationsIself :: FieldDeclarations
              _lhsOassumptions =
                  internalError "KindInferencing.ag" "n/a" "Record constructors are not supported"
              _self =
                  Constructor_Record _rangeIself _constructorIself _fieldDeclarationsIself
              _lhsOself =
                  _self
              _lhsOconstraints =
                  _lhsIconstraints
              _lhsOkappaUnique =
                  _fieldDeclarationsIkappaUnique
              _fieldDeclarationsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _constructorIself) =
                  constructor_
              ( _fieldDeclarationsIkappaUnique,_fieldDeclarationsIself) =
                  fieldDeclarations_ _fieldDeclarationsOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappaUnique,_lhsOself)))
-- Constructors ------------------------------------------------
-- cata
sem_Constructors :: Constructors ->
                    T_Constructors
sem_Constructors list =
    (Prelude.foldr sem_Constructors_Cons sem_Constructors_Nil (Prelude.map sem_Constructor list))
-- semantic domain
type T_Constructors = KindConstraints ->
                      Int ->
                      ( Assumptions,KindConstraints,Int,Constructors)
sem_Constructors_Cons :: T_Constructor ->
                         T_Constructors ->
                         T_Constructors
sem_Constructors_Cons hd_ tl_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOself :: Constructors
              _lhsOconstraints :: KindConstraints
              _lhsOkappaUnique :: Int
              _hdOconstraints :: KindConstraints
              _hdOkappaUnique :: Int
              _tlOconstraints :: KindConstraints
              _tlOkappaUnique :: Int
              _hdIassumptions :: Assumptions
              _hdIconstraints :: KindConstraints
              _hdIkappaUnique :: Int
              _hdIself :: Constructor
              _tlIassumptions :: Assumptions
              _tlIconstraints :: KindConstraints
              _tlIkappaUnique :: Int
              _tlIself :: Constructors
              _lhsOassumptions =
                  _hdIassumptions `combine` _tlIassumptions
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOconstraints =
                  _tlIconstraints
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdOconstraints =
                  _lhsIconstraints
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlOconstraints =
                  _hdIconstraints
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIassumptions,_hdIconstraints,_hdIkappaUnique,_hdIself) =
                  hd_ _hdOconstraints _hdOkappaUnique
              ( _tlIassumptions,_tlIconstraints,_tlIkappaUnique,_tlIself) =
                  tl_ _tlOconstraints _tlOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappaUnique,_lhsOself)))
sem_Constructors_Nil :: T_Constructors
sem_Constructors_Nil =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOself :: Constructors
              _lhsOconstraints :: KindConstraints
              _lhsOkappaUnique :: Int
              _lhsOassumptions =
                  noAssumptions
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOconstraints =
                  _lhsIconstraints
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappaUnique,_lhsOself)))
-- ContextItem -------------------------------------------------
-- cata
sem_ContextItem :: ContextItem ->
                   T_ContextItem
sem_ContextItem (ContextItem_ContextItem _range _name _types) =
    (sem_ContextItem_ContextItem (sem_Range _range) (sem_Name _name) (sem_Types _types))
-- semantic domain
type T_ContextItem = Int ->
                     ( Int,ContextItem)
sem_ContextItem_ContextItem :: T_Range ->
                               T_Name ->
                               T_Types ->
                               T_ContextItem
sem_ContextItem_ContextItem range_ name_ types_ =
    (\ _lhsIkappaUnique ->
         (let _lhsOself :: ContextItem
              _lhsOkappaUnique :: Int
              _typesOconstraints :: KindConstraints
              _typesOkappaUnique :: Int
              _rangeIself :: Range
              _nameIself :: Name
              _typesIassumptions :: Assumptions
              _typesIconstraints :: KindConstraints
              _typesIkappaUnique :: Int
              _typesIkappas :: Kinds
              _typesIself :: Types
              _constraints =
                  internalError "KindInferencing.ag" "n/a" "ContextItems are not supported"
              _self =
                  ContextItem_ContextItem _rangeIself _nameIself _typesIself
              _lhsOself =
                  _self
              _lhsOkappaUnique =
                  _typesIkappaUnique
              _typesOconstraints =
                  _constraints
              _typesOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _nameIself) =
                  name_
              ( _typesIassumptions,_typesIconstraints,_typesIkappaUnique,_typesIkappas,_typesIself) =
                  types_ _typesOconstraints _typesOkappaUnique
          in  ( _lhsOkappaUnique,_lhsOself)))
-- ContextItems ------------------------------------------------
-- cata
sem_ContextItems :: ContextItems ->
                    T_ContextItems
sem_ContextItems list =
    (Prelude.foldr sem_ContextItems_Cons sem_ContextItems_Nil (Prelude.map sem_ContextItem list))
-- semantic domain
type T_ContextItems = Int ->
                      ( Int,ContextItems)
sem_ContextItems_Cons :: T_ContextItem ->
                         T_ContextItems ->
                         T_ContextItems
sem_ContextItems_Cons hd_ tl_ =
    (\ _lhsIkappaUnique ->
         (let _lhsOself :: ContextItems
              _lhsOkappaUnique :: Int
              _hdOkappaUnique :: Int
              _tlOkappaUnique :: Int
              _hdIkappaUnique :: Int
              _hdIself :: ContextItem
              _tlIkappaUnique :: Int
              _tlIself :: ContextItems
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIkappaUnique,_hdIself) =
                  hd_ _hdOkappaUnique
              ( _tlIkappaUnique,_tlIself) =
                  tl_ _tlOkappaUnique
          in  ( _lhsOkappaUnique,_lhsOself)))
sem_ContextItems_Nil :: T_ContextItems
sem_ContextItems_Nil =
    (\ _lhsIkappaUnique ->
         (let _lhsOself :: ContextItems
              _lhsOkappaUnique :: Int
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsOkappaUnique,_lhsOself)))
-- Declaration -------------------------------------------------
-- cata
sem_Declaration :: Declaration ->
                   T_Declaration
sem_Declaration (Declaration_Class _range _context _simpletype _where) =
    (sem_Declaration_Class (sem_Range _range) (sem_ContextItems _context) (sem_SimpleType _simpletype) (sem_MaybeDeclarations _where))
sem_Declaration (Declaration_Data _range _context _simpletype _constructors _derivings) =
    (sem_Declaration_Data (sem_Range _range) (sem_ContextItems _context) (sem_SimpleType _simpletype) (sem_Constructors _constructors) (sem_Names _derivings))
sem_Declaration (Declaration_Default _range _types) =
    (sem_Declaration_Default (sem_Range _range) (sem_Types _types))
sem_Declaration (Declaration_Empty _range) =
    (sem_Declaration_Empty (sem_Range _range))
sem_Declaration (Declaration_Fixity _range _fixity _priority _operators) =
    (sem_Declaration_Fixity (sem_Range _range) (sem_Fixity _fixity) (sem_MaybeInt _priority) (sem_Names _operators))
sem_Declaration (Declaration_FunctionBindings _range _bindings) =
    (sem_Declaration_FunctionBindings (sem_Range _range) (sem_FunctionBindings _bindings))
sem_Declaration (Declaration_Hole _range _id) =
    (sem_Declaration_Hole (sem_Range _range) _id)
sem_Declaration (Declaration_Instance _range _context _name _types _where) =
    (sem_Declaration_Instance (sem_Range _range) (sem_ContextItems _context) (sem_Name _name) (sem_Types _types) (sem_MaybeDeclarations _where))
sem_Declaration (Declaration_Newtype _range _context _simpletype _constructor _derivings) =
    (sem_Declaration_Newtype (sem_Range _range) (sem_ContextItems _context) (sem_SimpleType _simpletype) (sem_Constructor _constructor) (sem_Names _derivings))
sem_Declaration (Declaration_PatternBinding _range _pattern _righthandside) =
    (sem_Declaration_PatternBinding (sem_Range _range) (sem_Pattern _pattern) (sem_RightHandSide _righthandside))
sem_Declaration (Declaration_Type _range _simpletype _type) =
    (sem_Declaration_Type (sem_Range _range) (sem_SimpleType _simpletype) (sem_Type _type))
sem_Declaration (Declaration_TypeSignature _range _names _type) =
    (sem_Declaration_TypeSignature (sem_Range _range) (sem_Names _names) (sem_Type _type))
-- semantic domain
type T_Declaration = BindingGroups ->
                     Int ->
                     ( BindingGroups,Int,Declaration)
sem_Declaration_Class :: T_Range ->
                         T_ContextItems ->
                         T_SimpleType ->
                         T_MaybeDeclarations ->
                         T_Declaration
sem_Declaration_Class range_ context_ simpletype_ where_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Declaration
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _contextOkappaUnique :: Int
              _simpletypeOconstraints :: KindConstraints
              _simpletypeOkappaOfRHS :: Kind
              _simpletypeOkappaUnique :: Int
              _whereObindingGroups :: BindingGroups
              _whereOkappaUnique :: Int
              _rangeIself :: Range
              _contextIkappaUnique :: Int
              _contextIself :: ContextItems
              _simpletypeIconstraints :: KindConstraints
              _simpletypeIdeclared :: PatternAssumptions
              _simpletypeIenvironment :: PatternAssumptions
              _simpletypeIkappaUnique :: Int
              _simpletypeIself :: SimpleType
              _whereIbindingGroups :: BindingGroups
              _whereIkappaUnique :: Int
              _whereIself :: MaybeDeclarations
              (_constraints,_kappaOfRHS) =
                  internalError "KindInferencing.ag" "n/a" "class decls are not supported"
              _self =
                  Declaration_Class _rangeIself _contextIself _simpletypeIself _whereIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _whereIbindingGroups
              _lhsOkappaUnique =
                  _whereIkappaUnique
              _contextOkappaUnique =
                  _lhsIkappaUnique
              _simpletypeOconstraints =
                  _constraints
              _simpletypeOkappaOfRHS =
                  _kappaOfRHS
              _simpletypeOkappaUnique =
                  _contextIkappaUnique
              _whereObindingGroups =
                  _lhsIbindingGroups
              _whereOkappaUnique =
                  _simpletypeIkappaUnique
              ( _rangeIself) =
                  range_
              ( _contextIkappaUnique,_contextIself) =
                  context_ _contextOkappaUnique
              ( _simpletypeIconstraints,_simpletypeIdeclared,_simpletypeIenvironment,_simpletypeIkappaUnique,_simpletypeIself) =
                  simpletype_ _simpletypeOconstraints _simpletypeOkappaOfRHS _simpletypeOkappaUnique
              ( _whereIbindingGroups,_whereIkappaUnique,_whereIself) =
                  where_ _whereObindingGroups _whereOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declaration_Data :: T_Range ->
                        T_ContextItems ->
                        T_SimpleType ->
                        T_Constructors ->
                        T_Names ->
                        T_Declaration
sem_Declaration_Data range_ context_ simpletype_ constructors_ derivings_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _simpletypeOconstraints :: KindConstraints
              _simpletypeOkappaOfRHS :: Kind
              _lhsObindingGroups :: BindingGroups
              _lhsOself :: Declaration
              _lhsOkappaUnique :: Int
              _contextOkappaUnique :: Int
              _simpletypeOkappaUnique :: Int
              _constructorsOconstraints :: KindConstraints
              _constructorsOkappaUnique :: Int
              _rangeIself :: Range
              _contextIkappaUnique :: Int
              _contextIself :: ContextItems
              _simpletypeIconstraints :: KindConstraints
              _simpletypeIdeclared :: PatternAssumptions
              _simpletypeIenvironment :: PatternAssumptions
              _simpletypeIkappaUnique :: Int
              _simpletypeIself :: SimpleType
              _constructorsIassumptions :: Assumptions
              _constructorsIconstraints :: KindConstraints
              _constructorsIkappaUnique :: Int
              _constructorsIself :: Constructors
              _derivingsIself :: Names
              _simpletypeOconstraints =
                  []
              _simpletypeOkappaOfRHS =
                  star
              _lhsObindingGroups =
                  _newGroup : _lhsIbindingGroups
              _newConstraints =
                  fst $ (_simpletypeIenvironment .===. _constructorsIassumptions) (\n -> unexpected $ "Declaration.Data " ++ show n)
              _newGroup =
                  (_simpletypeIdeclared, _constructorsIassumptions, _newConstraints ++ _constructorsIconstraints)
              _self =
                  Declaration_Data _rangeIself _contextIself _simpletypeIself _constructorsIself _derivingsIself
              _lhsOself =
                  _self
              _lhsOkappaUnique =
                  _constructorsIkappaUnique
              _contextOkappaUnique =
                  _lhsIkappaUnique
              _simpletypeOkappaUnique =
                  _contextIkappaUnique
              _constructorsOconstraints =
                  _simpletypeIconstraints
              _constructorsOkappaUnique =
                  _simpletypeIkappaUnique
              ( _rangeIself) =
                  range_
              ( _contextIkappaUnique,_contextIself) =
                  context_ _contextOkappaUnique
              ( _simpletypeIconstraints,_simpletypeIdeclared,_simpletypeIenvironment,_simpletypeIkappaUnique,_simpletypeIself) =
                  simpletype_ _simpletypeOconstraints _simpletypeOkappaOfRHS _simpletypeOkappaUnique
              ( _constructorsIassumptions,_constructorsIconstraints,_constructorsIkappaUnique,_constructorsIself) =
                  constructors_ _constructorsOconstraints _constructorsOkappaUnique
              ( _derivingsIself) =
                  derivings_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declaration_Default :: T_Range ->
                           T_Types ->
                           T_Declaration
sem_Declaration_Default range_ types_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Declaration
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _typesOconstraints :: KindConstraints
              _typesOkappaUnique :: Int
              _rangeIself :: Range
              _typesIassumptions :: Assumptions
              _typesIconstraints :: KindConstraints
              _typesIkappaUnique :: Int
              _typesIkappas :: Kinds
              _typesIself :: Types
              _constraints =
                  internalError "KindInferencing.ag" "n/a" "default decls is not supported"
              _self =
                  Declaration_Default _rangeIself _typesIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _typesIkappaUnique
              _typesOconstraints =
                  _constraints
              _typesOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _typesIassumptions,_typesIconstraints,_typesIkappaUnique,_typesIkappas,_typesIself) =
                  types_ _typesOconstraints _typesOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declaration_Empty :: T_Range ->
                         T_Declaration
sem_Declaration_Empty range_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Declaration
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _self =
                  Declaration_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declaration_Fixity :: T_Range ->
                          T_Fixity ->
                          T_MaybeInt ->
                          T_Names ->
                          T_Declaration
sem_Declaration_Fixity range_ fixity_ priority_ operators_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Declaration
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _fixityIself :: Fixity
              _priorityIself :: MaybeInt
              _operatorsIself :: Names
              _self =
                  Declaration_Fixity _rangeIself _fixityIself _priorityIself _operatorsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _fixityIself) =
                  fixity_
              ( _priorityIself) =
                  priority_
              ( _operatorsIself) =
                  operators_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declaration_FunctionBindings :: T_Range ->
                                    T_FunctionBindings ->
                                    T_Declaration
sem_Declaration_FunctionBindings range_ bindings_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Declaration
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _bindingsObindingGroups :: BindingGroups
              _bindingsOkappaUnique :: Int
              _rangeIself :: Range
              _bindingsIbindingGroups :: BindingGroups
              _bindingsIkappaUnique :: Int
              _bindingsIself :: FunctionBindings
              _self =
                  Declaration_FunctionBindings _rangeIself _bindingsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _bindingsIbindingGroups
              _lhsOkappaUnique =
                  _bindingsIkappaUnique
              _bindingsObindingGroups =
                  _lhsIbindingGroups
              _bindingsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _bindingsIbindingGroups,_bindingsIkappaUnique,_bindingsIself) =
                  bindings_ _bindingsObindingGroups _bindingsOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declaration_Hole :: T_Range ->
                        Integer ->
                        T_Declaration
sem_Declaration_Hole range_ id_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Declaration
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _self =
                  Declaration_Hole _rangeIself id_
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declaration_Instance :: T_Range ->
                            T_ContextItems ->
                            T_Name ->
                            T_Types ->
                            T_MaybeDeclarations ->
                            T_Declaration
sem_Declaration_Instance range_ context_ name_ types_ where_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Declaration
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _contextOkappaUnique :: Int
              _typesOconstraints :: KindConstraints
              _typesOkappaUnique :: Int
              _whereObindingGroups :: BindingGroups
              _whereOkappaUnique :: Int
              _rangeIself :: Range
              _contextIkappaUnique :: Int
              _contextIself :: ContextItems
              _nameIself :: Name
              _typesIassumptions :: Assumptions
              _typesIconstraints :: KindConstraints
              _typesIkappaUnique :: Int
              _typesIkappas :: Kinds
              _typesIself :: Types
              _whereIbindingGroups :: BindingGroups
              _whereIkappaUnique :: Int
              _whereIself :: MaybeDeclarations
              _constraints =
                  internalError "KindInferencing.ag" "n/a" "instance decls are not supported"
              _self =
                  Declaration_Instance _rangeIself _contextIself _nameIself _typesIself _whereIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _whereIbindingGroups
              _lhsOkappaUnique =
                  _whereIkappaUnique
              _contextOkappaUnique =
                  _lhsIkappaUnique
              _typesOconstraints =
                  _constraints
              _typesOkappaUnique =
                  _contextIkappaUnique
              _whereObindingGroups =
                  _lhsIbindingGroups
              _whereOkappaUnique =
                  _typesIkappaUnique
              ( _rangeIself) =
                  range_
              ( _contextIkappaUnique,_contextIself) =
                  context_ _contextOkappaUnique
              ( _nameIself) =
                  name_
              ( _typesIassumptions,_typesIconstraints,_typesIkappaUnique,_typesIkappas,_typesIself) =
                  types_ _typesOconstraints _typesOkappaUnique
              ( _whereIbindingGroups,_whereIkappaUnique,_whereIself) =
                  where_ _whereObindingGroups _whereOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declaration_Newtype :: T_Range ->
                           T_ContextItems ->
                           T_SimpleType ->
                           T_Constructor ->
                           T_Names ->
                           T_Declaration
sem_Declaration_Newtype range_ context_ simpletype_ constructor_ derivings_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Declaration
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _contextOkappaUnique :: Int
              _simpletypeOconstraints :: KindConstraints
              _simpletypeOkappaOfRHS :: Kind
              _simpletypeOkappaUnique :: Int
              _constructorOconstraints :: KindConstraints
              _constructorOkappaUnique :: Int
              _rangeIself :: Range
              _contextIkappaUnique :: Int
              _contextIself :: ContextItems
              _simpletypeIconstraints :: KindConstraints
              _simpletypeIdeclared :: PatternAssumptions
              _simpletypeIenvironment :: PatternAssumptions
              _simpletypeIkappaUnique :: Int
              _simpletypeIself :: SimpleType
              _constructorIassumptions :: Assumptions
              _constructorIconstraints :: KindConstraints
              _constructorIkappaUnique :: Int
              _constructorIself :: Constructor
              _derivingsIself :: Names
              (_constraints,_kappaOfRHS) =
                  internalError "KindInferencing.ag" "n/a" "newtype decls are not supported"
              _self =
                  Declaration_Newtype _rangeIself _contextIself _simpletypeIself _constructorIself _derivingsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _constructorIkappaUnique
              _contextOkappaUnique =
                  _lhsIkappaUnique
              _simpletypeOconstraints =
                  _constraints
              _simpletypeOkappaOfRHS =
                  _kappaOfRHS
              _simpletypeOkappaUnique =
                  _contextIkappaUnique
              _constructorOconstraints =
                  _constraints
              _constructorOkappaUnique =
                  _simpletypeIkappaUnique
              ( _rangeIself) =
                  range_
              ( _contextIkappaUnique,_contextIself) =
                  context_ _contextOkappaUnique
              ( _simpletypeIconstraints,_simpletypeIdeclared,_simpletypeIenvironment,_simpletypeIkappaUnique,_simpletypeIself) =
                  simpletype_ _simpletypeOconstraints _simpletypeOkappaOfRHS _simpletypeOkappaUnique
              ( _constructorIassumptions,_constructorIconstraints,_constructorIkappaUnique,_constructorIself) =
                  constructor_ _constructorOconstraints _constructorOkappaUnique
              ( _derivingsIself) =
                  derivings_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declaration_PatternBinding :: T_Range ->
                                  T_Pattern ->
                                  T_RightHandSide ->
                                  T_Declaration
sem_Declaration_PatternBinding range_ pattern_ righthandside_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Declaration
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _righthandsideObindingGroups :: BindingGroups
              _righthandsideOkappaUnique :: Int
              _rangeIself :: Range
              _patternIself :: Pattern
              _righthandsideIbindingGroups :: BindingGroups
              _righthandsideIkappaUnique :: Int
              _righthandsideIself :: RightHandSide
              _self =
                  Declaration_PatternBinding _rangeIself _patternIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _righthandsideIbindingGroups
              _lhsOkappaUnique =
                  _righthandsideIkappaUnique
              _righthandsideObindingGroups =
                  _lhsIbindingGroups
              _righthandsideOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _patternIself) =
                  pattern_
              ( _righthandsideIbindingGroups,_righthandsideIkappaUnique,_righthandsideIself) =
                  righthandside_ _righthandsideObindingGroups _righthandsideOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declaration_Type :: T_Range ->
                        T_SimpleType ->
                        T_Type ->
                        T_Declaration
sem_Declaration_Type range_ simpletype_ type_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _simpletypeOconstraints :: KindConstraints
              _simpletypeOkappaOfRHS :: Kind
              _lhsObindingGroups :: BindingGroups
              _lhsOself :: Declaration
              _lhsOkappaUnique :: Int
              _simpletypeOkappaUnique :: Int
              _typeOconstraints :: KindConstraints
              _typeOkappaUnique :: Int
              _rangeIself :: Range
              _simpletypeIconstraints :: KindConstraints
              _simpletypeIdeclared :: PatternAssumptions
              _simpletypeIenvironment :: PatternAssumptions
              _simpletypeIkappaUnique :: Int
              _simpletypeIself :: SimpleType
              _typeIassumptions :: Assumptions
              _typeIconstraints :: KindConstraints
              _typeIkappa :: Kind
              _typeIkappaUnique :: Int
              _typeIself :: Type
              _simpletypeOconstraints =
                  []
              _simpletypeOkappaOfRHS =
                  _typeIkappa
              _lhsObindingGroups =
                  _newGroup : _lhsIbindingGroups
              _newConstraints =
                  fst $ (_simpletypeIenvironment .===. _typeIassumptions) (\n -> unexpected $ "Declaration.Type " ++ show n)
              _newGroup =
                  (_simpletypeIdeclared, _typeIassumptions, _newConstraints ++ _typeIconstraints)
              _self =
                  Declaration_Type _rangeIself _simpletypeIself _typeIself
              _lhsOself =
                  _self
              _lhsOkappaUnique =
                  _typeIkappaUnique
              _simpletypeOkappaUnique =
                  _lhsIkappaUnique
              _typeOconstraints =
                  _simpletypeIconstraints
              _typeOkappaUnique =
                  _simpletypeIkappaUnique
              ( _rangeIself) =
                  range_
              ( _simpletypeIconstraints,_simpletypeIdeclared,_simpletypeIenvironment,_simpletypeIkappaUnique,_simpletypeIself) =
                  simpletype_ _simpletypeOconstraints _simpletypeOkappaOfRHS _simpletypeOkappaUnique
              ( _typeIassumptions,_typeIconstraints,_typeIkappa,_typeIkappaUnique,_typeIself) =
                  type_ _typeOconstraints _typeOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declaration_TypeSignature :: T_Range ->
                                 T_Names ->
                                 T_Type ->
                                 T_Declaration
sem_Declaration_TypeSignature range_ names_ type_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _typeOconstraints :: KindConstraints
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _lhsOself :: Declaration
              _typeOkappaUnique :: Int
              _rangeIself :: Range
              _namesIself :: Names
              _typeIassumptions :: Assumptions
              _typeIconstraints :: KindConstraints
              _typeIkappa :: Kind
              _typeIkappaUnique :: Int
              _typeIself :: Type
              _typeOconstraints =
                  []
              _lhsObindingGroups =
                  _newGroup : _lhsIbindingGroups
              _lhsOkappaUnique =
                  _typeIkappaUnique + length _tvEnv
              _newConstraint =
                  (_typeIkappa <==> star) (mustBeStar _rangeIself "type signature" _typeIself)
              _tvEnv =
                  zip (getTypeVariables _typeIassumptions) (map TVar [_typeIkappaUnique..])
              (_cset,_aset) =
                  (M.fromList _tvEnv .===. _typeIassumptions) (\n -> unexpected $ "Declaration.TypeSignature " ++ show n)
              _newGroup =
                  (M.empty, _aset, _cset ++ _typeIconstraints ++ [_newConstraint])
              _self =
                  Declaration_TypeSignature _rangeIself _namesIself _typeIself
              _lhsOself =
                  _self
              _typeOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _namesIself) =
                  names_
              ( _typeIassumptions,_typeIconstraints,_typeIkappa,_typeIkappaUnique,_typeIself) =
                  type_ _typeOconstraints _typeOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- Declarations ------------------------------------------------
-- cata
sem_Declarations :: Declarations ->
                    T_Declarations
sem_Declarations list =
    (Prelude.foldr sem_Declarations_Cons sem_Declarations_Nil (Prelude.map sem_Declaration list))
-- semantic domain
type T_Declarations = BindingGroups ->
                      Int ->
                      ( BindingGroups,Int,Declarations)
sem_Declarations_Cons :: T_Declaration ->
                         T_Declarations ->
                         T_Declarations
sem_Declarations_Cons hd_ tl_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Declarations
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _hdObindingGroups :: BindingGroups
              _hdOkappaUnique :: Int
              _tlObindingGroups :: BindingGroups
              _tlOkappaUnique :: Int
              _hdIbindingGroups :: BindingGroups
              _hdIkappaUnique :: Int
              _hdIself :: Declaration
              _tlIbindingGroups :: BindingGroups
              _tlIkappaUnique :: Int
              _tlIself :: Declarations
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _tlIbindingGroups
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdObindingGroups =
                  _lhsIbindingGroups
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlObindingGroups =
                  _hdIbindingGroups
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIbindingGroups,_hdIkappaUnique,_hdIself) =
                  hd_ _hdObindingGroups _hdOkappaUnique
              ( _tlIbindingGroups,_tlIkappaUnique,_tlIself) =
                  tl_ _tlObindingGroups _tlOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Declarations_Nil :: T_Declarations
sem_Declarations_Nil =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Declarations
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- Export ------------------------------------------------------
-- cata
sem_Export :: Export ->
              T_Export
sem_Export (Export_Module _range _name) =
    (sem_Export_Module (sem_Range _range) (sem_Name _name))
sem_Export (Export_TypeOrClass _range _name _names) =
    (sem_Export_TypeOrClass (sem_Range _range) (sem_Name _name) (sem_MaybeNames _names))
sem_Export (Export_TypeOrClassComplete _range _name) =
    (sem_Export_TypeOrClassComplete (sem_Range _range) (sem_Name _name))
sem_Export (Export_Variable _range _name) =
    (sem_Export_Variable (sem_Range _range) (sem_Name _name))
-- semantic domain
type T_Export = ( Export)
sem_Export_Module :: T_Range ->
                     T_Name ->
                     T_Export
sem_Export_Module range_ name_ =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Export_Module _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
     in  ( _lhsOself))
sem_Export_TypeOrClass :: T_Range ->
                          T_Name ->
                          T_MaybeNames ->
                          T_Export
sem_Export_TypeOrClass range_ name_ names_ =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _namesIself :: MaybeNames
         _self =
             Export_TypeOrClass _rangeIself _nameIself _namesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
         ( _namesIself) =
             names_
     in  ( _lhsOself))
sem_Export_TypeOrClassComplete :: T_Range ->
                                  T_Name ->
                                  T_Export
sem_Export_TypeOrClassComplete range_ name_ =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Export_TypeOrClassComplete _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
     in  ( _lhsOself))
sem_Export_Variable :: T_Range ->
                       T_Name ->
                       T_Export
sem_Export_Variable range_ name_ =
    (let _lhsOself :: Export
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Export_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
     in  ( _lhsOself))
-- Exports -----------------------------------------------------
-- cata
sem_Exports :: Exports ->
               T_Exports
sem_Exports list =
    (Prelude.foldr sem_Exports_Cons sem_Exports_Nil (Prelude.map sem_Export list))
-- semantic domain
type T_Exports = ( Exports)
sem_Exports_Cons :: T_Export ->
                    T_Exports ->
                    T_Exports
sem_Exports_Cons hd_ tl_ =
    (let _lhsOself :: Exports
         _hdIself :: Export
         _tlIself :: Exports
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Exports_Nil :: T_Exports
sem_Exports_Nil =
    (let _lhsOself :: Exports
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Expression --------------------------------------------------
-- cata
sem_Expression :: Expression ->
                  T_Expression
sem_Expression (Expression_Case _range _expression _alternatives) =
    (sem_Expression_Case (sem_Range _range) (sem_Expression _expression) (sem_Alternatives _alternatives))
sem_Expression (Expression_Comprehension _range _expression _qualifiers) =
    (sem_Expression_Comprehension (sem_Range _range) (sem_Expression _expression) (sem_Qualifiers _qualifiers))
sem_Expression (Expression_Constructor _range _name) =
    (sem_Expression_Constructor (sem_Range _range) (sem_Name _name))
sem_Expression (Expression_Do _range _statements) =
    (sem_Expression_Do (sem_Range _range) (sem_Statements _statements))
sem_Expression (Expression_Enum _range _from _then _to) =
    (sem_Expression_Enum (sem_Range _range) (sem_Expression _from) (sem_MaybeExpression _then) (sem_MaybeExpression _to))
sem_Expression (Expression_Feedback _range _feedback _expression) =
    (sem_Expression_Feedback (sem_Range _range) _feedback (sem_Expression _expression))
sem_Expression (Expression_Hole _range _id) =
    (sem_Expression_Hole (sem_Range _range) _id)
sem_Expression (Expression_If _range _guardExpression _thenExpression _elseExpression) =
    (sem_Expression_If (sem_Range _range) (sem_Expression _guardExpression) (sem_Expression _thenExpression) (sem_Expression _elseExpression))
sem_Expression (Expression_InfixApplication _range _leftExpression _operator _rightExpression) =
    (sem_Expression_InfixApplication (sem_Range _range) (sem_MaybeExpression _leftExpression) (sem_Expression _operator) (sem_MaybeExpression _rightExpression))
sem_Expression (Expression_Lambda _range _patterns _expression) =
    (sem_Expression_Lambda (sem_Range _range) (sem_Patterns _patterns) (sem_Expression _expression))
sem_Expression (Expression_Let _range _declarations _expression) =
    (sem_Expression_Let (sem_Range _range) (sem_Declarations _declarations) (sem_Expression _expression))
sem_Expression (Expression_List _range _expressions) =
    (sem_Expression_List (sem_Range _range) (sem_Expressions _expressions))
sem_Expression (Expression_Literal _range _literal) =
    (sem_Expression_Literal (sem_Range _range) (sem_Literal _literal))
sem_Expression (Expression_MustUse _range _expression) =
    (sem_Expression_MustUse (sem_Range _range) (sem_Expression _expression))
sem_Expression (Expression_Negate _range _expression) =
    (sem_Expression_Negate (sem_Range _range) (sem_Expression _expression))
sem_Expression (Expression_NegateFloat _range _expression) =
    (sem_Expression_NegateFloat (sem_Range _range) (sem_Expression _expression))
sem_Expression (Expression_NormalApplication _range _function _arguments) =
    (sem_Expression_NormalApplication (sem_Range _range) (sem_Expression _function) (sem_Expressions _arguments))
sem_Expression (Expression_Parenthesized _range _expression) =
    (sem_Expression_Parenthesized (sem_Range _range) (sem_Expression _expression))
sem_Expression (Expression_RecordConstruction _range _name _recordExpressionBindings) =
    (sem_Expression_RecordConstruction (sem_Range _range) (sem_Name _name) (sem_RecordExpressionBindings _recordExpressionBindings))
sem_Expression (Expression_RecordUpdate _range _expression _recordExpressionBindings) =
    (sem_Expression_RecordUpdate (sem_Range _range) (sem_Expression _expression) (sem_RecordExpressionBindings _recordExpressionBindings))
sem_Expression (Expression_Tuple _range _expressions) =
    (sem_Expression_Tuple (sem_Range _range) (sem_Expressions _expressions))
sem_Expression (Expression_Typed _range _expression _type) =
    (sem_Expression_Typed (sem_Range _range) (sem_Expression _expression) (sem_Type _type))
sem_Expression (Expression_Variable _range _name) =
    (sem_Expression_Variable (sem_Range _range) (sem_Name _name))
-- semantic domain
type T_Expression = BindingGroups ->
                    Int ->
                    ( BindingGroups,Int,Expression)
sem_Expression_Case :: T_Range ->
                       T_Expression ->
                       T_Alternatives ->
                       T_Expression
sem_Expression_Case range_ expression_ alternatives_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _alternativesObindingGroups :: BindingGroups
              _alternativesOkappaUnique :: Int
              _rangeIself :: Range
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _alternativesIbindingGroups :: BindingGroups
              _alternativesIkappaUnique :: Int
              _alternativesIself :: Alternatives
              _self =
                  Expression_Case _rangeIself _expressionIself _alternativesIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _alternativesIbindingGroups
              _lhsOkappaUnique =
                  _alternativesIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              _alternativesObindingGroups =
                  _expressionIbindingGroups
              _alternativesOkappaUnique =
                  _expressionIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
              ( _alternativesIbindingGroups,_alternativesIkappaUnique,_alternativesIself) =
                  alternatives_ _alternativesObindingGroups _alternativesOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Comprehension :: T_Range ->
                                T_Expression ->
                                T_Qualifiers ->
                                T_Expression
sem_Expression_Comprehension range_ expression_ qualifiers_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _qualifiersObindingGroups :: BindingGroups
              _qualifiersOkappaUnique :: Int
              _rangeIself :: Range
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _qualifiersIbindingGroups :: BindingGroups
              _qualifiersIkappaUnique :: Int
              _qualifiersIself :: Qualifiers
              _self =
                  Expression_Comprehension _rangeIself _expressionIself _qualifiersIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _qualifiersIbindingGroups
              _lhsOkappaUnique =
                  _qualifiersIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              _qualifiersObindingGroups =
                  _expressionIbindingGroups
              _qualifiersOkappaUnique =
                  _expressionIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
              ( _qualifiersIbindingGroups,_qualifiersIkappaUnique,_qualifiersIself) =
                  qualifiers_ _qualifiersObindingGroups _qualifiersOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Constructor :: T_Range ->
                              T_Name ->
                              T_Expression
sem_Expression_Constructor range_ name_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _nameIself :: Name
              _self =
                  Expression_Constructor _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _nameIself) =
                  name_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Do :: T_Range ->
                     T_Statements ->
                     T_Expression
sem_Expression_Do range_ statements_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _statementsObindingGroups :: BindingGroups
              _statementsOkappaUnique :: Int
              _rangeIself :: Range
              _statementsIbindingGroups :: BindingGroups
              _statementsIkappaUnique :: Int
              _statementsIself :: Statements
              _self =
                  Expression_Do _rangeIself _statementsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _statementsIbindingGroups
              _lhsOkappaUnique =
                  _statementsIkappaUnique
              _statementsObindingGroups =
                  _lhsIbindingGroups
              _statementsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _statementsIbindingGroups,_statementsIkappaUnique,_statementsIself) =
                  statements_ _statementsObindingGroups _statementsOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Enum :: T_Range ->
                       T_Expression ->
                       T_MaybeExpression ->
                       T_MaybeExpression ->
                       T_Expression
sem_Expression_Enum range_ from_ then_ to_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _fromObindingGroups :: BindingGroups
              _fromOkappaUnique :: Int
              _thenObindingGroups :: BindingGroups
              _thenOkappaUnique :: Int
              _toObindingGroups :: BindingGroups
              _toOkappaUnique :: Int
              _rangeIself :: Range
              _fromIbindingGroups :: BindingGroups
              _fromIkappaUnique :: Int
              _fromIself :: Expression
              _thenIbindingGroups :: BindingGroups
              _thenIkappaUnique :: Int
              _thenIself :: MaybeExpression
              _toIbindingGroups :: BindingGroups
              _toIkappaUnique :: Int
              _toIself :: MaybeExpression
              _self =
                  Expression_Enum _rangeIself _fromIself _thenIself _toIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _toIbindingGroups
              _lhsOkappaUnique =
                  _toIkappaUnique
              _fromObindingGroups =
                  _lhsIbindingGroups
              _fromOkappaUnique =
                  _lhsIkappaUnique
              _thenObindingGroups =
                  _fromIbindingGroups
              _thenOkappaUnique =
                  _fromIkappaUnique
              _toObindingGroups =
                  _thenIbindingGroups
              _toOkappaUnique =
                  _thenIkappaUnique
              ( _rangeIself) =
                  range_
              ( _fromIbindingGroups,_fromIkappaUnique,_fromIself) =
                  from_ _fromObindingGroups _fromOkappaUnique
              ( _thenIbindingGroups,_thenIkappaUnique,_thenIself) =
                  then_ _thenObindingGroups _thenOkappaUnique
              ( _toIbindingGroups,_toIkappaUnique,_toIself) =
                  to_ _toObindingGroups _toOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Feedback :: T_Range ->
                           String ->
                           T_Expression ->
                           T_Expression
sem_Expression_Feedback range_ feedback_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  Expression_Feedback _rangeIself feedback_ _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Hole :: T_Range ->
                       Integer ->
                       T_Expression
sem_Expression_Hole range_ id_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _self =
                  Expression_Hole _rangeIself id_
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_If :: T_Range ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression ->
                     T_Expression
sem_Expression_If range_ guardExpression_ thenExpression_ elseExpression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _guardExpressionObindingGroups :: BindingGroups
              _guardExpressionOkappaUnique :: Int
              _thenExpressionObindingGroups :: BindingGroups
              _thenExpressionOkappaUnique :: Int
              _elseExpressionObindingGroups :: BindingGroups
              _elseExpressionOkappaUnique :: Int
              _rangeIself :: Range
              _guardExpressionIbindingGroups :: BindingGroups
              _guardExpressionIkappaUnique :: Int
              _guardExpressionIself :: Expression
              _thenExpressionIbindingGroups :: BindingGroups
              _thenExpressionIkappaUnique :: Int
              _thenExpressionIself :: Expression
              _elseExpressionIbindingGroups :: BindingGroups
              _elseExpressionIkappaUnique :: Int
              _elseExpressionIself :: Expression
              _self =
                  Expression_If _rangeIself _guardExpressionIself _thenExpressionIself _elseExpressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _elseExpressionIbindingGroups
              _lhsOkappaUnique =
                  _elseExpressionIkappaUnique
              _guardExpressionObindingGroups =
                  _lhsIbindingGroups
              _guardExpressionOkappaUnique =
                  _lhsIkappaUnique
              _thenExpressionObindingGroups =
                  _guardExpressionIbindingGroups
              _thenExpressionOkappaUnique =
                  _guardExpressionIkappaUnique
              _elseExpressionObindingGroups =
                  _thenExpressionIbindingGroups
              _elseExpressionOkappaUnique =
                  _thenExpressionIkappaUnique
              ( _rangeIself) =
                  range_
              ( _guardExpressionIbindingGroups,_guardExpressionIkappaUnique,_guardExpressionIself) =
                  guardExpression_ _guardExpressionObindingGroups _guardExpressionOkappaUnique
              ( _thenExpressionIbindingGroups,_thenExpressionIkappaUnique,_thenExpressionIself) =
                  thenExpression_ _thenExpressionObindingGroups _thenExpressionOkappaUnique
              ( _elseExpressionIbindingGroups,_elseExpressionIkappaUnique,_elseExpressionIself) =
                  elseExpression_ _elseExpressionObindingGroups _elseExpressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_InfixApplication :: T_Range ->
                                   T_MaybeExpression ->
                                   T_Expression ->
                                   T_MaybeExpression ->
                                   T_Expression
sem_Expression_InfixApplication range_ leftExpression_ operator_ rightExpression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _leftExpressionObindingGroups :: BindingGroups
              _leftExpressionOkappaUnique :: Int
              _operatorObindingGroups :: BindingGroups
              _operatorOkappaUnique :: Int
              _rightExpressionObindingGroups :: BindingGroups
              _rightExpressionOkappaUnique :: Int
              _rangeIself :: Range
              _leftExpressionIbindingGroups :: BindingGroups
              _leftExpressionIkappaUnique :: Int
              _leftExpressionIself :: MaybeExpression
              _operatorIbindingGroups :: BindingGroups
              _operatorIkappaUnique :: Int
              _operatorIself :: Expression
              _rightExpressionIbindingGroups :: BindingGroups
              _rightExpressionIkappaUnique :: Int
              _rightExpressionIself :: MaybeExpression
              _self =
                  Expression_InfixApplication _rangeIself _leftExpressionIself _operatorIself _rightExpressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _rightExpressionIbindingGroups
              _lhsOkappaUnique =
                  _rightExpressionIkappaUnique
              _leftExpressionObindingGroups =
                  _lhsIbindingGroups
              _leftExpressionOkappaUnique =
                  _lhsIkappaUnique
              _operatorObindingGroups =
                  _leftExpressionIbindingGroups
              _operatorOkappaUnique =
                  _leftExpressionIkappaUnique
              _rightExpressionObindingGroups =
                  _operatorIbindingGroups
              _rightExpressionOkappaUnique =
                  _operatorIkappaUnique
              ( _rangeIself) =
                  range_
              ( _leftExpressionIbindingGroups,_leftExpressionIkappaUnique,_leftExpressionIself) =
                  leftExpression_ _leftExpressionObindingGroups _leftExpressionOkappaUnique
              ( _operatorIbindingGroups,_operatorIkappaUnique,_operatorIself) =
                  operator_ _operatorObindingGroups _operatorOkappaUnique
              ( _rightExpressionIbindingGroups,_rightExpressionIkappaUnique,_rightExpressionIself) =
                  rightExpression_ _rightExpressionObindingGroups _rightExpressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Lambda :: T_Range ->
                         T_Patterns ->
                         T_Expression ->
                         T_Expression
sem_Expression_Lambda range_ patterns_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _patternsIself :: Patterns
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  Expression_Lambda _rangeIself _patternsIself _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _patternsIself) =
                  patterns_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Let :: T_Range ->
                      T_Declarations ->
                      T_Expression ->
                      T_Expression
sem_Expression_Let range_ declarations_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _declarationsObindingGroups :: BindingGroups
              _declarationsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _declarationsIbindingGroups :: BindingGroups
              _declarationsIkappaUnique :: Int
              _declarationsIself :: Declarations
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  Expression_Let _rangeIself _declarationsIself _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _declarationsObindingGroups =
                  _lhsIbindingGroups
              _declarationsOkappaUnique =
                  _lhsIkappaUnique
              _expressionObindingGroups =
                  _declarationsIbindingGroups
              _expressionOkappaUnique =
                  _declarationsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _declarationsIbindingGroups,_declarationsIkappaUnique,_declarationsIself) =
                  declarations_ _declarationsObindingGroups _declarationsOkappaUnique
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_List :: T_Range ->
                       T_Expressions ->
                       T_Expression
sem_Expression_List range_ expressions_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionsObindingGroups :: BindingGroups
              _expressionsOkappaUnique :: Int
              _rangeIself :: Range
              _expressionsIbindingGroups :: BindingGroups
              _expressionsIkappaUnique :: Int
              _expressionsIself :: Expressions
              _self =
                  Expression_List _rangeIself _expressionsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionsIbindingGroups
              _lhsOkappaUnique =
                  _expressionsIkappaUnique
              _expressionsObindingGroups =
                  _lhsIbindingGroups
              _expressionsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionsIbindingGroups,_expressionsIkappaUnique,_expressionsIself) =
                  expressions_ _expressionsObindingGroups _expressionsOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Literal :: T_Range ->
                          T_Literal ->
                          T_Expression
sem_Expression_Literal range_ literal_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _literalIself :: Literal
              _self =
                  Expression_Literal _rangeIself _literalIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _literalIself) =
                  literal_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_MustUse :: T_Range ->
                          T_Expression ->
                          T_Expression
sem_Expression_MustUse range_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  Expression_MustUse _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Negate :: T_Range ->
                         T_Expression ->
                         T_Expression
sem_Expression_Negate range_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  Expression_Negate _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_NegateFloat :: T_Range ->
                              T_Expression ->
                              T_Expression
sem_Expression_NegateFloat range_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  Expression_NegateFloat _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_NormalApplication :: T_Range ->
                                    T_Expression ->
                                    T_Expressions ->
                                    T_Expression
sem_Expression_NormalApplication range_ function_ arguments_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _functionObindingGroups :: BindingGroups
              _functionOkappaUnique :: Int
              _argumentsObindingGroups :: BindingGroups
              _argumentsOkappaUnique :: Int
              _rangeIself :: Range
              _functionIbindingGroups :: BindingGroups
              _functionIkappaUnique :: Int
              _functionIself :: Expression
              _argumentsIbindingGroups :: BindingGroups
              _argumentsIkappaUnique :: Int
              _argumentsIself :: Expressions
              _self =
                  Expression_NormalApplication _rangeIself _functionIself _argumentsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _argumentsIbindingGroups
              _lhsOkappaUnique =
                  _argumentsIkappaUnique
              _functionObindingGroups =
                  _lhsIbindingGroups
              _functionOkappaUnique =
                  _lhsIkappaUnique
              _argumentsObindingGroups =
                  _functionIbindingGroups
              _argumentsOkappaUnique =
                  _functionIkappaUnique
              ( _rangeIself) =
                  range_
              ( _functionIbindingGroups,_functionIkappaUnique,_functionIself) =
                  function_ _functionObindingGroups _functionOkappaUnique
              ( _argumentsIbindingGroups,_argumentsIkappaUnique,_argumentsIself) =
                  arguments_ _argumentsObindingGroups _argumentsOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Parenthesized :: T_Range ->
                                T_Expression ->
                                T_Expression
sem_Expression_Parenthesized range_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  Expression_Parenthesized _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_RecordConstruction :: T_Range ->
                                     T_Name ->
                                     T_RecordExpressionBindings ->
                                     T_Expression
sem_Expression_RecordConstruction range_ name_ recordExpressionBindings_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _recordExpressionBindingsObindingGroups :: BindingGroups
              _recordExpressionBindingsOkappaUnique :: Int
              _rangeIself :: Range
              _nameIself :: Name
              _recordExpressionBindingsIbindingGroups :: BindingGroups
              _recordExpressionBindingsIkappaUnique :: Int
              _recordExpressionBindingsIself :: RecordExpressionBindings
              _self =
                  Expression_RecordConstruction _rangeIself _nameIself _recordExpressionBindingsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _recordExpressionBindingsIbindingGroups
              _lhsOkappaUnique =
                  _recordExpressionBindingsIkappaUnique
              _recordExpressionBindingsObindingGroups =
                  _lhsIbindingGroups
              _recordExpressionBindingsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _nameIself) =
                  name_
              ( _recordExpressionBindingsIbindingGroups,_recordExpressionBindingsIkappaUnique,_recordExpressionBindingsIself) =
                  recordExpressionBindings_ _recordExpressionBindingsObindingGroups _recordExpressionBindingsOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_RecordUpdate :: T_Range ->
                               T_Expression ->
                               T_RecordExpressionBindings ->
                               T_Expression
sem_Expression_RecordUpdate range_ expression_ recordExpressionBindings_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _recordExpressionBindingsObindingGroups :: BindingGroups
              _recordExpressionBindingsOkappaUnique :: Int
              _rangeIself :: Range
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _recordExpressionBindingsIbindingGroups :: BindingGroups
              _recordExpressionBindingsIkappaUnique :: Int
              _recordExpressionBindingsIself :: RecordExpressionBindings
              _self =
                  Expression_RecordUpdate _rangeIself _expressionIself _recordExpressionBindingsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _recordExpressionBindingsIbindingGroups
              _lhsOkappaUnique =
                  _recordExpressionBindingsIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              _recordExpressionBindingsObindingGroups =
                  _expressionIbindingGroups
              _recordExpressionBindingsOkappaUnique =
                  _expressionIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
              ( _recordExpressionBindingsIbindingGroups,_recordExpressionBindingsIkappaUnique,_recordExpressionBindingsIself) =
                  recordExpressionBindings_ _recordExpressionBindingsObindingGroups _recordExpressionBindingsOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Tuple :: T_Range ->
                        T_Expressions ->
                        T_Expression
sem_Expression_Tuple range_ expressions_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionsObindingGroups :: BindingGroups
              _expressionsOkappaUnique :: Int
              _rangeIself :: Range
              _expressionsIbindingGroups :: BindingGroups
              _expressionsIkappaUnique :: Int
              _expressionsIself :: Expressions
              _self =
                  Expression_Tuple _rangeIself _expressionsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionsIbindingGroups
              _lhsOkappaUnique =
                  _expressionsIkappaUnique
              _expressionsObindingGroups =
                  _lhsIbindingGroups
              _expressionsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionsIbindingGroups,_expressionsIkappaUnique,_expressionsIself) =
                  expressions_ _expressionsObindingGroups _expressionsOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Typed :: T_Range ->
                        T_Expression ->
                        T_Type ->
                        T_Expression
sem_Expression_Typed range_ expression_ type_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _typeOconstraints :: KindConstraints
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _lhsOself :: Expression
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _typeOkappaUnique :: Int
              _rangeIself :: Range
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _typeIassumptions :: Assumptions
              _typeIconstraints :: KindConstraints
              _typeIkappa :: Kind
              _typeIkappaUnique :: Int
              _typeIself :: Type
              _typeOconstraints =
                  []
              _lhsObindingGroups =
                  _newGroup : _expressionIbindingGroups
              _lhsOkappaUnique =
                  _typeIkappaUnique + length _tvEnv
              _newConstraint =
                  (_typeIkappa <==> star) (mustBeStar _rangeIself "type annotation" _typeIself)
              _tvEnv =
                  zip (getTypeVariables _typeIassumptions) (map TVar [_typeIkappaUnique..])
              (_cset,_aset) =
                  (M.fromList _tvEnv .===. _typeIassumptions) (\n -> unexpected $ "Expression.Typed " ++ show n)
              _newGroup =
                  (M.empty, _aset, _cset ++ _typeIconstraints ++ [_newConstraint])
              _self =
                  Expression_Typed _rangeIself _expressionIself _typeIself
              _lhsOself =
                  _self
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              _typeOkappaUnique =
                  _expressionIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
              ( _typeIassumptions,_typeIconstraints,_typeIkappa,_typeIkappaUnique,_typeIself) =
                  type_ _typeOconstraints _typeOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expression_Variable :: T_Range ->
                           T_Name ->
                           T_Expression
sem_Expression_Variable range_ name_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _nameIself :: Name
              _self =
                  Expression_Variable _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _nameIself) =
                  name_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- Expressions -------------------------------------------------
-- cata
sem_Expressions :: Expressions ->
                   T_Expressions
sem_Expressions list =
    (Prelude.foldr sem_Expressions_Cons sem_Expressions_Nil (Prelude.map sem_Expression list))
-- semantic domain
type T_Expressions = BindingGroups ->
                     Int ->
                     ( BindingGroups,Int,Expressions)
sem_Expressions_Cons :: T_Expression ->
                        T_Expressions ->
                        T_Expressions
sem_Expressions_Cons hd_ tl_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expressions
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _hdObindingGroups :: BindingGroups
              _hdOkappaUnique :: Int
              _tlObindingGroups :: BindingGroups
              _tlOkappaUnique :: Int
              _hdIbindingGroups :: BindingGroups
              _hdIkappaUnique :: Int
              _hdIself :: Expression
              _tlIbindingGroups :: BindingGroups
              _tlIkappaUnique :: Int
              _tlIself :: Expressions
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _tlIbindingGroups
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdObindingGroups =
                  _lhsIbindingGroups
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlObindingGroups =
                  _hdIbindingGroups
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIbindingGroups,_hdIkappaUnique,_hdIself) =
                  hd_ _hdObindingGroups _hdOkappaUnique
              ( _tlIbindingGroups,_tlIkappaUnique,_tlIself) =
                  tl_ _tlObindingGroups _tlOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Expressions_Nil :: T_Expressions
sem_Expressions_Nil =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Expressions
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- FieldDeclaration --------------------------------------------
-- cata
sem_FieldDeclaration :: FieldDeclaration ->
                        T_FieldDeclaration
sem_FieldDeclaration (FieldDeclaration_FieldDeclaration _range _names _type) =
    (sem_FieldDeclaration_FieldDeclaration (sem_Range _range) (sem_Names _names) (sem_AnnotatedType _type))
-- semantic domain
type T_FieldDeclaration = Int ->
                          ( Int,FieldDeclaration)
sem_FieldDeclaration_FieldDeclaration :: T_Range ->
                                         T_Names ->
                                         T_AnnotatedType ->
                                         T_FieldDeclaration
sem_FieldDeclaration_FieldDeclaration range_ names_ type_ =
    (\ _lhsIkappaUnique ->
         (let _lhsOself :: FieldDeclaration
              _lhsOkappaUnique :: Int
              _typeOconstraints :: KindConstraints
              _typeOkappaUnique :: Int
              _rangeIself :: Range
              _namesIself :: Names
              _typeIassumptions :: Assumptions
              _typeIconstraints :: KindConstraints
              _typeIkappa :: Kind
              _typeIkappaUnique :: Int
              _typeIself :: AnnotatedType
              _constraints =
                  internalError "KindInferencing.ag" "n/a" "Field decls are not supported"
              _self =
                  FieldDeclaration_FieldDeclaration _rangeIself _namesIself _typeIself
              _lhsOself =
                  _self
              _lhsOkappaUnique =
                  _typeIkappaUnique
              _typeOconstraints =
                  _constraints
              _typeOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _namesIself) =
                  names_
              ( _typeIassumptions,_typeIconstraints,_typeIkappa,_typeIkappaUnique,_typeIself) =
                  type_ _typeOconstraints _typeOkappaUnique
          in  ( _lhsOkappaUnique,_lhsOself)))
-- FieldDeclarations -------------------------------------------
-- cata
sem_FieldDeclarations :: FieldDeclarations ->
                         T_FieldDeclarations
sem_FieldDeclarations list =
    (Prelude.foldr sem_FieldDeclarations_Cons sem_FieldDeclarations_Nil (Prelude.map sem_FieldDeclaration list))
-- semantic domain
type T_FieldDeclarations = Int ->
                           ( Int,FieldDeclarations)
sem_FieldDeclarations_Cons :: T_FieldDeclaration ->
                              T_FieldDeclarations ->
                              T_FieldDeclarations
sem_FieldDeclarations_Cons hd_ tl_ =
    (\ _lhsIkappaUnique ->
         (let _lhsOself :: FieldDeclarations
              _lhsOkappaUnique :: Int
              _hdOkappaUnique :: Int
              _tlOkappaUnique :: Int
              _hdIkappaUnique :: Int
              _hdIself :: FieldDeclaration
              _tlIkappaUnique :: Int
              _tlIself :: FieldDeclarations
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIkappaUnique,_hdIself) =
                  hd_ _hdOkappaUnique
              ( _tlIkappaUnique,_tlIself) =
                  tl_ _tlOkappaUnique
          in  ( _lhsOkappaUnique,_lhsOself)))
sem_FieldDeclarations_Nil :: T_FieldDeclarations
sem_FieldDeclarations_Nil =
    (\ _lhsIkappaUnique ->
         (let _lhsOself :: FieldDeclarations
              _lhsOkappaUnique :: Int
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsOkappaUnique,_lhsOself)))
-- Fixity ------------------------------------------------------
-- cata
sem_Fixity :: Fixity ->
              T_Fixity
sem_Fixity (Fixity_Infix _range) =
    (sem_Fixity_Infix (sem_Range _range))
sem_Fixity (Fixity_Infixl _range) =
    (sem_Fixity_Infixl (sem_Range _range))
sem_Fixity (Fixity_Infixr _range) =
    (sem_Fixity_Infixr (sem_Range _range))
-- semantic domain
type T_Fixity = ( Fixity)
sem_Fixity_Infix :: T_Range ->
                    T_Fixity
sem_Fixity_Infix range_ =
    (let _lhsOself :: Fixity
         _rangeIself :: Range
         _self =
             Fixity_Infix _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
     in  ( _lhsOself))
sem_Fixity_Infixl :: T_Range ->
                     T_Fixity
sem_Fixity_Infixl range_ =
    (let _lhsOself :: Fixity
         _rangeIself :: Range
         _self =
             Fixity_Infixl _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
     in  ( _lhsOself))
sem_Fixity_Infixr :: T_Range ->
                     T_Fixity
sem_Fixity_Infixr range_ =
    (let _lhsOself :: Fixity
         _rangeIself :: Range
         _self =
             Fixity_Infixr _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
     in  ( _lhsOself))
-- FunctionBinding ---------------------------------------------
-- cata
sem_FunctionBinding :: FunctionBinding ->
                       T_FunctionBinding
sem_FunctionBinding (FunctionBinding_Feedback _range _feedback _functionBinding) =
    (sem_FunctionBinding_Feedback (sem_Range _range) _feedback (sem_FunctionBinding _functionBinding))
sem_FunctionBinding (FunctionBinding_FunctionBinding _range _lefthandside _righthandside) =
    (sem_FunctionBinding_FunctionBinding (sem_Range _range) (sem_LeftHandSide _lefthandside) (sem_RightHandSide _righthandside))
sem_FunctionBinding (FunctionBinding_Hole _range _id) =
    (sem_FunctionBinding_Hole (sem_Range _range) _id)
-- semantic domain
type T_FunctionBinding = BindingGroups ->
                         Int ->
                         ( BindingGroups,Int,FunctionBinding)
sem_FunctionBinding_Feedback :: T_Range ->
                                String ->
                                T_FunctionBinding ->
                                T_FunctionBinding
sem_FunctionBinding_Feedback range_ feedback_ functionBinding_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: FunctionBinding
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _functionBindingObindingGroups :: BindingGroups
              _functionBindingOkappaUnique :: Int
              _rangeIself :: Range
              _functionBindingIbindingGroups :: BindingGroups
              _functionBindingIkappaUnique :: Int
              _functionBindingIself :: FunctionBinding
              _self =
                  FunctionBinding_Feedback _rangeIself feedback_ _functionBindingIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _functionBindingIbindingGroups
              _lhsOkappaUnique =
                  _functionBindingIkappaUnique
              _functionBindingObindingGroups =
                  _lhsIbindingGroups
              _functionBindingOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _functionBindingIbindingGroups,_functionBindingIkappaUnique,_functionBindingIself) =
                  functionBinding_ _functionBindingObindingGroups _functionBindingOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_FunctionBinding_FunctionBinding :: T_Range ->
                                       T_LeftHandSide ->
                                       T_RightHandSide ->
                                       T_FunctionBinding
sem_FunctionBinding_FunctionBinding range_ lefthandside_ righthandside_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: FunctionBinding
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _righthandsideObindingGroups :: BindingGroups
              _righthandsideOkappaUnique :: Int
              _rangeIself :: Range
              _lefthandsideIself :: LeftHandSide
              _righthandsideIbindingGroups :: BindingGroups
              _righthandsideIkappaUnique :: Int
              _righthandsideIself :: RightHandSide
              _self =
                  FunctionBinding_FunctionBinding _rangeIself _lefthandsideIself _righthandsideIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _righthandsideIbindingGroups
              _lhsOkappaUnique =
                  _righthandsideIkappaUnique
              _righthandsideObindingGroups =
                  _lhsIbindingGroups
              _righthandsideOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _lefthandsideIself) =
                  lefthandside_
              ( _righthandsideIbindingGroups,_righthandsideIkappaUnique,_righthandsideIself) =
                  righthandside_ _righthandsideObindingGroups _righthandsideOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_FunctionBinding_Hole :: T_Range ->
                            Integer ->
                            T_FunctionBinding
sem_FunctionBinding_Hole range_ id_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: FunctionBinding
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _self =
                  FunctionBinding_Hole _rangeIself id_
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- FunctionBindings --------------------------------------------
-- cata
sem_FunctionBindings :: FunctionBindings ->
                        T_FunctionBindings
sem_FunctionBindings list =
    (Prelude.foldr sem_FunctionBindings_Cons sem_FunctionBindings_Nil (Prelude.map sem_FunctionBinding list))
-- semantic domain
type T_FunctionBindings = BindingGroups ->
                          Int ->
                          ( BindingGroups,Int,FunctionBindings)
sem_FunctionBindings_Cons :: T_FunctionBinding ->
                             T_FunctionBindings ->
                             T_FunctionBindings
sem_FunctionBindings_Cons hd_ tl_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: FunctionBindings
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _hdObindingGroups :: BindingGroups
              _hdOkappaUnique :: Int
              _tlObindingGroups :: BindingGroups
              _tlOkappaUnique :: Int
              _hdIbindingGroups :: BindingGroups
              _hdIkappaUnique :: Int
              _hdIself :: FunctionBinding
              _tlIbindingGroups :: BindingGroups
              _tlIkappaUnique :: Int
              _tlIself :: FunctionBindings
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _tlIbindingGroups
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdObindingGroups =
                  _lhsIbindingGroups
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlObindingGroups =
                  _hdIbindingGroups
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIbindingGroups,_hdIkappaUnique,_hdIself) =
                  hd_ _hdObindingGroups _hdOkappaUnique
              ( _tlIbindingGroups,_tlIkappaUnique,_tlIself) =
                  tl_ _tlObindingGroups _tlOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_FunctionBindings_Nil :: T_FunctionBindings
sem_FunctionBindings_Nil =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: FunctionBindings
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- GuardedExpression -------------------------------------------
-- cata
sem_GuardedExpression :: GuardedExpression ->
                         T_GuardedExpression
sem_GuardedExpression (GuardedExpression_GuardedExpression _range _guard _expression) =
    (sem_GuardedExpression_GuardedExpression (sem_Range _range) (sem_Expression _guard) (sem_Expression _expression))
-- semantic domain
type T_GuardedExpression = BindingGroups ->
                           Int ->
                           ( BindingGroups,Int,GuardedExpression)
sem_GuardedExpression_GuardedExpression :: T_Range ->
                                           T_Expression ->
                                           T_Expression ->
                                           T_GuardedExpression
sem_GuardedExpression_GuardedExpression range_ guard_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: GuardedExpression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _guardObindingGroups :: BindingGroups
              _guardOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _guardIbindingGroups :: BindingGroups
              _guardIkappaUnique :: Int
              _guardIself :: Expression
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  GuardedExpression_GuardedExpression _rangeIself _guardIself _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _guardObindingGroups =
                  _lhsIbindingGroups
              _guardOkappaUnique =
                  _lhsIkappaUnique
              _expressionObindingGroups =
                  _guardIbindingGroups
              _expressionOkappaUnique =
                  _guardIkappaUnique
              ( _rangeIself) =
                  range_
              ( _guardIbindingGroups,_guardIkappaUnique,_guardIself) =
                  guard_ _guardObindingGroups _guardOkappaUnique
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- GuardedExpressions ------------------------------------------
-- cata
sem_GuardedExpressions :: GuardedExpressions ->
                          T_GuardedExpressions
sem_GuardedExpressions list =
    (Prelude.foldr sem_GuardedExpressions_Cons sem_GuardedExpressions_Nil (Prelude.map sem_GuardedExpression list))
-- semantic domain
type T_GuardedExpressions = BindingGroups ->
                            Int ->
                            ( BindingGroups,Int,GuardedExpressions)
sem_GuardedExpressions_Cons :: T_GuardedExpression ->
                               T_GuardedExpressions ->
                               T_GuardedExpressions
sem_GuardedExpressions_Cons hd_ tl_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: GuardedExpressions
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _hdObindingGroups :: BindingGroups
              _hdOkappaUnique :: Int
              _tlObindingGroups :: BindingGroups
              _tlOkappaUnique :: Int
              _hdIbindingGroups :: BindingGroups
              _hdIkappaUnique :: Int
              _hdIself :: GuardedExpression
              _tlIbindingGroups :: BindingGroups
              _tlIkappaUnique :: Int
              _tlIself :: GuardedExpressions
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _tlIbindingGroups
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdObindingGroups =
                  _lhsIbindingGroups
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlObindingGroups =
                  _hdIbindingGroups
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIbindingGroups,_hdIkappaUnique,_hdIself) =
                  hd_ _hdObindingGroups _hdOkappaUnique
              ( _tlIbindingGroups,_tlIkappaUnique,_tlIself) =
                  tl_ _tlObindingGroups _tlOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_GuardedExpressions_Nil :: T_GuardedExpressions
sem_GuardedExpressions_Nil =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: GuardedExpressions
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- Import ------------------------------------------------------
-- cata
sem_Import :: Import ->
              T_Import
sem_Import (Import_TypeOrClass _range _name _names) =
    (sem_Import_TypeOrClass (sem_Range _range) (sem_Name _name) (sem_MaybeNames _names))
sem_Import (Import_TypeOrClassComplete _range _name) =
    (sem_Import_TypeOrClassComplete (sem_Range _range) (sem_Name _name))
sem_Import (Import_Variable _range _name) =
    (sem_Import_Variable (sem_Range _range) (sem_Name _name))
-- semantic domain
type T_Import = ( Import)
sem_Import_TypeOrClass :: T_Range ->
                          T_Name ->
                          T_MaybeNames ->
                          T_Import
sem_Import_TypeOrClass range_ name_ names_ =
    (let _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _namesIself :: MaybeNames
         _self =
             Import_TypeOrClass _rangeIself _nameIself _namesIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
         ( _namesIself) =
             names_
     in  ( _lhsOself))
sem_Import_TypeOrClassComplete :: T_Range ->
                                  T_Name ->
                                  T_Import
sem_Import_TypeOrClassComplete range_ name_ =
    (let _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Import_TypeOrClassComplete _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
     in  ( _lhsOself))
sem_Import_Variable :: T_Range ->
                       T_Name ->
                       T_Import
sem_Import_Variable range_ name_ =
    (let _lhsOself :: Import
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Import_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
     in  ( _lhsOself))
-- ImportDeclaration -------------------------------------------
-- cata
sem_ImportDeclaration :: ImportDeclaration ->
                         T_ImportDeclaration
sem_ImportDeclaration (ImportDeclaration_Empty _range) =
    (sem_ImportDeclaration_Empty (sem_Range _range))
sem_ImportDeclaration (ImportDeclaration_Import _range _qualified _name _asname _importspecification) =
    (sem_ImportDeclaration_Import (sem_Range _range) _qualified (sem_Name _name) (sem_MaybeName _asname) (sem_MaybeImportSpecification _importspecification))
-- semantic domain
type T_ImportDeclaration = ( ImportDeclaration)
sem_ImportDeclaration_Empty :: T_Range ->
                               T_ImportDeclaration
sem_ImportDeclaration_Empty range_ =
    (let _lhsOself :: ImportDeclaration
         _rangeIself :: Range
         _self =
             ImportDeclaration_Empty _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
     in  ( _lhsOself))
sem_ImportDeclaration_Import :: T_Range ->
                                Bool ->
                                T_Name ->
                                T_MaybeName ->
                                T_MaybeImportSpecification ->
                                T_ImportDeclaration
sem_ImportDeclaration_Import range_ qualified_ name_ asname_ importspecification_ =
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
             range_
         ( _nameIself) =
             name_
         ( _asnameIself) =
             asname_
         ( _importspecificationIself) =
             importspecification_
     in  ( _lhsOself))
-- ImportDeclarations ------------------------------------------
-- cata
sem_ImportDeclarations :: ImportDeclarations ->
                          T_ImportDeclarations
sem_ImportDeclarations list =
    (Prelude.foldr sem_ImportDeclarations_Cons sem_ImportDeclarations_Nil (Prelude.map sem_ImportDeclaration list))
-- semantic domain
type T_ImportDeclarations = ( ImportDeclarations)
sem_ImportDeclarations_Cons :: T_ImportDeclaration ->
                               T_ImportDeclarations ->
                               T_ImportDeclarations
sem_ImportDeclarations_Cons hd_ tl_ =
    (let _lhsOself :: ImportDeclarations
         _hdIself :: ImportDeclaration
         _tlIself :: ImportDeclarations
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_ImportDeclarations_Nil :: T_ImportDeclarations
sem_ImportDeclarations_Nil =
    (let _lhsOself :: ImportDeclarations
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- ImportSpecification -----------------------------------------
-- cata
sem_ImportSpecification :: ImportSpecification ->
                           T_ImportSpecification
sem_ImportSpecification (ImportSpecification_Import _range _hiding _imports) =
    (sem_ImportSpecification_Import (sem_Range _range) _hiding (sem_Imports _imports))
-- semantic domain
type T_ImportSpecification = ( ImportSpecification)
sem_ImportSpecification_Import :: T_Range ->
                                  Bool ->
                                  T_Imports ->
                                  T_ImportSpecification
sem_ImportSpecification_Import range_ hiding_ imports_ =
    (let _lhsOself :: ImportSpecification
         _rangeIself :: Range
         _importsIself :: Imports
         _self =
             ImportSpecification_Import _rangeIself hiding_ _importsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _importsIself) =
             imports_
     in  ( _lhsOself))
-- Imports -----------------------------------------------------
-- cata
sem_Imports :: Imports ->
               T_Imports
sem_Imports list =
    (Prelude.foldr sem_Imports_Cons sem_Imports_Nil (Prelude.map sem_Import list))
-- semantic domain
type T_Imports = ( Imports)
sem_Imports_Cons :: T_Import ->
                    T_Imports ->
                    T_Imports
sem_Imports_Cons hd_ tl_ =
    (let _lhsOself :: Imports
         _hdIself :: Import
         _tlIself :: Imports
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Imports_Nil :: T_Imports
sem_Imports_Nil =
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
sem_LeftHandSide (LeftHandSide_Function _range _name _patterns) =
    (sem_LeftHandSide_Function (sem_Range _range) (sem_Name _name) (sem_Patterns _patterns))
sem_LeftHandSide (LeftHandSide_Infix _range _leftPattern _operator _rightPattern) =
    (sem_LeftHandSide_Infix (sem_Range _range) (sem_Pattern _leftPattern) (sem_Name _operator) (sem_Pattern _rightPattern))
sem_LeftHandSide (LeftHandSide_Parenthesized _range _lefthandside _patterns) =
    (sem_LeftHandSide_Parenthesized (sem_Range _range) (sem_LeftHandSide _lefthandside) (sem_Patterns _patterns))
-- semantic domain
type T_LeftHandSide = ( LeftHandSide)
sem_LeftHandSide_Function :: T_Range ->
                             T_Name ->
                             T_Patterns ->
                             T_LeftHandSide
sem_LeftHandSide_Function range_ name_ patterns_ =
    (let _lhsOself :: LeftHandSide
         _rangeIself :: Range
         _nameIself :: Name
         _patternsIself :: Patterns
         _self =
             LeftHandSide_Function _rangeIself _nameIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
         ( _patternsIself) =
             patterns_
     in  ( _lhsOself))
sem_LeftHandSide_Infix :: T_Range ->
                          T_Pattern ->
                          T_Name ->
                          T_Pattern ->
                          T_LeftHandSide
sem_LeftHandSide_Infix range_ leftPattern_ operator_ rightPattern_ =
    (let _lhsOself :: LeftHandSide
         _rangeIself :: Range
         _leftPatternIself :: Pattern
         _operatorIself :: Name
         _rightPatternIself :: Pattern
         _self =
             LeftHandSide_Infix _rangeIself _leftPatternIself _operatorIself _rightPatternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _leftPatternIself) =
             leftPattern_
         ( _operatorIself) =
             operator_
         ( _rightPatternIself) =
             rightPattern_
     in  ( _lhsOself))
sem_LeftHandSide_Parenthesized :: T_Range ->
                                  T_LeftHandSide ->
                                  T_Patterns ->
                                  T_LeftHandSide
sem_LeftHandSide_Parenthesized range_ lefthandside_ patterns_ =
    (let _lhsOself :: LeftHandSide
         _rangeIself :: Range
         _lefthandsideIself :: LeftHandSide
         _patternsIself :: Patterns
         _self =
             LeftHandSide_Parenthesized _rangeIself _lefthandsideIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _lefthandsideIself) =
             lefthandside_
         ( _patternsIself) =
             patterns_
     in  ( _lhsOself))
-- Literal -----------------------------------------------------
-- cata
sem_Literal :: Literal ->
               T_Literal
sem_Literal (Literal_Char _range _value) =
    (sem_Literal_Char (sem_Range _range) _value)
sem_Literal (Literal_Float _range _value) =
    (sem_Literal_Float (sem_Range _range) _value)
sem_Literal (Literal_Int _range _value) =
    (sem_Literal_Int (sem_Range _range) _value)
sem_Literal (Literal_String _range _value) =
    (sem_Literal_String (sem_Range _range) _value)
-- semantic domain
type T_Literal = ( Literal)
sem_Literal_Char :: T_Range ->
                    String ->
                    T_Literal
sem_Literal_Char range_ value_ =
    (let _lhsOself :: Literal
         _rangeIself :: Range
         _self =
             Literal_Char _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
     in  ( _lhsOself))
sem_Literal_Float :: T_Range ->
                     String ->
                     T_Literal
sem_Literal_Float range_ value_ =
    (let _lhsOself :: Literal
         _rangeIself :: Range
         _self =
             Literal_Float _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
     in  ( _lhsOself))
sem_Literal_Int :: T_Range ->
                   String ->
                   T_Literal
sem_Literal_Int range_ value_ =
    (let _lhsOself :: Literal
         _rangeIself :: Range
         _self =
             Literal_Int _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
     in  ( _lhsOself))
sem_Literal_String :: T_Range ->
                      String ->
                      T_Literal
sem_Literal_String range_ value_ =
    (let _lhsOself :: Literal
         _rangeIself :: Range
         _self =
             Literal_String _rangeIself value_
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
     in  ( _lhsOself))
-- MaybeDeclarations -------------------------------------------
-- cata
sem_MaybeDeclarations :: MaybeDeclarations ->
                         T_MaybeDeclarations
sem_MaybeDeclarations (MaybeDeclarations_Just _declarations) =
    (sem_MaybeDeclarations_Just (sem_Declarations _declarations))
sem_MaybeDeclarations (MaybeDeclarations_Nothing) =
    (sem_MaybeDeclarations_Nothing)
-- semantic domain
type T_MaybeDeclarations = BindingGroups ->
                           Int ->
                           ( BindingGroups,Int,MaybeDeclarations)
sem_MaybeDeclarations_Just :: T_Declarations ->
                              T_MaybeDeclarations
sem_MaybeDeclarations_Just declarations_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: MaybeDeclarations
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _declarationsObindingGroups :: BindingGroups
              _declarationsOkappaUnique :: Int
              _declarationsIbindingGroups :: BindingGroups
              _declarationsIkappaUnique :: Int
              _declarationsIself :: Declarations
              _self =
                  MaybeDeclarations_Just _declarationsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _declarationsIbindingGroups
              _lhsOkappaUnique =
                  _declarationsIkappaUnique
              _declarationsObindingGroups =
                  _lhsIbindingGroups
              _declarationsOkappaUnique =
                  _lhsIkappaUnique
              ( _declarationsIbindingGroups,_declarationsIkappaUnique,_declarationsIself) =
                  declarations_ _declarationsObindingGroups _declarationsOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_MaybeDeclarations_Nothing :: T_MaybeDeclarations
sem_MaybeDeclarations_Nothing =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: MaybeDeclarations
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _self =
                  MaybeDeclarations_Nothing
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- MaybeExports ------------------------------------------------
-- cata
sem_MaybeExports :: MaybeExports ->
                    T_MaybeExports
sem_MaybeExports (MaybeExports_Just _exports) =
    (sem_MaybeExports_Just (sem_Exports _exports))
sem_MaybeExports (MaybeExports_Nothing) =
    (sem_MaybeExports_Nothing)
-- semantic domain
type T_MaybeExports = ( MaybeExports)
sem_MaybeExports_Just :: T_Exports ->
                         T_MaybeExports
sem_MaybeExports_Just exports_ =
    (let _lhsOself :: MaybeExports
         _exportsIself :: Exports
         _self =
             MaybeExports_Just _exportsIself
         _lhsOself =
             _self
         ( _exportsIself) =
             exports_
     in  ( _lhsOself))
sem_MaybeExports_Nothing :: T_MaybeExports
sem_MaybeExports_Nothing =
    (let _lhsOself :: MaybeExports
         _self =
             MaybeExports_Nothing
         _lhsOself =
             _self
     in  ( _lhsOself))
-- MaybeExpression ---------------------------------------------
-- cata
sem_MaybeExpression :: MaybeExpression ->
                       T_MaybeExpression
sem_MaybeExpression (MaybeExpression_Just _expression) =
    (sem_MaybeExpression_Just (sem_Expression _expression))
sem_MaybeExpression (MaybeExpression_Nothing) =
    (sem_MaybeExpression_Nothing)
-- semantic domain
type T_MaybeExpression = BindingGroups ->
                         Int ->
                         ( BindingGroups,Int,MaybeExpression)
sem_MaybeExpression_Just :: T_Expression ->
                            T_MaybeExpression
sem_MaybeExpression_Just expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: MaybeExpression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  MaybeExpression_Just _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_MaybeExpression_Nothing :: T_MaybeExpression
sem_MaybeExpression_Nothing =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: MaybeExpression
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _self =
                  MaybeExpression_Nothing
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- MaybeImportSpecification ------------------------------------
-- cata
sem_MaybeImportSpecification :: MaybeImportSpecification ->
                                T_MaybeImportSpecification
sem_MaybeImportSpecification (MaybeImportSpecification_Just _importspecification) =
    (sem_MaybeImportSpecification_Just (sem_ImportSpecification _importspecification))
sem_MaybeImportSpecification (MaybeImportSpecification_Nothing) =
    (sem_MaybeImportSpecification_Nothing)
-- semantic domain
type T_MaybeImportSpecification = ( MaybeImportSpecification)
sem_MaybeImportSpecification_Just :: T_ImportSpecification ->
                                     T_MaybeImportSpecification
sem_MaybeImportSpecification_Just importspecification_ =
    (let _lhsOself :: MaybeImportSpecification
         _importspecificationIself :: ImportSpecification
         _self =
             MaybeImportSpecification_Just _importspecificationIself
         _lhsOself =
             _self
         ( _importspecificationIself) =
             importspecification_
     in  ( _lhsOself))
sem_MaybeImportSpecification_Nothing :: T_MaybeImportSpecification
sem_MaybeImportSpecification_Nothing =
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
sem_MaybeInt (MaybeInt_Just _int) =
    (sem_MaybeInt_Just _int)
sem_MaybeInt (MaybeInt_Nothing) =
    (sem_MaybeInt_Nothing)
-- semantic domain
type T_MaybeInt = ( MaybeInt)
sem_MaybeInt_Just :: Int ->
                     T_MaybeInt
sem_MaybeInt_Just int_ =
    (let _lhsOself :: MaybeInt
         _self =
             MaybeInt_Just int_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_MaybeInt_Nothing :: T_MaybeInt
sem_MaybeInt_Nothing =
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
sem_MaybeName (MaybeName_Just _name) =
    (sem_MaybeName_Just (sem_Name _name))
sem_MaybeName (MaybeName_Nothing) =
    (sem_MaybeName_Nothing)
-- semantic domain
type T_MaybeName = ( MaybeName)
sem_MaybeName_Just :: T_Name ->
                      T_MaybeName
sem_MaybeName_Just name_ =
    (let _lhsOself :: MaybeName
         _nameIself :: Name
         _self =
             MaybeName_Just _nameIself
         _lhsOself =
             _self
         ( _nameIself) =
             name_
     in  ( _lhsOself))
sem_MaybeName_Nothing :: T_MaybeName
sem_MaybeName_Nothing =
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
sem_MaybeNames (MaybeNames_Just _names) =
    (sem_MaybeNames_Just (sem_Names _names))
sem_MaybeNames (MaybeNames_Nothing) =
    (sem_MaybeNames_Nothing)
-- semantic domain
type T_MaybeNames = ( MaybeNames)
sem_MaybeNames_Just :: T_Names ->
                       T_MaybeNames
sem_MaybeNames_Just names_ =
    (let _lhsOself :: MaybeNames
         _namesIself :: Names
         _self =
             MaybeNames_Just _namesIself
         _lhsOself =
             _self
         ( _namesIself) =
             names_
     in  ( _lhsOself))
sem_MaybeNames_Nothing :: T_MaybeNames
sem_MaybeNames_Nothing =
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
sem_Module (Module_Module _range _name _exports _body) =
    (sem_Module_Module (sem_Range _range) (sem_MaybeName _name) (sem_MaybeExports _exports) (sem_Body _body))
-- semantic domain
type T_Module = ImportEnvironment ->
                ([Option]) ->
                ( (IO ()),KindEnvironment,KindErrors,Module)
sem_Module_Module :: T_Range ->
                     T_MaybeName ->
                     T_MaybeExports ->
                     T_Body ->
                     T_Module
sem_Module_Module range_ name_ exports_ body_ =
    (\ _lhsIimportEnvironment
       _lhsIoptions ->
         (let _lhsOkindErrors :: KindErrors
              _lhsOdebugIO :: (IO ())
              _bodyOkappaUnique :: Int
              _lhsOself :: Module
              _lhsOkindEnvironment :: KindEnvironment
              _bodyOimportEnvironment :: ImportEnvironment
              _rangeIself :: Range
              _nameIself :: MaybeName
              _exportsIself :: MaybeExports
              _bodyIconstraints :: KindConstraints
              _bodyIenvironment :: PatternAssumptions
              _bodyIkappaUnique :: Int
              _bodyIself :: Body
              _lhsOkindErrors =
                  _substitution |-> (map fst _kindErrors)
              _lhsOdebugIO =
                  putStrLn (show _logEntries)
              _bodyOkappaUnique =
                  0
              ((SolveResult _kappaUniqueAtTheEnd _substitution _ _ _kindErrors),_logEntries) =
                  solve (solveOptions { uniqueCounter = _bodyIkappaUnique }) _bodyIconstraints greedyConstraintSolver
              _kindEnvironment =
                  let f kind = generalizeAll ([] .=>. defaultToStar (_substitution |-> kind))
                  in M.map f _bodyIenvironment
              _self =
                  Module_Module _rangeIself _nameIself _exportsIself _bodyIself
              _lhsOself =
                  _self
              _lhsOkindEnvironment =
                  _kindEnvironment
              _bodyOimportEnvironment =
                  _lhsIimportEnvironment
              ( _rangeIself) =
                  range_
              ( _nameIself) =
                  name_
              ( _exportsIself) =
                  exports_
              ( _bodyIconstraints,_bodyIenvironment,_bodyIkappaUnique,_bodyIself) =
                  body_ _bodyOimportEnvironment _bodyOkappaUnique
          in  ( _lhsOdebugIO,_lhsOkindEnvironment,_lhsOkindErrors,_lhsOself)))
-- Name --------------------------------------------------------
-- cata
sem_Name :: Name ->
            T_Name
sem_Name (Name_Identifier _range _module _name) =
    (sem_Name_Identifier (sem_Range _range) (sem_Strings _module) _name)
sem_Name (Name_Operator _range _module _name) =
    (sem_Name_Operator (sem_Range _range) (sem_Strings _module) _name)
sem_Name (Name_Special _range _module _name) =
    (sem_Name_Special (sem_Range _range) (sem_Strings _module) _name)
-- semantic domain
type T_Name = ( Name)
sem_Name_Identifier :: T_Range ->
                       T_Strings ->
                       String ->
                       T_Name
sem_Name_Identifier range_ module_ name_ =
    (let _lhsOself :: Name
         _rangeIself :: Range
         _moduleIself :: Strings
         _self =
             Name_Identifier _rangeIself _moduleIself name_
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _moduleIself) =
             module_
     in  ( _lhsOself))
sem_Name_Operator :: T_Range ->
                     T_Strings ->
                     String ->
                     T_Name
sem_Name_Operator range_ module_ name_ =
    (let _lhsOself :: Name
         _rangeIself :: Range
         _moduleIself :: Strings
         _self =
             Name_Operator _rangeIself _moduleIself name_
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _moduleIself) =
             module_
     in  ( _lhsOself))
sem_Name_Special :: T_Range ->
                    T_Strings ->
                    String ->
                    T_Name
sem_Name_Special range_ module_ name_ =
    (let _lhsOself :: Name
         _rangeIself :: Range
         _moduleIself :: Strings
         _self =
             Name_Special _rangeIself _moduleIself name_
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _moduleIself) =
             module_
     in  ( _lhsOself))
-- Names -------------------------------------------------------
-- cata
sem_Names :: Names ->
             T_Names
sem_Names list =
    (Prelude.foldr sem_Names_Cons sem_Names_Nil (Prelude.map sem_Name list))
-- semantic domain
type T_Names = ( Names)
sem_Names_Cons :: T_Name ->
                  T_Names ->
                  T_Names
sem_Names_Cons hd_ tl_ =
    (let _lhsOself :: Names
         _hdIself :: Name
         _tlIself :: Names
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Names_Nil :: T_Names
sem_Names_Nil =
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
sem_Pattern (Pattern_As _range _name _pattern) =
    (sem_Pattern_As (sem_Range _range) (sem_Name _name) (sem_Pattern _pattern))
sem_Pattern (Pattern_Constructor _range _name _patterns) =
    (sem_Pattern_Constructor (sem_Range _range) (sem_Name _name) (sem_Patterns _patterns))
sem_Pattern (Pattern_Hole _range _id) =
    (sem_Pattern_Hole (sem_Range _range) _id)
sem_Pattern (Pattern_InfixConstructor _range _leftPattern _constructorOperator _rightPattern) =
    (sem_Pattern_InfixConstructor (sem_Range _range) (sem_Pattern _leftPattern) (sem_Name _constructorOperator) (sem_Pattern _rightPattern))
sem_Pattern (Pattern_Irrefutable _range _pattern) =
    (sem_Pattern_Irrefutable (sem_Range _range) (sem_Pattern _pattern))
sem_Pattern (Pattern_List _range _patterns) =
    (sem_Pattern_List (sem_Range _range) (sem_Patterns _patterns))
sem_Pattern (Pattern_Literal _range _literal) =
    (sem_Pattern_Literal (sem_Range _range) (sem_Literal _literal))
sem_Pattern (Pattern_Negate _range _literal) =
    (sem_Pattern_Negate (sem_Range _range) (sem_Literal _literal))
sem_Pattern (Pattern_NegateFloat _range _literal) =
    (sem_Pattern_NegateFloat (sem_Range _range) (sem_Literal _literal))
sem_Pattern (Pattern_Parenthesized _range _pattern) =
    (sem_Pattern_Parenthesized (sem_Range _range) (sem_Pattern _pattern))
sem_Pattern (Pattern_Record _range _name _recordPatternBindings) =
    (sem_Pattern_Record (sem_Range _range) (sem_Name _name) (sem_RecordPatternBindings _recordPatternBindings))
sem_Pattern (Pattern_Successor _range _name _literal) =
    (sem_Pattern_Successor (sem_Range _range) (sem_Name _name) (sem_Literal _literal))
sem_Pattern (Pattern_Tuple _range _patterns) =
    (sem_Pattern_Tuple (sem_Range _range) (sem_Patterns _patterns))
sem_Pattern (Pattern_Variable _range _name) =
    (sem_Pattern_Variable (sem_Range _range) (sem_Name _name))
sem_Pattern (Pattern_Wildcard _range) =
    (sem_Pattern_Wildcard (sem_Range _range))
-- semantic domain
type T_Pattern = ( Pattern)
sem_Pattern_As :: T_Range ->
                  T_Name ->
                  T_Pattern ->
                  T_Pattern
sem_Pattern_As range_ name_ pattern_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _patternIself :: Pattern
         _self =
             Pattern_As _rangeIself _nameIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
         ( _patternIself) =
             pattern_
     in  ( _lhsOself))
sem_Pattern_Constructor :: T_Range ->
                           T_Name ->
                           T_Patterns ->
                           T_Pattern
sem_Pattern_Constructor range_ name_ patterns_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _patternsIself :: Patterns
         _self =
             Pattern_Constructor _rangeIself _nameIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
         ( _patternsIself) =
             patterns_
     in  ( _lhsOself))
sem_Pattern_Hole :: T_Range ->
                    Integer ->
                    T_Pattern
sem_Pattern_Hole range_ id_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _self =
             Pattern_Hole _rangeIself id_
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
     in  ( _lhsOself))
sem_Pattern_InfixConstructor :: T_Range ->
                                T_Pattern ->
                                T_Name ->
                                T_Pattern ->
                                T_Pattern
sem_Pattern_InfixConstructor range_ leftPattern_ constructorOperator_ rightPattern_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _leftPatternIself :: Pattern
         _constructorOperatorIself :: Name
         _rightPatternIself :: Pattern
         _self =
             Pattern_InfixConstructor _rangeIself _leftPatternIself _constructorOperatorIself _rightPatternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _leftPatternIself) =
             leftPattern_
         ( _constructorOperatorIself) =
             constructorOperator_
         ( _rightPatternIself) =
             rightPattern_
     in  ( _lhsOself))
sem_Pattern_Irrefutable :: T_Range ->
                           T_Pattern ->
                           T_Pattern
sem_Pattern_Irrefutable range_ pattern_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _patternIself :: Pattern
         _self =
             Pattern_Irrefutable _rangeIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _patternIself) =
             pattern_
     in  ( _lhsOself))
sem_Pattern_List :: T_Range ->
                    T_Patterns ->
                    T_Pattern
sem_Pattern_List range_ patterns_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _patternsIself :: Patterns
         _self =
             Pattern_List _rangeIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _patternsIself) =
             patterns_
     in  ( _lhsOself))
sem_Pattern_Literal :: T_Range ->
                       T_Literal ->
                       T_Pattern
sem_Pattern_Literal range_ literal_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _literalIself :: Literal
         _self =
             Pattern_Literal _rangeIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _literalIself) =
             literal_
     in  ( _lhsOself))
sem_Pattern_Negate :: T_Range ->
                      T_Literal ->
                      T_Pattern
sem_Pattern_Negate range_ literal_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _literalIself :: Literal
         _self =
             Pattern_Negate _rangeIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _literalIself) =
             literal_
     in  ( _lhsOself))
sem_Pattern_NegateFloat :: T_Range ->
                           T_Literal ->
                           T_Pattern
sem_Pattern_NegateFloat range_ literal_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _literalIself :: Literal
         _self =
             Pattern_NegateFloat _rangeIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _literalIself) =
             literal_
     in  ( _lhsOself))
sem_Pattern_Parenthesized :: T_Range ->
                             T_Pattern ->
                             T_Pattern
sem_Pattern_Parenthesized range_ pattern_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _patternIself :: Pattern
         _self =
             Pattern_Parenthesized _rangeIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _patternIself) =
             pattern_
     in  ( _lhsOself))
sem_Pattern_Record :: T_Range ->
                      T_Name ->
                      T_RecordPatternBindings ->
                      T_Pattern
sem_Pattern_Record range_ name_ recordPatternBindings_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _recordPatternBindingsIself :: RecordPatternBindings
         _self =
             Pattern_Record _rangeIself _nameIself _recordPatternBindingsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
         ( _recordPatternBindingsIself) =
             recordPatternBindings_
     in  ( _lhsOself))
sem_Pattern_Successor :: T_Range ->
                         T_Name ->
                         T_Literal ->
                         T_Pattern
sem_Pattern_Successor range_ name_ literal_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _literalIself :: Literal
         _self =
             Pattern_Successor _rangeIself _nameIself _literalIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
         ( _literalIself) =
             literal_
     in  ( _lhsOself))
sem_Pattern_Tuple :: T_Range ->
                     T_Patterns ->
                     T_Pattern
sem_Pattern_Tuple range_ patterns_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _patternsIself :: Patterns
         _self =
             Pattern_Tuple _rangeIself _patternsIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _patternsIself) =
             patterns_
     in  ( _lhsOself))
sem_Pattern_Variable :: T_Range ->
                        T_Name ->
                        T_Pattern
sem_Pattern_Variable range_ name_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _nameIself :: Name
         _self =
             Pattern_Variable _rangeIself _nameIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
     in  ( _lhsOself))
sem_Pattern_Wildcard :: T_Range ->
                        T_Pattern
sem_Pattern_Wildcard range_ =
    (let _lhsOself :: Pattern
         _rangeIself :: Range
         _self =
             Pattern_Wildcard _rangeIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
     in  ( _lhsOself))
-- Patterns ----------------------------------------------------
-- cata
sem_Patterns :: Patterns ->
                T_Patterns
sem_Patterns list =
    (Prelude.foldr sem_Patterns_Cons sem_Patterns_Nil (Prelude.map sem_Pattern list))
-- semantic domain
type T_Patterns = ( Patterns)
sem_Patterns_Cons :: T_Pattern ->
                     T_Patterns ->
                     T_Patterns
sem_Patterns_Cons hd_ tl_ =
    (let _lhsOself :: Patterns
         _hdIself :: Pattern
         _tlIself :: Patterns
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Patterns_Nil :: T_Patterns
sem_Patterns_Nil =
    (let _lhsOself :: Patterns
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- Position ----------------------------------------------------
-- cata
sem_Position :: Position ->
                T_Position
sem_Position (Position_Position _filename _line _column) =
    (sem_Position_Position _filename _line _column)
sem_Position (Position_Unknown) =
    (sem_Position_Unknown)
-- semantic domain
type T_Position = ( Position)
sem_Position_Position :: String ->
                         Int ->
                         Int ->
                         T_Position
sem_Position_Position filename_ line_ column_ =
    (let _lhsOself :: Position
         _self =
             Position_Position filename_ line_ column_
         _lhsOself =
             _self
     in  ( _lhsOself))
sem_Position_Unknown :: T_Position
sem_Position_Unknown =
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
sem_Qualifier (Qualifier_Empty _range) =
    (sem_Qualifier_Empty (sem_Range _range))
sem_Qualifier (Qualifier_Generator _range _pattern _expression) =
    (sem_Qualifier_Generator (sem_Range _range) (sem_Pattern _pattern) (sem_Expression _expression))
sem_Qualifier (Qualifier_Guard _range _guard) =
    (sem_Qualifier_Guard (sem_Range _range) (sem_Expression _guard))
sem_Qualifier (Qualifier_Let _range _declarations) =
    (sem_Qualifier_Let (sem_Range _range) (sem_Declarations _declarations))
-- semantic domain
type T_Qualifier = BindingGroups ->
                   Int ->
                   ( BindingGroups,Int,Qualifier)
sem_Qualifier_Empty :: T_Range ->
                       T_Qualifier
sem_Qualifier_Empty range_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Qualifier
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _self =
                  Qualifier_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Qualifier_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Qualifier
sem_Qualifier_Generator range_ pattern_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Qualifier
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _patternIself :: Pattern
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  Qualifier_Generator _rangeIself _patternIself _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _patternIself) =
                  pattern_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Qualifier_Guard :: T_Range ->
                       T_Expression ->
                       T_Qualifier
sem_Qualifier_Guard range_ guard_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Qualifier
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _guardObindingGroups :: BindingGroups
              _guardOkappaUnique :: Int
              _rangeIself :: Range
              _guardIbindingGroups :: BindingGroups
              _guardIkappaUnique :: Int
              _guardIself :: Expression
              _self =
                  Qualifier_Guard _rangeIself _guardIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _guardIbindingGroups
              _lhsOkappaUnique =
                  _guardIkappaUnique
              _guardObindingGroups =
                  _lhsIbindingGroups
              _guardOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _guardIbindingGroups,_guardIkappaUnique,_guardIself) =
                  guard_ _guardObindingGroups _guardOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Qualifier_Let :: T_Range ->
                     T_Declarations ->
                     T_Qualifier
sem_Qualifier_Let range_ declarations_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Qualifier
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _declarationsObindingGroups :: BindingGroups
              _declarationsOkappaUnique :: Int
              _rangeIself :: Range
              _declarationsIbindingGroups :: BindingGroups
              _declarationsIkappaUnique :: Int
              _declarationsIself :: Declarations
              _self =
                  Qualifier_Let _rangeIself _declarationsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _declarationsIbindingGroups
              _lhsOkappaUnique =
                  _declarationsIkappaUnique
              _declarationsObindingGroups =
                  _lhsIbindingGroups
              _declarationsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _declarationsIbindingGroups,_declarationsIkappaUnique,_declarationsIself) =
                  declarations_ _declarationsObindingGroups _declarationsOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- Qualifiers --------------------------------------------------
-- cata
sem_Qualifiers :: Qualifiers ->
                  T_Qualifiers
sem_Qualifiers list =
    (Prelude.foldr sem_Qualifiers_Cons sem_Qualifiers_Nil (Prelude.map sem_Qualifier list))
-- semantic domain
type T_Qualifiers = BindingGroups ->
                    Int ->
                    ( BindingGroups,Int,Qualifiers)
sem_Qualifiers_Cons :: T_Qualifier ->
                       T_Qualifiers ->
                       T_Qualifiers
sem_Qualifiers_Cons hd_ tl_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Qualifiers
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _hdObindingGroups :: BindingGroups
              _hdOkappaUnique :: Int
              _tlObindingGroups :: BindingGroups
              _tlOkappaUnique :: Int
              _hdIbindingGroups :: BindingGroups
              _hdIkappaUnique :: Int
              _hdIself :: Qualifier
              _tlIbindingGroups :: BindingGroups
              _tlIkappaUnique :: Int
              _tlIself :: Qualifiers
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _tlIbindingGroups
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdObindingGroups =
                  _lhsIbindingGroups
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlObindingGroups =
                  _hdIbindingGroups
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIbindingGroups,_hdIkappaUnique,_hdIself) =
                  hd_ _hdObindingGroups _hdOkappaUnique
              ( _tlIbindingGroups,_tlIkappaUnique,_tlIself) =
                  tl_ _tlObindingGroups _tlOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Qualifiers_Nil :: T_Qualifiers
sem_Qualifiers_Nil =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Qualifiers
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- Range -------------------------------------------------------
-- cata
sem_Range :: Range ->
             T_Range
sem_Range (Range_Range _start _stop) =
    (sem_Range_Range (sem_Position _start) (sem_Position _stop))
-- semantic domain
type T_Range = ( Range)
sem_Range_Range :: T_Position ->
                   T_Position ->
                   T_Range
sem_Range_Range start_ stop_ =
    (let _lhsOself :: Range
         _startIself :: Position
         _stopIself :: Position
         _self =
             Range_Range _startIself _stopIself
         _lhsOself =
             _self
         ( _startIself) =
             start_
         ( _stopIself) =
             stop_
     in  ( _lhsOself))
-- RecordExpressionBinding -------------------------------------
-- cata
sem_RecordExpressionBinding :: RecordExpressionBinding ->
                               T_RecordExpressionBinding
sem_RecordExpressionBinding (RecordExpressionBinding_RecordExpressionBinding _range _name _expression) =
    (sem_RecordExpressionBinding_RecordExpressionBinding (sem_Range _range) (sem_Name _name) (sem_Expression _expression))
-- semantic domain
type T_RecordExpressionBinding = BindingGroups ->
                                 Int ->
                                 ( BindingGroups,Int,RecordExpressionBinding)
sem_RecordExpressionBinding_RecordExpressionBinding :: T_Range ->
                                                       T_Name ->
                                                       T_Expression ->
                                                       T_RecordExpressionBinding
sem_RecordExpressionBinding_RecordExpressionBinding range_ name_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: RecordExpressionBinding
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _nameIself :: Name
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  RecordExpressionBinding_RecordExpressionBinding _rangeIself _nameIself _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _nameIself) =
                  name_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- RecordExpressionBindings ------------------------------------
-- cata
sem_RecordExpressionBindings :: RecordExpressionBindings ->
                                T_RecordExpressionBindings
sem_RecordExpressionBindings list =
    (Prelude.foldr sem_RecordExpressionBindings_Cons sem_RecordExpressionBindings_Nil (Prelude.map sem_RecordExpressionBinding list))
-- semantic domain
type T_RecordExpressionBindings = BindingGroups ->
                                  Int ->
                                  ( BindingGroups,Int,RecordExpressionBindings)
sem_RecordExpressionBindings_Cons :: T_RecordExpressionBinding ->
                                     T_RecordExpressionBindings ->
                                     T_RecordExpressionBindings
sem_RecordExpressionBindings_Cons hd_ tl_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: RecordExpressionBindings
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _hdObindingGroups :: BindingGroups
              _hdOkappaUnique :: Int
              _tlObindingGroups :: BindingGroups
              _tlOkappaUnique :: Int
              _hdIbindingGroups :: BindingGroups
              _hdIkappaUnique :: Int
              _hdIself :: RecordExpressionBinding
              _tlIbindingGroups :: BindingGroups
              _tlIkappaUnique :: Int
              _tlIself :: RecordExpressionBindings
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _tlIbindingGroups
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdObindingGroups =
                  _lhsIbindingGroups
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlObindingGroups =
                  _hdIbindingGroups
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIbindingGroups,_hdIkappaUnique,_hdIself) =
                  hd_ _hdObindingGroups _hdOkappaUnique
              ( _tlIbindingGroups,_tlIkappaUnique,_tlIself) =
                  tl_ _tlObindingGroups _tlOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_RecordExpressionBindings_Nil :: T_RecordExpressionBindings
sem_RecordExpressionBindings_Nil =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: RecordExpressionBindings
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- RecordPatternBinding ----------------------------------------
-- cata
sem_RecordPatternBinding :: RecordPatternBinding ->
                            T_RecordPatternBinding
sem_RecordPatternBinding (RecordPatternBinding_RecordPatternBinding _range _name _pattern) =
    (sem_RecordPatternBinding_RecordPatternBinding (sem_Range _range) (sem_Name _name) (sem_Pattern _pattern))
-- semantic domain
type T_RecordPatternBinding = ( RecordPatternBinding)
sem_RecordPatternBinding_RecordPatternBinding :: T_Range ->
                                                 T_Name ->
                                                 T_Pattern ->
                                                 T_RecordPatternBinding
sem_RecordPatternBinding_RecordPatternBinding range_ name_ pattern_ =
    (let _lhsOself :: RecordPatternBinding
         _rangeIself :: Range
         _nameIself :: Name
         _patternIself :: Pattern
         _self =
             RecordPatternBinding_RecordPatternBinding _rangeIself _nameIself _patternIself
         _lhsOself =
             _self
         ( _rangeIself) =
             range_
         ( _nameIself) =
             name_
         ( _patternIself) =
             pattern_
     in  ( _lhsOself))
-- RecordPatternBindings ---------------------------------------
-- cata
sem_RecordPatternBindings :: RecordPatternBindings ->
                             T_RecordPatternBindings
sem_RecordPatternBindings list =
    (Prelude.foldr sem_RecordPatternBindings_Cons sem_RecordPatternBindings_Nil (Prelude.map sem_RecordPatternBinding list))
-- semantic domain
type T_RecordPatternBindings = ( RecordPatternBindings)
sem_RecordPatternBindings_Cons :: T_RecordPatternBinding ->
                                  T_RecordPatternBindings ->
                                  T_RecordPatternBindings
sem_RecordPatternBindings_Cons hd_ tl_ =
    (let _lhsOself :: RecordPatternBindings
         _hdIself :: RecordPatternBinding
         _tlIself :: RecordPatternBindings
         _self =
             (:) _hdIself _tlIself
         _lhsOself =
             _self
         ( _hdIself) =
             hd_
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_RecordPatternBindings_Nil :: T_RecordPatternBindings
sem_RecordPatternBindings_Nil =
    (let _lhsOself :: RecordPatternBindings
         _self =
             []
         _lhsOself =
             _self
     in  ( _lhsOself))
-- RightHandSide -----------------------------------------------
-- cata
sem_RightHandSide :: RightHandSide ->
                     T_RightHandSide
sem_RightHandSide (RightHandSide_Expression _range _expression _where) =
    (sem_RightHandSide_Expression (sem_Range _range) (sem_Expression _expression) (sem_MaybeDeclarations _where))
sem_RightHandSide (RightHandSide_Guarded _range _guardedexpressions _where) =
    (sem_RightHandSide_Guarded (sem_Range _range) (sem_GuardedExpressions _guardedexpressions) (sem_MaybeDeclarations _where))
-- semantic domain
type T_RightHandSide = BindingGroups ->
                       Int ->
                       ( BindingGroups,Int,RightHandSide)
sem_RightHandSide_Expression :: T_Range ->
                                T_Expression ->
                                T_MaybeDeclarations ->
                                T_RightHandSide
sem_RightHandSide_Expression range_ expression_ where_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: RightHandSide
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _whereObindingGroups :: BindingGroups
              _whereOkappaUnique :: Int
              _rangeIself :: Range
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _whereIbindingGroups :: BindingGroups
              _whereIkappaUnique :: Int
              _whereIself :: MaybeDeclarations
              _self =
                  RightHandSide_Expression _rangeIself _expressionIself _whereIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _whereIbindingGroups
              _lhsOkappaUnique =
                  _whereIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              _whereObindingGroups =
                  _expressionIbindingGroups
              _whereOkappaUnique =
                  _expressionIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
              ( _whereIbindingGroups,_whereIkappaUnique,_whereIself) =
                  where_ _whereObindingGroups _whereOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_RightHandSide_Guarded :: T_Range ->
                             T_GuardedExpressions ->
                             T_MaybeDeclarations ->
                             T_RightHandSide
sem_RightHandSide_Guarded range_ guardedexpressions_ where_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: RightHandSide
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _guardedexpressionsObindingGroups :: BindingGroups
              _guardedexpressionsOkappaUnique :: Int
              _whereObindingGroups :: BindingGroups
              _whereOkappaUnique :: Int
              _rangeIself :: Range
              _guardedexpressionsIbindingGroups :: BindingGroups
              _guardedexpressionsIkappaUnique :: Int
              _guardedexpressionsIself :: GuardedExpressions
              _whereIbindingGroups :: BindingGroups
              _whereIkappaUnique :: Int
              _whereIself :: MaybeDeclarations
              _self =
                  RightHandSide_Guarded _rangeIself _guardedexpressionsIself _whereIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _whereIbindingGroups
              _lhsOkappaUnique =
                  _whereIkappaUnique
              _guardedexpressionsObindingGroups =
                  _lhsIbindingGroups
              _guardedexpressionsOkappaUnique =
                  _lhsIkappaUnique
              _whereObindingGroups =
                  _guardedexpressionsIbindingGroups
              _whereOkappaUnique =
                  _guardedexpressionsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _guardedexpressionsIbindingGroups,_guardedexpressionsIkappaUnique,_guardedexpressionsIself) =
                  guardedexpressions_ _guardedexpressionsObindingGroups _guardedexpressionsOkappaUnique
              ( _whereIbindingGroups,_whereIkappaUnique,_whereIself) =
                  where_ _whereObindingGroups _whereOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- SimpleType --------------------------------------------------
-- cata
sem_SimpleType :: SimpleType ->
                  T_SimpleType
sem_SimpleType (SimpleType_SimpleType _range _name _typevariables) =
    (sem_SimpleType_SimpleType (sem_Range _range) (sem_Name _name) (sem_Names _typevariables))
-- semantic domain
type T_SimpleType = KindConstraints ->
                    Kind ->
                    Int ->
                    ( KindConstraints,PatternAssumptions,PatternAssumptions,Int,SimpleType)
sem_SimpleType_SimpleType :: T_Range ->
                             T_Name ->
                             T_Names ->
                             T_SimpleType
sem_SimpleType_SimpleType range_ name_ typevariables_ =
    (\ _lhsIconstraints
       _lhsIkappaOfRHS
       _lhsIkappaUnique ->
         (let _lhsOenvironment :: PatternAssumptions
              _lhsOdeclared :: PatternAssumptions
              _lhsOconstraints :: KindConstraints
              _lhsOkappaUnique :: Int
              _lhsOself :: SimpleType
              _rangeIself :: Range
              _nameIself :: Name
              _typevariablesIself :: Names
              _lhsOenvironment =
                  M.fromList (zip _typevariablesIself _kappasVars)
              _lhsOdeclared =
                  M.singleton _nameIself _kappaCon
              _lhsOconstraints =
                  _newConstraint : _lhsIconstraints
              _lhsOkappaUnique =
                  1 + length _typevariablesIself + _lhsIkappaUnique
              _kappaCon =
                  TVar _lhsIkappaUnique
              _kappasVars =
                  take (length _typevariablesIself) [ TVar i | i <- [ _lhsIkappaUnique+1 .. ]]
              _newConstraint =
                  (_kappaCon .==. foldr (.->.) _lhsIkappaOfRHS _kappasVars) (unexpected "SimpleType.SimpleType")
              _self =
                  SimpleType_SimpleType _rangeIself _nameIself _typevariablesIself
              _lhsOself =
                  _self
              ( _rangeIself) =
                  range_
              ( _nameIself) =
                  name_
              ( _typevariablesIself) =
                  typevariables_
          in  ( _lhsOconstraints,_lhsOdeclared,_lhsOenvironment,_lhsOkappaUnique,_lhsOself)))
-- Statement ---------------------------------------------------
-- cata
sem_Statement :: Statement ->
                 T_Statement
sem_Statement (Statement_Empty _range) =
    (sem_Statement_Empty (sem_Range _range))
sem_Statement (Statement_Expression _range _expression) =
    (sem_Statement_Expression (sem_Range _range) (sem_Expression _expression))
sem_Statement (Statement_Generator _range _pattern _expression) =
    (sem_Statement_Generator (sem_Range _range) (sem_Pattern _pattern) (sem_Expression _expression))
sem_Statement (Statement_Let _range _declarations) =
    (sem_Statement_Let (sem_Range _range) (sem_Declarations _declarations))
-- semantic domain
type T_Statement = BindingGroups ->
                   Int ->
                   ( BindingGroups,Int,Statement)
sem_Statement_Empty :: T_Range ->
                       T_Statement
sem_Statement_Empty range_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Statement
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _rangeIself :: Range
              _self =
                  Statement_Empty _rangeIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Statement_Expression :: T_Range ->
                            T_Expression ->
                            T_Statement
sem_Statement_Expression range_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Statement
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  Statement_Expression _rangeIself _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Statement_Generator :: T_Range ->
                           T_Pattern ->
                           T_Expression ->
                           T_Statement
sem_Statement_Generator range_ pattern_ expression_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Statement
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _expressionObindingGroups :: BindingGroups
              _expressionOkappaUnique :: Int
              _rangeIself :: Range
              _patternIself :: Pattern
              _expressionIbindingGroups :: BindingGroups
              _expressionIkappaUnique :: Int
              _expressionIself :: Expression
              _self =
                  Statement_Generator _rangeIself _patternIself _expressionIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _expressionIbindingGroups
              _lhsOkappaUnique =
                  _expressionIkappaUnique
              _expressionObindingGroups =
                  _lhsIbindingGroups
              _expressionOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _patternIself) =
                  pattern_
              ( _expressionIbindingGroups,_expressionIkappaUnique,_expressionIself) =
                  expression_ _expressionObindingGroups _expressionOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Statement_Let :: T_Range ->
                     T_Declarations ->
                     T_Statement
sem_Statement_Let range_ declarations_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Statement
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _declarationsObindingGroups :: BindingGroups
              _declarationsOkappaUnique :: Int
              _rangeIself :: Range
              _declarationsIbindingGroups :: BindingGroups
              _declarationsIkappaUnique :: Int
              _declarationsIself :: Declarations
              _self =
                  Statement_Let _rangeIself _declarationsIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _declarationsIbindingGroups
              _lhsOkappaUnique =
                  _declarationsIkappaUnique
              _declarationsObindingGroups =
                  _lhsIbindingGroups
              _declarationsOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _declarationsIbindingGroups,_declarationsIkappaUnique,_declarationsIself) =
                  declarations_ _declarationsObindingGroups _declarationsOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- Statements --------------------------------------------------
-- cata
sem_Statements :: Statements ->
                  T_Statements
sem_Statements list =
    (Prelude.foldr sem_Statements_Cons sem_Statements_Nil (Prelude.map sem_Statement list))
-- semantic domain
type T_Statements = BindingGroups ->
                    Int ->
                    ( BindingGroups,Int,Statements)
sem_Statements_Cons :: T_Statement ->
                       T_Statements ->
                       T_Statements
sem_Statements_Cons hd_ tl_ =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Statements
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _hdObindingGroups :: BindingGroups
              _hdOkappaUnique :: Int
              _tlObindingGroups :: BindingGroups
              _tlOkappaUnique :: Int
              _hdIbindingGroups :: BindingGroups
              _hdIkappaUnique :: Int
              _hdIself :: Statement
              _tlIbindingGroups :: BindingGroups
              _tlIkappaUnique :: Int
              _tlIself :: Statements
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _tlIbindingGroups
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdObindingGroups =
                  _lhsIbindingGroups
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlObindingGroups =
                  _hdIbindingGroups
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIbindingGroups,_hdIkappaUnique,_hdIself) =
                  hd_ _hdObindingGroups _hdOkappaUnique
              ( _tlIbindingGroups,_tlIkappaUnique,_tlIself) =
                  tl_ _tlObindingGroups _tlOkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
sem_Statements_Nil :: T_Statements
sem_Statements_Nil =
    (\ _lhsIbindingGroups
       _lhsIkappaUnique ->
         (let _lhsOself :: Statements
              _lhsObindingGroups :: BindingGroups
              _lhsOkappaUnique :: Int
              _self =
                  []
              _lhsOself =
                  _self
              _lhsObindingGroups =
                  _lhsIbindingGroups
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsObindingGroups,_lhsOkappaUnique,_lhsOself)))
-- Strings -----------------------------------------------------
-- cata
sem_Strings :: Strings ->
               T_Strings
sem_Strings list =
    (Prelude.foldr sem_Strings_Cons sem_Strings_Nil list)
-- semantic domain
type T_Strings = ( Strings)
sem_Strings_Cons :: String ->
                    T_Strings ->
                    T_Strings
sem_Strings_Cons hd_ tl_ =
    (let _lhsOself :: Strings
         _tlIself :: Strings
         _self =
             (:) hd_ _tlIself
         _lhsOself =
             _self
         ( _tlIself) =
             tl_
     in  ( _lhsOself))
sem_Strings_Nil :: T_Strings
sem_Strings_Nil =
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
sem_Type (Type_Application _range _prefix _function _arguments) =
    (sem_Type_Application (sem_Range _range) _prefix (sem_Type _function) (sem_Types _arguments))
sem_Type (Type_Constructor _range _name) =
    (sem_Type_Constructor (sem_Range _range) (sem_Name _name))
sem_Type (Type_Exists _range _typevariables _type) =
    (sem_Type_Exists (sem_Range _range) (sem_Names _typevariables) (sem_Type _type))
sem_Type (Type_Forall _range _typevariables _type) =
    (sem_Type_Forall (sem_Range _range) (sem_Names _typevariables) (sem_Type _type))
sem_Type (Type_Parenthesized _range _type) =
    (sem_Type_Parenthesized (sem_Range _range) (sem_Type _type))
sem_Type (Type_Qualified _range _context _type) =
    (sem_Type_Qualified (sem_Range _range) (sem_ContextItems _context) (sem_Type _type))
sem_Type (Type_Variable _range _name) =
    (sem_Type_Variable (sem_Range _range) (sem_Name _name))
-- semantic domain
type T_Type = KindConstraints ->
              Int ->
              ( Assumptions,KindConstraints,Kind,Int,Type)
sem_Type_Application :: T_Range ->
                        Bool ->
                        T_Type ->
                        T_Types ->
                        T_Type
sem_Type_Application range_ prefix_ function_ arguments_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOconstraints :: KindConstraints
              _lhsOkappaUnique :: Int
              _lhsOself :: Type
              _lhsOkappa :: Kind
              _functionOconstraints :: KindConstraints
              _functionOkappaUnique :: Int
              _argumentsOconstraints :: KindConstraints
              _argumentsOkappaUnique :: Int
              _rangeIself :: Range
              _functionIassumptions :: Assumptions
              _functionIconstraints :: KindConstraints
              _functionIkappa :: Kind
              _functionIkappaUnique :: Int
              _functionIself :: Type
              _argumentsIassumptions :: Assumptions
              _argumentsIconstraints :: KindConstraints
              _argumentsIkappaUnique :: Int
              _argumentsIkappas :: Kinds
              _argumentsIself :: Types
              _lhsOassumptions =
                  _functionIassumptions `combine` _argumentsIassumptions
              _lhsOconstraints =
                  _argumentsIconstraints ++ [_newConstraint]
              _lhsOkappaUnique =
                  _argumentsIkappaUnique + 1
              _kappa =
                  TVar _argumentsIkappaUnique
              _newConstraint =
                  (_functionIkappa <==> foldr (.->.) _kappa _argumentsIkappas) (kindApplication _rangeIself _self _functionIself)
              _self =
                  Type_Application _rangeIself prefix_ _functionIself _argumentsIself
              _lhsOself =
                  _self
              _lhsOkappa =
                  _kappa
              _functionOconstraints =
                  _lhsIconstraints
              _functionOkappaUnique =
                  _lhsIkappaUnique
              _argumentsOconstraints =
                  _functionIconstraints
              _argumentsOkappaUnique =
                  _functionIkappaUnique
              ( _rangeIself) =
                  range_
              ( _functionIassumptions,_functionIconstraints,_functionIkappa,_functionIkappaUnique,_functionIself) =
                  function_ _functionOconstraints _functionOkappaUnique
              ( _argumentsIassumptions,_argumentsIconstraints,_argumentsIkappaUnique,_argumentsIkappas,_argumentsIself) =
                  arguments_ _argumentsOconstraints _argumentsOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappa,_lhsOkappaUnique,_lhsOself)))
sem_Type_Constructor :: T_Range ->
                        T_Name ->
                        T_Type
sem_Type_Constructor range_ name_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOkappaUnique :: Int
              _lhsOself :: Type
              _lhsOconstraints :: KindConstraints
              _lhsOkappa :: Kind
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOassumptions =
                  single _nameIself _kappa
              _lhsOkappaUnique =
                  _lhsIkappaUnique + 1
              _kappa =
                  TVar _lhsIkappaUnique
              _self =
                  Type_Constructor _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsOconstraints =
                  _lhsIconstraints
              _lhsOkappa =
                  _kappa
              ( _rangeIself) =
                  range_
              ( _nameIself) =
                  name_
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappa,_lhsOkappaUnique,_lhsOself)))
sem_Type_Exists :: T_Range ->
                   T_Names ->
                   T_Type ->
                   T_Type
sem_Type_Exists range_ typevariables_ type_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOself :: Type
              _lhsOassumptions :: Assumptions
              _lhsOconstraints :: KindConstraints
              _lhsOkappa :: Kind
              _lhsOkappaUnique :: Int
              _typeOconstraints :: KindConstraints
              _typeOkappaUnique :: Int
              _rangeIself :: Range
              _typevariablesIself :: Names
              _typeIassumptions :: Assumptions
              _typeIconstraints :: KindConstraints
              _typeIkappa :: Kind
              _typeIkappaUnique :: Int
              _typeIself :: Type
              (_assumptions,_kappa) =
                  internalError "KindInferencing.ag" "n/a" "Existential types are not supported"
              _self =
                  Type_Exists _rangeIself _typevariablesIself _typeIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _assumptions
              _lhsOconstraints =
                  _typeIconstraints
              _lhsOkappa =
                  _kappa
              _lhsOkappaUnique =
                  _typeIkappaUnique
              _typeOconstraints =
                  _lhsIconstraints
              _typeOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _typevariablesIself) =
                  typevariables_
              ( _typeIassumptions,_typeIconstraints,_typeIkappa,_typeIkappaUnique,_typeIself) =
                  type_ _typeOconstraints _typeOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappa,_lhsOkappaUnique,_lhsOself)))
sem_Type_Forall :: T_Range ->
                   T_Names ->
                   T_Type ->
                   T_Type
sem_Type_Forall range_ typevariables_ type_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOself :: Type
              _lhsOassumptions :: Assumptions
              _lhsOconstraints :: KindConstraints
              _lhsOkappa :: Kind
              _lhsOkappaUnique :: Int
              _typeOconstraints :: KindConstraints
              _typeOkappaUnique :: Int
              _rangeIself :: Range
              _typevariablesIself :: Names
              _typeIassumptions :: Assumptions
              _typeIconstraints :: KindConstraints
              _typeIkappa :: Kind
              _typeIkappaUnique :: Int
              _typeIself :: Type
              (_assumptions,_kappa) =
                  internalError "KindInferencing.ag" "n/a" "Universal types are not supported"
              _self =
                  Type_Forall _rangeIself _typevariablesIself _typeIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _assumptions
              _lhsOconstraints =
                  _typeIconstraints
              _lhsOkappa =
                  _kappa
              _lhsOkappaUnique =
                  _typeIkappaUnique
              _typeOconstraints =
                  _lhsIconstraints
              _typeOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _typevariablesIself) =
                  typevariables_
              ( _typeIassumptions,_typeIconstraints,_typeIkappa,_typeIkappaUnique,_typeIself) =
                  type_ _typeOconstraints _typeOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappa,_lhsOkappaUnique,_lhsOself)))
sem_Type_Parenthesized :: T_Range ->
                          T_Type ->
                          T_Type
sem_Type_Parenthesized range_ type_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOself :: Type
              _lhsOassumptions :: Assumptions
              _lhsOconstraints :: KindConstraints
              _lhsOkappa :: Kind
              _lhsOkappaUnique :: Int
              _typeOconstraints :: KindConstraints
              _typeOkappaUnique :: Int
              _rangeIself :: Range
              _typeIassumptions :: Assumptions
              _typeIconstraints :: KindConstraints
              _typeIkappa :: Kind
              _typeIkappaUnique :: Int
              _typeIself :: Type
              _self =
                  Type_Parenthesized _rangeIself _typeIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _typeIassumptions
              _lhsOconstraints =
                  _typeIconstraints
              _lhsOkappa =
                  _typeIkappa
              _lhsOkappaUnique =
                  _typeIkappaUnique
              _typeOconstraints =
                  _lhsIconstraints
              _typeOkappaUnique =
                  _lhsIkappaUnique
              ( _rangeIself) =
                  range_
              ( _typeIassumptions,_typeIconstraints,_typeIkappa,_typeIkappaUnique,_typeIself) =
                  type_ _typeOconstraints _typeOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappa,_lhsOkappaUnique,_lhsOself)))
sem_Type_Qualified :: T_Range ->
                      T_ContextItems ->
                      T_Type ->
                      T_Type
sem_Type_Qualified range_ context_ type_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOself :: Type
              _lhsOassumptions :: Assumptions
              _lhsOconstraints :: KindConstraints
              _lhsOkappa :: Kind
              _lhsOkappaUnique :: Int
              _contextOkappaUnique :: Int
              _typeOconstraints :: KindConstraints
              _typeOkappaUnique :: Int
              _rangeIself :: Range
              _contextIkappaUnique :: Int
              _contextIself :: ContextItems
              _typeIassumptions :: Assumptions
              _typeIconstraints :: KindConstraints
              _typeIkappa :: Kind
              _typeIkappaUnique :: Int
              _typeIself :: Type
              (_assumptions,_kappa) =
                  internalError "KindInferencing.ag" "n/a" "Qualified types are not supported"
              _self =
                  Type_Qualified _rangeIself _contextIself _typeIself
              _lhsOself =
                  _self
              _lhsOassumptions =
                  _assumptions
              _lhsOconstraints =
                  _typeIconstraints
              _lhsOkappa =
                  _kappa
              _lhsOkappaUnique =
                  _typeIkappaUnique
              _contextOkappaUnique =
                  _lhsIkappaUnique
              _typeOconstraints =
                  _lhsIconstraints
              _typeOkappaUnique =
                  _contextIkappaUnique
              ( _rangeIself) =
                  range_
              ( _contextIkappaUnique,_contextIself) =
                  context_ _contextOkappaUnique
              ( _typeIassumptions,_typeIconstraints,_typeIkappa,_typeIkappaUnique,_typeIself) =
                  type_ _typeOconstraints _typeOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappa,_lhsOkappaUnique,_lhsOself)))
sem_Type_Variable :: T_Range ->
                     T_Name ->
                     T_Type
sem_Type_Variable range_ name_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOkappaUnique :: Int
              _lhsOself :: Type
              _lhsOconstraints :: KindConstraints
              _lhsOkappa :: Kind
              _rangeIself :: Range
              _nameIself :: Name
              _lhsOassumptions =
                  single _nameIself _kappa
              _lhsOkappaUnique =
                  _lhsIkappaUnique + 1
              _kappa =
                  TVar _lhsIkappaUnique
              _self =
                  Type_Variable _rangeIself _nameIself
              _lhsOself =
                  _self
              _lhsOconstraints =
                  _lhsIconstraints
              _lhsOkappa =
                  _kappa
              ( _rangeIself) =
                  range_
              ( _nameIself) =
                  name_
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappa,_lhsOkappaUnique,_lhsOself)))
-- Types -------------------------------------------------------
-- cata
sem_Types :: Types ->
             T_Types
sem_Types list =
    (Prelude.foldr sem_Types_Cons sem_Types_Nil (Prelude.map sem_Type list))
-- semantic domain
type T_Types = KindConstraints ->
               Int ->
               ( Assumptions,KindConstraints,Int,Kinds,Types)
sem_Types_Cons :: T_Type ->
                  T_Types ->
                  T_Types
sem_Types_Cons hd_ tl_ =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOkappas :: Kinds
              _lhsOself :: Types
              _lhsOconstraints :: KindConstraints
              _lhsOkappaUnique :: Int
              _hdOconstraints :: KindConstraints
              _hdOkappaUnique :: Int
              _tlOconstraints :: KindConstraints
              _tlOkappaUnique :: Int
              _hdIassumptions :: Assumptions
              _hdIconstraints :: KindConstraints
              _hdIkappa :: Kind
              _hdIkappaUnique :: Int
              _hdIself :: Type
              _tlIassumptions :: Assumptions
              _tlIconstraints :: KindConstraints
              _tlIkappaUnique :: Int
              _tlIkappas :: Kinds
              _tlIself :: Types
              _lhsOassumptions =
                  _hdIassumptions `combine` _tlIassumptions
              _lhsOkappas =
                  _hdIkappa : _tlIkappas
              _self =
                  (:) _hdIself _tlIself
              _lhsOself =
                  _self
              _lhsOconstraints =
                  _tlIconstraints
              _lhsOkappaUnique =
                  _tlIkappaUnique
              _hdOconstraints =
                  _lhsIconstraints
              _hdOkappaUnique =
                  _lhsIkappaUnique
              _tlOconstraints =
                  _hdIconstraints
              _tlOkappaUnique =
                  _hdIkappaUnique
              ( _hdIassumptions,_hdIconstraints,_hdIkappa,_hdIkappaUnique,_hdIself) =
                  hd_ _hdOconstraints _hdOkappaUnique
              ( _tlIassumptions,_tlIconstraints,_tlIkappaUnique,_tlIkappas,_tlIself) =
                  tl_ _tlOconstraints _tlOkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappaUnique,_lhsOkappas,_lhsOself)))
sem_Types_Nil :: T_Types
sem_Types_Nil =
    (\ _lhsIconstraints
       _lhsIkappaUnique ->
         (let _lhsOassumptions :: Assumptions
              _lhsOkappas :: Kinds
              _lhsOself :: Types
              _lhsOconstraints :: KindConstraints
              _lhsOkappaUnique :: Int
              _lhsOassumptions =
                  noAssumptions
              _lhsOkappas =
                  []
              _self =
                  []
              _lhsOself =
                  _self
              _lhsOconstraints =
                  _lhsIconstraints
              _lhsOkappaUnique =
                  _lhsIkappaUnique
          in  ( _lhsOassumptions,_lhsOconstraints,_lhsOkappaUnique,_lhsOkappas,_lhsOself)))