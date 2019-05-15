module Helium.CodeGeneration.Iridium.Region.Annotation where

import qualified Data.IntMap as IntMap
import Data.List
import qualified Data.Graph as Graph

import Lvm.Core.Type
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Relation

newtype AnnotationVar = AnnotationVar Int
  deriving (Eq, Ord)

instance Show AnnotationVar where
  show (AnnotationVar idx) = 'ψ' : showSubscript idx

data Parameter var a
  = ParameterMonomorphic !var !a
  | ParameterPolymorphic !var !TypeVar ![Type]
  | ParameterList ![Parameter var a]

parameterNames :: Parameter var a -> [var]
parameterNames (ParameterMonomorphic var _) = [var]
parameterNames (ParameterPolymorphic var _ _) = [var]
parameterNames (ParameterList params) = params >>= parameterNames

instance (Show var, Show a) => Show (Parameter var a) where
  show (ParameterMonomorphic r1 a) = show r1 ++ ": " ++ show a
  show (ParameterPolymorphic r1 tvar tps) = show r1 ++ "<" ++ show tvar ++ (tps >>= (\tp -> " " ++ showType [] tp)) ++ ">"
  show (ParameterList params) = show params

  showList params = ('(' :) . (intercalate ", " (map show params) ++) . (')' :)

data Argument a
  = ArgumentValue !a
  | ArgumentList ![Argument a]

argumentFlatten :: Argument a -> [a]
argumentFlatten (ArgumentValue a) = [a]
argumentFlatten (ArgumentList args) = args >>= argumentFlatten

instance (Show a) => Show (Argument a) where
  show (ArgumentValue r1) = show r1
  show (ArgumentList args) = show args

  showList args = ('(' :) . (intercalate ", " (map show args) ++) . (')' :)

instance Functor Argument where
  fmap f (ArgumentValue a) = ArgumentValue $ f a
  fmap f (ArgumentList args) = ArgumentList $ fmap (fmap f) args

data Annotation
  = AForall !TypeVar !Annotation
  | ALam !(Parameter AnnotationVar Sort) !(Parameter RegionVar SortArgumentRegion) !Annotation

  | AApp !Annotation !(Argument Annotation) !(Argument RegionVar)

  -- Leaf
  | AVar !AnnotationVar
  | AThunk !RegionVar ![RegionVar] -- Arguments must be monomorphic
  | ARelation ![RelationConstraint]
  | ABottom

  | AJoin !Annotation !Annotation

instance Show Annotation where
  show (AForall tvar annotation) = "forall " ++ show tvar ++ ". " ++ show annotation
  show (ALam annotationParams regionParams annotation) = "λ[" ++ show annotationParams ++ "; " ++ show regionParams ++ "] -> " ++ show annotation
  show annotation = showAnnotationJoin annotation

showAnnotationJoin :: Annotation -> String
showAnnotationJoin (AJoin a1 a2) = showAnnotationJoin a1 ++ " ⊔ " ++ showAnnotationJoin a2
showAnnotationJoin annotation = showAnnotationApp annotation

showAnnotationApp :: Annotation -> String
showAnnotationApp (AApp annotation annotationArgs regionArgs) =
  showAnnotationApp annotation ++ " " ++ show annotationArgs ++ " " ++ show regionArgs
showAnnotationApp (AThunk r1 rs) = "ψ_thunk " ++ show r1 ++ " " ++ show rs
showAnnotationApp annotation = showAnnotationLow annotation

showAnnotationLow :: Annotation -> String
showAnnotationLow (AVar var) = show var
showAnnotationLow (ARelation rel) = show rel
showAnnotationLow ABottom = "⊥"

annotationExpandBottom :: Sort -> Annotation
annotationExpandBottom (SortForall tvar sort) = AForall tvar $ annotationExpandBottom sort
annotationExpandBottom (SortFun annotationArgs regionArgs sort) = ALam
  (snd $ sortArgumentToParameter (map AnnotationVar [0..]) annotationArgs)
  (snd $ sortArgumentToParameter (map RegionVar [0..]) regionArgs)
  $ annotationExpandBottom sort
annotationExpandBottom SortRelation = ARelation []

sortArgumentToParameter :: [var] -> SortArgument a -> ([var], Parameter var a)
sortArgumentToParameter (freshVar:freshVars) (SortArgumentMonomorphic a) = (freshVars, ParameterMonomorphic freshVar a)
sortArgumentToParameter (freshVar:freshVars) (SortArgumentPolymorphic tvar tps) = (freshVars, ParameterPolymorphic freshVar tvar tps)
sortArgumentToParameter freshVars (SortArgumentList args) = (freshVars', ParameterList params)
  where
    (freshVars', params) = mapAccumL sortArgumentToParameter freshVars args

parameterToArgument :: Parameter var a -> Argument var
parameterToArgument (ParameterMonomorphic var _) = ArgumentValue var
parameterToArgument (ParameterPolymorphic var _ _ ) = ArgumentValue var
parameterToArgument (ParameterList params) = ArgumentList $ map parameterToArgument params

zipFlattenArgument :: (a -> b -> c) -> Argument a -> Argument b -> [c]
zipFlattenArgument f argLeft argRight = zipFlattenArgument' argLeft argRight []
  where
    zipFlattenArgument' (ArgumentValue a) (ArgumentValue b) accum = f a b : accum
    zipFlattenArgument' (ArgumentList as) (ArgumentList bs) accum = foldr (\(a, b) -> zipFlattenArgument' a b) accum $ zip as bs
    zipFlattenArgument' _ _ accum = error "zipFlattenArgument: Arguments do not have the same kind"
