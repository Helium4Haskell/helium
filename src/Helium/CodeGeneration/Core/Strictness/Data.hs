module Helium.CodeGeneration.Core.Strictness.Data where

import qualified Data.Set as S

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Module
import Lvm.Core.Type

-- Keys are annotation variables, values are the equality/join/meet
type AnnotationEnvironment = IdMap SAnn

-- Constraint set, l < r
type Constraints = S.Set Constraint
data Constraint = Constraint SAnn SAnn deriving (Eq, Ord, Show)
type SolvedConstraints = IdMap SAnn

-- Join and meet
join, meet :: SAnn -> SAnn -> SAnn
join L _ = L
join _ L = L
join S x = x
join x S = x
join l r | l == r    = l
         | otherwise = Join l r

meet S _ = S
meet _ S = S
meet L x = x
meet x L = x
meet l r | l == r    = l
         | otherwise = Meet l r

isAnn :: SAnn -> Bool
isAnn (AnnVar _) = True
isAnn _          = False

fromAnn :: SAnn -> Id
fromAnn (AnnVar x) = x
fromAnn _          = error "fromAnn"

isCustomAnn :: Custom -> Bool
isCustomAnn (CustomDecl (DeclKindCustom n) _) = stringFromId n == "strictness"
isCustomAnn  _ = False

fromCustomAnn :: Custom -> Type
fromCustomAnn (CustomDecl (DeclKindCustom _) [CustomType t]) = t

annEnvToConstraints :: AnnotationEnvironment -> Constraints
annEnvToConstraints = S.fromList . map snd . listFromMap . mapMapWithId (\x y -> Constraint y (AnnVar x))

-- Get all variables in an annotation or type
getVariablesAnn :: SAnn -> [Id]
getVariablesAnn (AnnVar x) = [x]
getVariablesAnn (Join x y) = getVariablesAnn x ++ getVariablesAnn y
getVariablesAnn (Meet x y) = getVariablesAnn x ++ getVariablesAnn y
getVariablesAnn _          = []

typeRemoveStrictnessQuantification :: Type -> Type
typeRemoveStrictnessQuantification (TForall _ KAnn t) = typeRemoveStrictnessQuantification t
typeRemoveStrictnessQuantification (TForall q k t) = TForall q k $ typeRemoveStrictnessQuantification t
typeRemoveStrictnessQuantification (TStrict t) = TStrict $ typeRemoveStrictnessQuantification t
typeRemoveStrictnessQuantification (TAp t1 t2) = TAp (typeRemoveStrictnessQuantification t1) (typeRemoveStrictnessQuantification t2)
typeRemoveStrictnessQuantification t = t

typeRemoveAnnotations :: Type -> Type
typeRemoveAnnotations (TAp (TAnn _) t1) = typeRemoveAnnotations t1
typeRemoveAnnotations (TAp t1 t2) = TAp (typeRemoveAnnotations t1) (typeRemoveAnnotations t2)
typeRemoveAnnotations (TForall _ KAnn t) = typeRemoveAnnotations t
typeRemoveAnnotations (TForall q k t) = TForall q k $ typeRemoveAnnotations t
typeRemoveAnnotations (TStrict t) = TStrict $ typeRemoveAnnotations t
typeRemoveAnnotations (TAnn a) = error $ "Annotation " ++ show a ++ " occurs outside application"
typeRemoveAnnotations t = t

typeNotAnnotated :: Type -> Type
typeNotAnnotated (TAp (TAnn _) t) = typeNotAnnotated t
typeNotAnnotated t = t

substitueAnn :: SAnn -> String -> SAnn -> SAnn
substitueAnn (AnnVar x) id a | stringFromId x == id = a
substitueAnn (Join x y) id a = join (substitueAnn x id a) (substitueAnn y id a)
substitueAnn (Meet x y) id a = meet (substitueAnn x id a) (substitueAnn y id a)
substitueAnn ann        _  _ = ann
      