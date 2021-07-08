module Helium.CodeGeneration.Core.Strictness.Data where

import qualified Data.Set as S

import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

import Text.PrettyPrint.Leijen (pretty)

type BindMap = IdMap SAnn
type PolyMap = IdMap (Expr, Type)
type MonoMap = IdMap Type

-- Keys are annotation variables, values are the equality/join/meet
type AnnotationEnvironment = IdMap SAnn

-- Annotation variables per local definition by let or lambda
type RelevanceEnvironment       = IdMap SAnn
type ApplicativenessEnvironment = IdMap SAnn

-- Constraint set, l < r
type Constraints = S.Set Constraint
data Constraint = Constraint SAnn SAnn deriving (Eq, Ord, Show)
type SolvedConstraints = IdMap SAnn

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
fromCustomAnn (CustomDecl (DeclKindCustom n) [CustomType t]) | stringFromId n == "strictness" = t
fromCustomAnn c = error $ "Expected strictness annotations, got: " ++ show (pretty c)

typeFromCustom :: [Custom] -> Type
typeFromCustom [] = error "Strictness type not found"
typeFromCustom (CustomDecl (DeclKindCustom n) [CustomType t]:_) | stringFromId n == "strictness" = t
typeFromCustom (_:xs) = typeFromCustom xs

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

isTupAp :: Expr -> Bool
isTupAp (Con (ConTuple _)) = True
isTupAp (Ap e _) = isTupAp e
isTupAp (ApType e _) = isTupAp e
isTupAp _ = False

isTup :: Type -> Bool
isTup (TAp t1 _) = isTup t1
isTup (TCon (TConTuple _)) = True
isTup _ = False

threeIds :: NameSupply -> (Id, Id, Id, NameSupply)
threeIds supply0 = (id1, id2, id3, supply3)
  where
    (id1, supply1) = freshId supply0
    (id2, supply2) = freshId supply1
    (id3, supply3) = freshId supply2

blockedConstraint :: IdSet -> Constraint -> Bool
blockedConstraint is (_ `Constraint` AnnVar x) = elemSet x is
blockedConstraint _ _                          = True

mapConstraint :: SolvedConstraints -> Constraint -> Constraint
mapConstraint sc (a1 `Constraint` a2) = a1 `Constraint` replaceVar sc a2

getForalls :: TypeEnvironment -> Type -> [Bool]
getForalls env (TForall _ KAnn t) = True : getForalls env t
getForalls env (TForall _ _ t) = getForalls env t
getForalls env (TStrict t) = getForalls env t
getForalls env (TAp t1 t2) = getForalls env t1 ++ getForalls env t2
getForalls env t | t' == t = []
                 | otherwise = getForalls env t'
                where
                    t' = typeNormalizeHead env t

-- Replace solved annotation variables
replaceVar :: SolvedConstraints -> SAnn -> SAnn
replaceVar sc (AnnVar x) | elemMap x sc = findMap x sc
replaceVar sc (Meet x y) = meet (replaceVar sc x) (replaceVar sc y)
replaceVar sc (Join x y) = join (replaceVar sc x) (replaceVar sc y)
replaceVar _  x          = x

setStrictnessType :: CoreDecl -> CoreDecl
setStrictnessType decl = decl{declType = t}
  where
    t = typeFromCustom $ declCustoms decl

strictnessToCustom :: Type -> [Custom] -> [Custom]
strictnessToCustom t c = CustomDecl (DeclKindCustom (idFromString "strictness")) [CustomType t] : c

-- Lookup annotation of variables
lookupVar :: SAnn -> SolvedConstraints -> SAnn
lookupVar (AnnVar x) sc | elemMap x sc = findMap x sc
lookupVar (Join x y) sc = join (lookupVar x sc) (lookupVar y sc)
lookupVar (Meet x y) sc = meet (lookupVar x sc) (lookupVar y sc)
lookupVar x _ = x

uncontain :: [Id] -> SAnn -> SAnn
uncontain xs (AnnVar x) | x `elem` xs = S
uncontain xs (Join x y) = join (uncontain xs x) (uncontain xs y)
uncontain xs (Meet x y) = meet (uncontain xs x) (uncontain xs y)
uncontain _  x          = x

setValue :: (Type -> Type) -> PolyMap -> CoreDecl -> CoreDecl
setValue _ vs decl@DeclValue{}
    | elemMap (declName decl) vs = decl{valueValue = e, declCustoms = c}
    where
        (e, t) = findMap (declName decl) vs
        c = strictnessToCustom t (declCustoms decl)
setValue f _ decl
  | isUpdate decl = decl{declCustoms = c}
  | otherwise     = decl
    where
      c = strictnessToCustom (f $ declType decl) (declCustoms decl)

isUpdate :: CoreDecl -> Bool
isUpdate decl@DeclAbstract{} = not $ any isCustomAnn (declCustoms decl)
isUpdate decl@DeclCon{} = not $ any isCustomAnn (declCustoms decl)
isUpdate _ = False

normalTypeOfCoreExpression :: TypeEnvironment -> Expr -> Type
normalTypeOfCoreExpression env e = typeNormalizeHead env $ typeOfCoreExpression env e 

analyseAnn :: SAnn -> SAnn -> AnnotationEnvironment
analyseAnn (AnnVar x) y = singleMap x y
analyseAnn x (AnnVar y) = singleMap y x
analyseAnn _ _ = emptyMap
