module Helium.CodeGeneration.Core.Strictness.Data where

import Data.List
import qualified Data.Set as S

import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

import Text.PrettyPrint.Leijen (pretty)

-- Keys are annotation variables, values are the equality/join/meet
type AnnotationEnvironment = IdMap SAnn

-- Annotation variables per local definition by let or lambda
type RelevanceEnvironment       = IdMap SAnn
type ApplicativenessEnvironment = IdMap SAnn

-- Complete environment with type and annotation environment
data Environment = Environment { typeEnv :: TypeEnvironment,
                                 relEnv  :: RelevanceEnvironment,
                                 appEnv  :: ApplicativenessEnvironment,
                                 vars    :: IdSet}

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

-- Helper functions to add variables to both type and annotation environment
envAddVariable :: Variable -> Environment -> Environment
envAddVariable var env = env{typeEnv = typeEnv', relEnv = relEnv', appEnv = appEnv'}
  where
    typeEnv' = typeEnvAddVariable var $ typeEnv env
    relEnv'  = relEnvAddVariable  var $ relEnv env
    appEnv'  = appEnvAddVariable  var $ appEnv env

envAddVariables :: [Variable] -> Environment -> Environment
envAddVariables vars env = foldr envAddVariable env vars

envAddBind :: Bind -> Environment -> Environment
envAddBind (Bind var _) = envAddVariable var

envAddBinds :: Binds -> Environment -> Environment
envAddBinds (Strict bind) env = envAddBind bind env
envAddBinds (NonRec bind) env = envAddBind bind env
envAddBinds (Rec binds) env = foldr envAddBind env binds

envAddPattern :: Pat -> Environment -> Environment
envAddPattern p env = envAddVariables x env
  where
    x = patternVariables (typeEnv env) p

relEnvAddVariable :: Variable -> RelevanceEnvironment -> RelevanceEnvironment
relEnvAddVariable (Variable x (TAp (TAnn _) (TAp (TAnn r) (TAp (TAnn _) _)))) = insertMap x r
relEnvAddVariable (Variable x t) = error $ show x ++ show (pretty t)

appEnvAddVariable :: Variable -> ApplicativenessEnvironment -> ApplicativenessEnvironment
appEnvAddVariable (Variable x (TAp (TAnn a) (TAp (TAnn _) (TAp (TAnn _) _)))) = insertMap x a
appEnvAddVariable (Variable x t) = error $ show x ++ show (pretty t)

envAddVars :: IdSet -> Environment -> Environment
envAddVars is env = env{vars = unionSet is (vars env)}

-- Add foralls for strictness annotations
forallify :: Bool -> Type -> Type
forallify b (TAp (TAnn a) t) = TAp (TAnn a) $ forallify b t
forallify b t = foldr (\a t' -> TForall (Quantor (Just $ stringFromId a)) KAnn t') (typeRemoveStrictnessQuantification t) anns
  where
    anns = getVariablesType b t

getVariablesType :: Bool -> Type -> [Id]
getVariablesType b (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1)))) t2) = nub $ concat [i1, i2, i3]
  where
    i1 = getVariablesType b t1
    i2 = getVariablesType b t2
    i3 = concatMap getVariablesAnn [a1, r, a2]
getVariablesType b (TAp t1 t2) = nub $ getVariablesType b t1 ++ getVariablesType b t2
getVariablesType b (TStrict t) = getVariablesType b t
getVariablesType b (TForall _ _ t) = getVariablesType b t
getVariablesType True (TAnn a) = getVariablesAnn a
getVariablesType _ _ = []

-- Get relevance and applicative annotations of var, set them equal to contexts
getAnnotations :: Environment -> SAnn -> SAnn -> Id -> AnnotationEnvironment
getAnnotations env rel app var = unionMap (f (relEnv env) rel) (f (appEnv env) app)
  where
    f env' con = case lookupMap var env' of
      Just (AnnVar a) -> singleMap a con
      _ -> emptyMap

-- Make a L constraint for all annotation variables
getLConstraints :: Environment -> AnnotationEnvironment
getLConstraints = mapFromList . map (\x -> (x, L)) . getAnnotationVariablesEnv

-- Get all annotation variables in the environment to introduce constraints
getAnnotationVariablesEnv :: Environment -> [Id]
getAnnotationVariablesEnv env = f (relEnv env) ++ f (appEnv env)
  where
    f env' = map snd $ listFromMap $ mapMap fromAnn $ filterMap isAnn env'

-- Containment
containment :: Environment -> SAnn -> AnnotationEnvironment
containment env con = mapFromList $ map (\x -> (x, con)) (getAnnotationVariablesEnv env)

isTupAp :: Expr -> Bool
isTupAp (Con (ConTuple _)) = True
isTupAp (Ap e _) = isTupAp e
isTupAp (ApType e _) = isTupAp e
isTupAp _ = False

threeIds :: NameSupply -> (Id, Id, Id, NameSupply)
threeIds supply0 = (id1, id2, id3, supply3)
  where
    (id1, supply1) = freshId supply0
    (id2, supply2) = freshId supply1
    (id3, supply3) = freshId supply2

strictBind :: Bind -> AnnotationEnvironment -> AnnotationEnvironment
strictBind (Bind (Variable _ (TAp (TAnn (AnnVar a)) (TAp (TAnn (AnnVar r)) (TAp _ _)))) _) ae = ae'
    where
        ae' = insertMap a S $ insertMap r S ae
    

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


-- Switch back original and annotated type, or remove annotations
resetDeclaration :: CoreDecl -> CoreDecl
resetDeclaration decl = resetDeclaration' decl
  where
      t = typeRemoveAnnotations $ declType decl
      c = strictnessToCustom (declType decl) (declCustoms decl)
      resetDeclaration' :: CoreDecl -> CoreDecl
      resetDeclaration' DeclValue{}       = decl{declType = t, declCustoms = c}
      resetDeclaration' DeclAbstract{}    = decl{declType = t, declCustoms = c}
      resetDeclaration' DeclCon{}         = decl{declType = t}
      resetDeclaration' DeclTypeSynonym{} = decl{declType = t}
      resetDeclaration' _                 = decl

setStrictnessType :: CoreDecl -> CoreDecl
setStrictnessType decl = decl{declType = t}
  where
    t = typeFromCustom $ declCustoms decl

strictnessToCustom :: Type -> [Custom] -> [Custom]
strictnessToCustom t c = CustomDecl (DeclKindCustom (idFromString "strictness")) [CustomType t] : c

removeAnn :: [Type] -> [Type]
removeAnn (TAnn _:xs) = removeAnn xs
removeAnn x = x

-- Lookup annotation of variables
lookupVar :: SAnn -> SolvedConstraints -> SAnn
lookupVar (AnnVar x) sc | elemMap x sc = findMap x sc
lookupVar x _ = x

uncontain :: [Id] -> SAnn -> SAnn
uncontain xs (AnnVar x) | x `elem` xs = S
uncontain xs (Join x y) = join (uncontain xs x) (uncontain xs y)
uncontain xs (Meet x y) = meet (uncontain xs x) (uncontain xs y)
uncontain _  x          = x

-- Turn bind to strict if annotated with S
bindToStrict :: SolvedConstraints -> Bind -> Bool
bindToStrict sc (Bind (Variable _ (TAp (TAnn a) (TAp (TAnn r) (TAp _ _)))) _) = lookupVar r sc == S && lookupVar a sc == S
