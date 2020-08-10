{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE TupleSections #-}

module Helium.CodeGeneration.Core.Uniqueness.Data where

import Control.Monad.Identity
import Control.Monad.Reader
import Control.Monad.State.Strict
import Control.Monad.Writer.Strict hiding (Alt, Ap)
import qualified Data.List as L
import qualified Data.IntMap as M
import qualified Data.Maybe as M
import qualified Data.Set as S
import Lvm.Common.IdMap hiding (foldMap)
import qualified Lvm.Common.IdMap as IM (foldMap)
import Text.PrettyPrint.Leijen (pretty, Pretty)
import Lvm.Common.Id
import Lvm.Core.Expr
import Lvm.Core.Type

---------------------------------------------------------------
-- Operations on generating fresh annotation variables
----------------------------------------------------------------

newtype UniqueT m a = UniqueT (StateT UAnn m a)
  deriving (Functor, Applicative, Monad, MonadTrans, MonadIO)

newtype Unique a = Unique (UniqueT Identity a)
  deriving (Functor, Applicative, Monad, MonadUnique)

class Monad m => MonadUnique m where
  fresh :: m UAnn

instance (Monad m) => MonadUnique (UniqueT m) where
  fresh = UniqueT $ do
    ~(UVar n) <- get
    put (UVar (succ n))
    return (UVar n)

instance (Monoid r, MonadUnique m) => MonadUnique (ReaderT r m) where
  fresh = lift fresh

instance (Monoid w, MonadUnique m) => MonadUnique (WriterT w m) where
  fresh = lift fresh

evalUniqueT :: Monad m => UniqueT m a -> m a
evalUniqueT (UniqueT s) = evalStateT s (UVar 0)

evalUnique :: Unique a -> a
evalUnique (Unique s) = runIdentity (evalUniqueT s)

----------------------------------------------------------------
-- Reader Environment: Type Environment and the MSet
----------------------------------------------------------------

data REnv = REnv {
 type_env :: TyEnv,
 mset :: S.Set UAnn
}

instance Semigroup REnv where
  re1 <> re2 = REnv { type_env = type_env re1 <> type_env re2, mset = mset re1 <> mset re2 }

instance Monoid REnv where
  mempty = REnv mempty mempty

askT :: Infer TyEnv
askT = type_env <$> ask

askM :: Infer (S.Set UAnn)
askM = mset <$> ask

inREnv :: (Id, (Visibility, Annotated, Type)) -> S.Set UAnn -> Infer a -> Infer a
inREnv e us m = local rmodify m
  where rmodify renv = renv { type_env = extendT (type_env renv) e, mset = us <> mset renv}

----------------------------------------------------------------
-- Type Environment: map variable, constructor, function name to their usage and type
----------------------------------------------------------------

newtype TyEnv = TyEnv (IdMap (Visibility, Annotated, Type))

----------------------------------------------------------------
-- Operations on Type Environment
----------------------------------------------------------------

instance Show TyEnv where
  show (TyEnv m) = unlines (map showKaV (listFromMap m))
    where showKaV (i, (v, a, tp)) = "name: " ++ show i ++ ", visibility: " ++ show v ++ ", annotated: " ++ show a ++ ", type: " ++ show (pretty tp)

instance Semigroup TyEnv where
  (TyEnv e1) <> (TyEnv e2) = TyEnv (unionMap e1 e2)

instance Monoid TyEnv where
  mempty = TyEnv emptyMap

extendT :: TyEnv -> (Id, (Visibility, Annotated, Type)) -> TyEnv
extendT (TyEnv e) (i, vt) = TyEnv $ insertMap i vt e

lookupT :: Id -> TyEnv -> (Visibility, Annotated, Type)
lookupT i (TyEnv e) = getMap i e

inEnvT :: (Id, (Visibility, Annotated, Type)) -> Infer a -> Infer a
inEnvT e m = local rmodify m
  where rmodify renv = renv { type_env = extendT (type_env renv) e}

inEnvsT :: TyEnv -> Infer a -> Infer a
inEnvsT ty m = local rmodify m
  where rmodify renv = renv { type_env = ty <> type_env renv}

getAnnotations :: Type -> S.Set UAnn
getAnnotations (TAnn _ u) = S.singleton u
getAnnotations (TForall _ t) = getAnnotations t
getAnnotations (TAp t1 t2) = getAnnotations t1 <> getAnnotations t2
getAnnotations t = mempty

getUsagesFromAlt :: Type -> [Id] -> (UAnn, [(Id, UAnn)])
getUsagesFromAlt t xs
  | null xs = (getU t, mempty)
  | (x : xs') <- xs,
    (TAp (TAp (TCon TConFun) t1) t2) <- t =
    let (u, env) = getUsagesFromAlt t2 xs'
     in (u, (x, getU t1) : env)
  where
    getU (TAp (TAnn _ u) _) = u

getAltEnv :: Type -> [Id] -> (Type, TyEnv)
getAltEnv t x = (treturn, TyEnv $ mapFromList aenv)
  where (treturn, aenv) = getAltEnv' t x

getAltEnv' :: Type -> [Id] -> (Type, [(Id, (Visibility, Annotated, Type))])
getAltEnv' t xs
  | null xs = (removeUAnnFromType t, mempty)
  | (x : xs') <- xs,
    (TAp (TAp (TCon TConFun) t1) t2) <- t = let (treturn, aenv) = getAltEnv' t2 xs'
                                            in (treturn, (x, (Local, AYes, removeUAnnFromType t1)) : aenv)

addBindsToEnv :: Binds -> TyEnv
addBindsToEnv b = TyEnv $ mapFromList $ addBindsToEnv' b

addBindsToEnv' :: Binds -> [(Id, (Visibility, Annotated, Type))]
addBindsToEnv' (Rec bs) = addBindToEnv <$> bs
addBindsToEnv' (Strict b) = [addBindToEnv b]
addBindsToEnv' (NonRec b) = [addBindToEnv b]

addBindToEnv :: Bind -> (Id, (Visibility, Annotated, Type))
addBindToEnv (Bind (Variable i t) _) = (i, (Local, ANo, t))

----------------------------------------------------------------
-- Usage Environment
----------------------------------------------------------------

-- The Usage environment consists of a name (variable) mapped to a UAnn
newtype UsEnv = UsEnv (IdMap UAnn)

----------------------------------------------------------------
-- Operations on Usage Environment
----------------------------------------------------------------

instance Show UsEnv where
  show (UsEnv ue) = show (listFromMap ue)

usempty :: UsEnv
usempty = UsEnv emptyMap

-- Match
cOr :: UsEnv -> UsEnv -> Infer UsEnv
cOr = combine $ AOrConstraint

-- Application
cAnd :: UsEnv -> UsEnv -> Infer UsEnv
cAnd = combine $ AAndConstraint

cAnd1 :: Id -> UAnn -> UsEnv -> Infer UsEnv
cAnd1 = combine1 $ AAndConstraint

-- Lambda
cTimes :: UsEnv -> Infer UAnn
cTimes (UsEnv s) = do
  u0 <- fresh
  mapM_ (addAInEqConstraint u0) s
  return u0

combine :: (UAnn -> UAnn -> UAnn -> AConstraint) -> UsEnv -> UsEnv -> Infer UsEnv
combine c (UsEnv s1) (UsEnv s2) = UsEnv <$> (sequence $ unionMapWith addConstraint (return <$> s1) (return <$> s2))
  where
    addConstraint v1 v2 = join $ addABConstraint c <$> v1 <*> v2

combine1 :: (UAnn -> UAnn -> UAnn -> AConstraint) -> Id -> UAnn -> UsEnv -> Infer UsEnv
combine1 c i u1 ue@(UsEnv s) =
   case lookupMap i s of
        Nothing -> return (UsEnv $ insertMap i u1 s)
        Just u2 -> (UsEnv . flip (insertMap i) s) <$> addABConstraint c u1 u2

cScrutinee :: Id -> UsEnv -> Infer UsEnv
cScrutinee i (UsEnv s) = do
  u1 <- fresh
  case lookupMap i s of
        Nothing -> return (UsEnv $ insertMap i u1 s)
        Just u2 -> (UsEnv (insertMap i u2 s)) <$ addAEqConstraint u1 u2

foldrS :: (UAnn -> b -> b) -> b -> UsEnv -> b
foldrS f z (UsEnv us) = IM.foldMap f z us

foldrWithKeyS :: (Id -> UAnn -> b -> b) -> b -> UsEnv -> b
foldrWithKeyS f z (UsEnv us) = foldMapWithId f z us

findWithDefaultS :: (MonadUnique m) => Id -> UsEnv -> m UAnn
findWithDefaultS i (UsEnv e) = M.fromMaybe fresh (return <$> lookupMap i e)

lookupS :: Id -> UsEnv -> Maybe UAnn
lookupS i (UsEnv e) = lookupMap i e

removeS :: Id -> UsEnv -> UsEnv
removeS i (UsEnv e) = UsEnv $ deleteMap i e

extendS :: (Id, UAnn) -> UsEnv -> UsEnv
extendS (i, a) (UsEnv e) = UsEnv $ insertMap i a e

singletonS :: (Id, UAnn) -> UsEnv
singletonS (i, a) = UsEnv $ singleMap i a

partitionWithKeyS :: (Id -> UAnn -> Bool) -> UsEnv -> (UsEnv, UsEnv)
partitionWithKeyS f (UsEnv e) = let (e1, e2) = partitionMapWithId f e in (UsEnv e1, UsEnv e2)

----------------------------------------------------------------
-- Substititions
----------------------------------------------------------------

-- Substititions map UAnn to uniqueness annotations
newtype Substitutions = Substitutions (M.IntMap UAnn)

----------------------------------------------------------------
-- Operations on Substitutions
----------------------------------------------------------------

class Substitutable a where
  apply :: Substitutions -> a -> a

instance Semigroup Substitutions where
  (Substitutions s1) <> (Substitutions s2) = Substitutions (s1 <> s2)

instance Monoid Substitutions where
  mempty = Substitutions mempty

instance Substitutable Expr where
  apply s (Let b e) = Let (apply s b) (apply s e)
  apply s (Match i a) = Match i (apply s a)
  apply s (Ap e1 e2) = Ap (apply s e1) (apply s e2)
  -- A function applied to an annotation. If it is shared then apparently we tried
  -- to call a function that requires ones of its arguments to be unique. So call the
  -- the non-unique variant.
  apply (Substitutions s) (ApType (Var i) (TAnn _ (UVar a))) =
    case s M.! a of
      UShared -> Var (nonMutId i)
      _ -> Var i
  -- If we have a constructor, and it reuses memory, then if the variable is used shared
  -- remove the reuse of memory.
  apply (Substitutions s) (ApType (Con c m) (TAnn _ (UVar a))) = Con c (m >>= applyreuse)
    where
      applyreuse i = case s M.! a of
        UShared -> Nothing
        _ -> Just i
  apply s (ApType e t) = ApType (apply s e) (apply s t)
  apply s (Forall q e) = Forall q (apply s e)
  apply _ e = e

instance Substitutable Binds where
  apply s (Rec b) = Rec (apply s b)
  apply s (Strict b) = Strict (apply s b)
  apply s (NonRec b) = NonRec (apply s b)

instance Substitutable Bind where
  apply s (Bind v e) = Bind v (apply s e)

instance Substitutable Alt where
  apply s (Alt p e) = Alt p (apply s e)

instance Substitutable Type where
  apply s (TAp t1 t2) = TAp (apply s t1) (apply s t2)
  apply s (TAnn a1 a2) = TAnn a1 (apply s a2)
  apply s (TForall q t) = TForall q (apply s t)
  apply s (TQTy t us) = TQTy (apply s t) (map aTQTy us)
    where
      aTQTy (u1, u2) = (apply s u1, apply s u2)
  apply _ t = t

instance Substitutable UAnn where
  apply (Substitutions m) u@(UVar a) = M.findWithDefault u a m
  apply _ u = u

instance Substitutable a => Substitutable [a] where
  apply = fmap . apply

instance (Ord a, Substitutable a) => Substitutable (S.Set a) where
  apply = S.map . apply

nonMutId :: Id -> Id
nonMutId i = idFromString (stringFromId i ++ "_nonmut")

fromListS :: [(Int, UAnn)] -> Substitutions
fromListS = Substitutions . M.fromList

insertS :: Int -> UAnn -> Substitutions -> Substitutions
insertS k v (Substitutions m) = Substitutions (M.insert k v m)

lookupSubs :: Int -> Substitutions -> Maybe UAnn
lookupSubs k (Substitutions m) = M.lookup k m

deleteS :: Int -> Substitutions -> Substitutions
deleteS k (Substitutions m) = Substitutions (M.delete k m)

----------------------------------------------------------------
-- Operations on Free annotations
----------------------------------------------------------------

class FreeUVar a where
  fav :: a -> S.Set UVar

instance FreeUVar Type where
  fav (TAp t1 t2) = fav t1 <> fav t2
  fav (TForall (Quantor idx KAnn _) tp) = S.delete idx $ fav tp
  fav (TForall _ tp) = fav tp
  fav (TAnn _ a2) = fav a2
  fav _ = S.empty

instance FreeUVar UAnn where
  fav (UVar a) = S.singleton a
  fav _ = S.empty

instance FreeUVar a => FreeUVar [a] where
  fav = foldr (S.union . fav) S.empty

----------------------------------------------------------------
-- Operations on function application
----------------------------------------------------------------

{-
Retrieve the annotations on a function type:
  - the first annotation is p
  - the second annotation is p2
  - the third annotation is p0
Retrieve argument and return type:
  - the first type is the return type
  - the second type is the argument type
-}

getFAnnotations :: Type -> ([UAnn], [Type])
getFAnnotations (TAp t1 (TAp (TAnn _ u) t2)) = (u:us, t2:ts)
  where (us, ts) = getFAnnotations t1
getFAnnotations (TAp (TAnn _ u) (TCon TConFun)) = ([u], [])
getFAnnotations t = error (show t)

----------------------------------------------------------------
-- Annotate functions and constructors
----------------------------------------------------------------

-- Adds annotations on the type. If a type is not a function type, or is not a constructor application
-- then we do not add annotations. example: t :: Int does not get annotations but t :: [Int] does (t :: [w:Int]).
-- The reason is that in this case we have a constant, so the usage is attached to the variable and not the type.
initEnvFType :: (MonadUnique m) => Type -> m Type
initEnvFType (TForall q t) = TForall q <$> initEnvFType t
initEnvFType (TAp (TAp tar@(TCon TConFun) t1) t2) = do
  t1' <- addUAnnToType <$> fresh <*> initEnvFType t1
  t2' <- addUAnnToType <$> fresh <*> initEnvFType t2
  tar' <- flip addUAnnToType tar <$> fresh
  return (TAp (TAp tar' t1') t2')
initEnvFType (TAp t1 t2) = do
  t1' <- initEnvFType t1
  t2' <- addUAnnToType <$> fresh <*> initEnvFType t2
  return (TAp t1' t2')
initEnvFType t = return t

{-
  annotate data constructors with annotations, we only support:
  - recursive datatypes
  - sum and product types
  - nested types (with some restrictions)
  So no functions in datatypes or record datatypes
  For every occurence of the same type variable, the type variable gets the same annotation
  All other applications of datatypes get the same annotation.
  For example:
  - Cons :: a -> List a -> List a => Cons :: u0:a -> u1:(List u0:a) -> u1:(List u0:a)
  - Node :: a -> List (Tree a) -> Tree a => Node :: u0:a -> u1:(List u1:(Tree u0:a) -> u1:Tree u0:a
  In short: if datatype is required to be unique, then all nested applications have to be unique.
  This is very pessimistic, but very simple.
-}
initEnvCType :: (MonadUnique m) => Type -> m Type
initEnvCType t = do
  u <- fresh
  (us, t') <- initEnvCForAll u mempty t
  let uis = (\(UVar i) -> i) <$> (u : us)
      ft = foldr (TForall . flip (flip Quantor KAnn) Nothing) t' uis
      cs = map (u,) us
  case cs of
    [] -> return ft
    _ -> return $ TQTy ft cs

initEnvCForAll :: (MonadUnique m) => UAnn -> M.IntMap UAnn -> Type -> m ([UAnn], Type)
initEnvCForAll u m (TForall q@(Quantor i _ _) t) = do
  fu <- fresh
  let m' = M.insert i fu m
  (us, t') <- initEnvCForAll u m' t
  return (fu : us, TForall q t')
initEnvCForAll u m t = return ([], initEnvCType' u m t)

initEnvCType' :: UAnn -> M.IntMap UAnn -> Type -> Type
initEnvCType' u m (TAp (TAp (TCon TConFun) t1) t2) = (TAp (TAp (TCon TConFun) t1') t2')
  where t1' = initEnvCType' u m t1
        t2' = initEnvCType' u m t2
initEnvCType' _ m t@(TVar i)= addUAnnToType (m M.! i) t
initEnvCType' u _ t@(TCon _) = addUAnnToType u t
initEnvCType' u m (TAp t1 t2) = addUAnnToType u (TAp t1' t2')
  where t1' = t1
        t2' = initEnvCType' u m t2


----------------------------------------------------------------
-- Generalization and Instantiation
----------------------------------------------------------------

instantiate :: Id -> Type -> Visibility -> Annotated -> Infer (Type, UAnn)
instantiate i t v a = (,) <$> instantiate' i t v a <*> fresh

instantiate' :: Id -> Type -> Visibility -> Annotated -> Infer Type
instantiate' _ t v a
  | v == Extern || v == Global && a == AYes = instantiateType t
instantiate' _ t Local AYes = return t
instantiate' i t _ _ = do
  t' <- initEnvFType t
  tellAssumption i t'
  return t'

instantiateType :: Type -> Infer Type
instantiateType t =
  do
    (t', cs) <- instantiateConstrainedType t
    mapM_ (tellAConstraint) cs
    return t'

instantiateConstrainedType :: (MonadUnique m) => Type -> m (Type, [AConstraint])
instantiateConstrainedType (TQTy t us) = instantiateType' mempty us t
instantiateConstrainedType t = instantiateType' mempty [] t

instantiateType' :: (MonadUnique m) => Substitutions -> [(UAnn, UAnn)] -> Type -> m (Type, [AConstraint])
instantiateType' s us (TForall (Quantor a KAnn _) t) = do
  a' <- fresh
  instantiateType' (insertS a a' s) us t
instantiateType' s us t = return (apply s t, apply s (fmap (uncurry AInEqConstraint) us))

generalize :: S.Set UAnn -> Type -> Type
generalize ms t = foldr (\a t' -> TForall (Quantor a KAnn Nothing) t') t favs
  where
    favs = fav t `S.difference` (removeNonUVar ms)

removeNonUVar :: S.Set UAnn -> S.Set UVar
removeNonUVar = S.map (\(UVar u) -> u) . S.filter nonUVar
  where nonUVar a = a == UShared || a == UNone || a == UUnique

----------------------------------------------------------------
-- Constraints
----------------------------------------------------------------

{-
  Visibility:
  - Local is used for local let bindings.
  - Global is used for functions/constructors inside this module. No annotations exists for global functions
  - Extern is for functions/constructors outside this module. annotations exist for external functions and constructors.
-}
data Visibility = Local | Global | Extern
  deriving (Eq, Show)

{-
  Annotated:
  - ANo: for types which have not been annotated yet
  - AYes: for annotated types
-}
data Annotated = ANo | AYes
  deriving (Eq, Show)

{-
  The following combinations of Visibility and Annotated are valid:
  - Local/ANo: lambdas and let
  - Local/AYes: pattern matches
  - Global/ANo: functions in this module
  - Global/AYes: datatype constructors in this module, functions after instantiating
  - External/AYes: functions/constructors outside this module
-}

----------------------------------------------------------------
-- Type Constraints
----------------------------------------------------------------

{- We have multiple kinds of type constraints
   1. An Instance constraint: since we gather constraints bottom-up and we do not know which in this function have been typechecked yet,
      we introduce an instance constraint. This constraint is generated at let bindings and at module level (for functions defined in module).
      This constraint can be solved when a function has been type checked, and is a simple substitution of non-variable annotations (UShared and UUnique).
      function calls to (mutually) recursive bindings are transformed to equality constraints.
   2. An Equality constraint: is used for lambdas, recursive let bindings, and pattern matches. Enforces monomorphism.
   3. An InEquality constraint: is used for arguments of function applications.
-}
data TConstraint
  = TEqConstraint Type Type
  | TInEqConstraint Type Type
  | TIConstraint Bool Visibility (S.Set UAnn) Type Type

instance Show TConstraint where
  show (TEqConstraint t1 t2) = show (pretty t1) ++ " == " ++ show (pretty t2)
  show (TInEqConstraint t1 t2) = show (pretty t1) ++ " <= " ++ show (pretty t2)
  show (TIConstraint b v ms t1 t2) = "polyvariant: " ++ show b ++ ", visibility: " ++
                                     show v ++ ", mset: " ++ show (S.toList ms) ++ ", instance " ++
                                     show (pretty t1) ++ " of " ++ show (pretty t2)

----------------------------------------------------------------
-- Operations on Type Constraints
----------------------------------------------------------------

makeGlobalTIConstraints :: (Id -> Type) -> IdMap [Type] -> IdMap [Bool -> TConstraint]
makeGlobalTIConstraints f am = mapMapWithId makeGlobalTIConstraint am
  where
    makeGlobalTIConstraint :: Id -> [Type] -> [Bool -> TConstraint]
    makeGlobalTIConstraint i ts = let t1 = f i in map (\t2 b -> (TIConstraint b Global mempty t1 t2)) ts

addLetTConstraints ::[Id] -> [Type] -> S.Set UAnn -> Infer a -> Infer a
addLetTConstraints is ts ms m = censor addLetTConstraints' m
  where
    addLetTConstraints' w = foldr (uncurry (addLetTConstraint True ms)) w (zip is ts)

addLetTConstraint :: Bool -> S.Set UAnn -> Id -> Type -> WEnv -> WEnv
addLetTConstraint b ms i t we@(WEnv {assumptions = at, tconstraints = tcs}) =
  let mts = lookupMap i at
      tcs' = M.maybe tcs ((<> tcs) . foldMap (Endo . (:) . TIConstraint b Local ms t)) mts
   in we {assumptions = deleteMap i at, tconstraints = tcs'}

addTInEqConstraint :: Type -> Type -> Infer ()
addTInEqConstraint = (tellTConstraint .) . TInEqConstraint

addTEqConstraint :: Type -> Type -> Infer ()
addTEqConstraint = (tellTConstraint .) . TEqConstraint

isTIConstraint :: TConstraint -> Bool
isTIConstraint (TIConstraint {}) = True
isTIConstraint _ = False

----------------------------------------------------------------
-- Annotation Constraints
----------------------------------------------------------------

{- We have multiple kinds of annotation constraints
   1. An equality constraint: Used on the variable of a destructive update, it must be used once
   2. An inequality constraint: Used for all other constraints that involve two annotation variables, examples are in Lam and Ap
   3. An Function constraint: Contains function name and a list of annotations placed on the arguments.
      If one of the elements is shared then it means that one of the arguments was shared, but the function requires it to be unique.
   4. An Argument constraint: The first argument is the same as an element in the function constraint. The second argument is the usage
      of the argument and the third argument is the usage on the type argument. The first argument resolves to UShared, if argument is shared
      but function requires it to be unique, otherwise it is UNone (it is save to call this function with this argument.
   5. The last three kind of constraints are related to the usage environment:
      1. AnnAnd is used in function application, since variables in both environments will definitely be used: we take the sum of second and third argument
      2. AnnOr is used in branching, If a variable occurs in both environments then only one will be used at a given time: we take the max of second and third argument
      3. AnnGuard is used in let.  A let can only consist of non-nested applications or a variable. If it is a variable it gets inlined, so doesn't exist at all.
         If it is an application, then a variable in the application is used, if the called function uses the argument. If this is the case then we add
         count the variable. If not, then we pass the usage of this variable unmodified
-}

data AConstraint
  = AEqConstraint UAnn UAnn
  | AInEqConstraint UAnn UAnn
  | AFConstraint UAnn [UAnn]
  | AArgConstraint UAnn UAnn UAnn
  | AAndConstraint UAnn UAnn UAnn
  | AOrConstraint UAnn UAnn UAnn
  deriving (Eq, Ord)

instance Show AConstraint where
  show (AEqConstraint u1 u2) = show u1 ++ " = " ++ show u2
  show (AInEqConstraint u1 u2) = show u1 ++ " ⊑ " ++ show u2
  show (AFConstraint u1 u2) = show u1 ++ " == u ∈ " ++ show u2 ++ "== ω ? ω : ∅"
  show (AArgConstraint u1 u2 u3) = show u1 ++ " ≡ " ++ show u2 ++ " ⊑ " ++ show u3
  show (AAndConstraint u1 u2 u3) = show u1 ++ " ≡ " ++ show u2 ++ " + " ++ show u3
  show (AOrConstraint u1 u2 u3) = show u1 ++ " ≡ " ++ show u2 ++ " `max`  " ++ show u3

instance Substitutable AConstraint where
  apply s (AEqConstraint u1 u2) = AEqConstraint (apply s u1) (apply s u2)
  apply s (AInEqConstraint u1 u2) = AInEqConstraint (apply s u1) (apply s u2)
  apply s (AFConstraint u1 u2) = AFConstraint (apply s u1) (apply s u2)
  apply s (AArgConstraint u1 u2 u3) = AArgConstraint (apply s u1) (apply s u2) (apply s u3)
  apply s (AAndConstraint u1 u2 u3) = AAndConstraint (apply s u1) (apply s u2) (apply s u3)
  apply s (AOrConstraint u1 u2 u3) = AOrConstraint (apply s u1) (apply s u2) (apply s u3)

----------------------------------------------------------------
-- Operations on Annotation Constraints
----------------------------------------------------------------

addAFConstraint :: UAnn -> [UAnn] -> Infer ()
addAFConstraint u us = tellAConstraint (AFConstraint u us)

addAEqConstraint :: UAnn -> UAnn -> Infer ()
addAEqConstraint u1 u0 = (tellAConstraint (AEqConstraint u1 u0))

addAInEqConstraint :: UAnn -> UAnn -> Infer ()
addAInEqConstraint u1 u0 = tellAConstraint (AInEqConstraint u1 u0)

addAArgConstraint :: UAnn -> UAnn -> UAnn -> Infer ()
addAArgConstraint u1 u2 u3 = tellAConstraint (AArgConstraint u1 u2 u3)

addABConstraint :: (UAnn -> UAnn -> UAnn -> AConstraint) -> UAnn -> UAnn -> Infer UAnn
addABConstraint op u1 u2 = fresh >>= \u -> tellAConstraint (op u u1 u2) >> return u

----------------------------------------------------------------
-- Operations on WEnv
----------------------------------------------------------------

{- The Writer Environment:
   1. Annotation constraints
   2. Type constraints
 　3. An assumption map, maps function names to types.
      This assumption map is used, together with a list of function names to generate a graph which is then topologically sorted. The result is an order in which
      the functions need to be typechecked. If a function is solved, this results in an annotated type. From this annotated type substitutions are generated and applied.
-}
data WEnv = WEnv
  { aconstraints :: Endo [AConstraint],
    tconstraints :: Endo [TConstraint],
    assumptions :: IdMap [Type]
  }

instance Semigroup WEnv where
  (WEnv ac1 tc1 a1) <> (WEnv ac2 tc2 a2) = WEnv (ac1 <> ac2) (tc1 <> tc2) (unionMapWith (<>) a1 a2)

instance Monoid WEnv where
  mempty = WEnv mempty mempty emptyMap

tellAConstraint :: AConstraint -> Infer ()
tellAConstraint c = tell $ mempty {aconstraints = Endo (c :)}

tellTConstraint :: TConstraint -> Infer ()
tellTConstraint c = tell $ mempty {tconstraints = Endo (c :)}

tellAssumption :: Id -> Type -> Infer ()
tellAssumption k t = tell $ mempty {assumptions = singleMap k [t]}

{-
 Infer a is a monad tranformer containing of three things:
 - An inherited reader environment (TyEnv) mapping function names to their type.
 - A synthesized writer environment (WEnv) containing annotation constraints, type constraints,
   assumptions, and a list of reuses (must be unique)
 - An chained state (Unique) that generates fresh integers used for annotation variables
-}
type Infer a = ReaderT REnv (WriterT WEnv Unique) a
