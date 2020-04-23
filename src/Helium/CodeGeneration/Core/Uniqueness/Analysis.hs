{-# LANGUAGE TupleSections #-}

-- | Uniquenes Analysis as implemented will be done in three phases:
--   - Generate constraints to be solved (Constraints)
--   - Solve the constraints (Solving),
module Helium.CodeGeneration.Core.Uniqueness.Analysis where

import Control.Monad
import Control.Monad.Reader (ask, runReaderT)
import Control.Monad.Trans
import Control.Monad.Writer.Strict (pass, censor, runWriterT, listen)
import qualified Data.IntMap as M hiding (mapMaybe)
import qualified Data.Maybe as M (fromJust, mapMaybe)
import Data.Monoid (appEndo, Endo(..))
import qualified Data.Set as S
import qualified Data.List as L
import Helium.CodeGeneration.Core.TypeEnvironment
import Helium.CodeGeneration.Core.Uniqueness.Data
import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type
import Text.PrettyPrint.Leijen (pretty)

coreUniqueness :: CoreModule -> CoreModule
coreUniqueness cmod@Module {moduleDecls = decls} = cmod {moduleDecls = coreUniqueness' decls}

coreUniqueness' :: [CoreDecl] -> [CoreDecl]
coreUniqueness' = evalUnique . runUniquenessAnalysis

-- Get set of functions that have to be duplicated
-- let dups = undefined
-- in duplicate dups decls'

runUniquenessAnalysis :: [CoreDecl] -> Unique [CoreDecl]
runUniquenessAnalysis decls = do
  -- First annotate the types of the functions with fresh annotation variables
  -- and annotate every function call with a fresh annotation variable.
  -- Second create an initial environment mapping function names to types annotated with fresh variables
  (tyenv, tdecls) <- createEnv decls
  -- Run algorithm W on the module and generate constraints. the types of functions can be specialized
  -- so for every function the type is replaced with the specialized type
  --mcs <- algorithmW tyenv tdecls
  -- Solve the constraints resulting in substitutions
  --  substitutions <- lift $ solveConstraints constraints
  -- Apply the substitutions to the Core file
  --  sdecls <- lift $ apply substitutions wdecls
  return undefined

---------------------------------------------------------------
-- Operations on creating initial environment
---------------------------------------------------------------

-- Add for every function call an extra aptype parameter
createEnv ::[CoreDecl] -> Unique (TyEnv, [CoreDecl])
createEnv decls = do
  decls' <- initEnvDecl `mapM` decls
  let tyenv = foldr (flip extendT) mempty (M.mapMaybe getIdAndType decls')
  return (tyenv, decls')

getIdAndType :: CoreDecl -> Maybe (Id, (Visibility, Annotated, Type))
getIdAndType d | isValue d = Just (declName d, (getVisibility d, getAnnotated d, declType d))
  where
    getAnnotated (DeclValue {}) = ANo
    getAnnotated (DeclCon {}) = AYes
    getAnnotated (DeclAbstract {}) = AYes
    getVisibility (DeclValue {}) = Global
    getVisibility (DeclCon {declModule = mname}) = if mname == Nothing then Global else Extern
    getVisibility (DeclAbstract {}) = Extern
    isValue (DeclExtern {}) = False
    isValue (DeclCustom {}) = False
    isValue _ = True
getIdAndType _ = Nothing

{-
For constructors and function declarations we need to add annotations.
Since constructors are used for dictionary values in typeclasses and
for constructors from other modules.
If the module name of a constructor declaration is empty and the name of the constructor
does not start with ":Dict$" then it is a data constructor in the current module.

-}
initEnvDecl :: CoreDecl -> Unique CoreDecl
initEnvDecl d@(DeclValue {valueValue = expr}) = do
  expr' <- initEnvExpr expr
  return $ d {valueValue = expr'}
initEnvDecl d@(DeclCon {declModule = mname, declName = cname, declType = dtype}) | isConstructor =
  do
    dtype' <- initEnvCType dtype
    return $ d {declType = dtype'}
  where isConstructor = mname == Nothing && not (L.isPrefixOf "Dict$" (stringFromId cname))
initEnvDecl d = return d

{-
  For every function application f a, add a fresh annotation on f: f^u.
  We use this annotation to create a function constraint, that when solved will
  result in a substitution of UShared or UNone. When UShared we must call the non_mut function variant
  For every constructor application containing a memory reuse, we also add a fresh annotation. When
  the constraints are solved and this annotation is UShared, this constructor application cannot be performed
  in-place. So we remove the memory reuse.
  See Substitution instance on Expr for more information.
  Since we only want to do this for applications, when we have Ap we know that the variable
  in the leftmost branch is the function/constructor name.
-}
initEnvExpr :: Expr -> Unique Expr
initEnvExpr (Let b e) = Let <$> initEnvBinds b <*> initEnvExpr e
initEnvExpr (Match i a) = Match i <$> sequence (initEnvAlt <$> a)
initEnvExpr (Ap v@(Var _) e) = flip Ap e <$> aFreshExpr v
initEnvExpr (ApType v@(Var _) e) = flip ApType e <$> aFreshExpr v
initEnvExpr (Ap e1 e2) = flip Ap e2 <$> initEnvExpr e1
initEnvExpr (ApType e t) = flip ApType t <$> initEnvExpr e
initEnvExpr (Lam b v e) = Lam b v <$> initEnvExpr e
initEnvExpr (Forall q e) = Forall q <$> initEnvExpr e
initEnvExpr c@(Con _ (Just _)) = aFreshExpr c
initEnvExpr e = return e

initEnvBinds :: Binds -> Unique Binds
initEnvBinds (Strict b) = Strict <$> initEnvBind b
initEnvBinds (Rec bs) = Rec <$> sequence (initEnvBind <$> bs)
initEnvBinds (NonRec b) = NonRec <$> initEnvBind b

initEnvBind :: Bind -> Unique Bind
initEnvBind (Bind v e) = Bind v <$> initEnvExpr e

initEnvAlt :: Alt -> Unique Alt
initEnvAlt (Alt p e) = Alt p <$> initEnvExpr e

aFreshExpr :: Expr -> Unique Expr
aFreshExpr e = (ApType e . TAnn SNone) <$> fresh

---------------------------------------------------------------
-- Some functions used in the general algorithm
---------------------------------------------------------------

-- Get the type of a application: is it constructor or function application
getTypeOfApplication :: Expr -> Bool
getTypeOfApplication (Ap e1 _) = getTypeOfApplication e1
getTypeOfApplication (ApType e _) = getTypeOfApplication e
getTypeOfApplication (Var _) = True
getTypeOfApplication (Con _ _) = False
getTypeOfApplication _ = error ("unsupported expr")

{-
 For every private  function, introduce a fresh annotation variable.
 This environment is used to split
-}
initUsageDeclValue :: [CoreDecl] -> Unique (IdMap UAnn)
initUsageDeclValue [] = return emptyMap
initUsageDeclValue (DeclValue {declName = dname, declAccess = access} : ds) = do
   us <- initUsageDeclValue ds
   if accessPublic access then return us else flip (insertMap dname) us <$> fresh
initUsageDeclValue (_:ds) = initUsageDeclValue ds

{-
  For every function we infer global usage. In the case of public/extern functions this is UShared.
  Private functions, however, can be unique, if used uniquely. So for every private function we introduce a fresh annotation variable u.
  The uniqueness is now equal to the anotation in the usage environment. If a private function is used uniquely, then u == UUnique.
-}
collectGlobalUsage :: IdMap UAnn -> UsEnv -> Endo [AConstraint] -> [AConstraint]
collectGlobalUsage us ue eacs = appEndo (foldrWithKeyS (\i u xs -> Endo (AEqConstraint u (getMap i us) :) <> xs) eacs ue) []

---------------------------------------------------------------
-- Collect Constraints on declarations: general algorithm
---------------------------------------------------------------

algorithmUModule :: TyEnv -> [CoreDecl] -> Unique (IdMap (WEnv, Type), [AConstraint])
algorithmUModule tyenv ds = do
  -- initialize usage for private functions
  us <- initUsageDeclValue ds
  -- collect constraints for all declarations
  ((mcs, ue), eacs) <- runWriterT $ runReaderT (algorithmUDecls us ds) (REnv tyenv mempty)
  return (mcs, collectGlobalUsage us ue (aconstraints eacs))

algorithmUDecls :: IdMap UAnn -> [CoreDecl] -> Infer (IdMap (WEnv, Type), UsEnv)
algorithmUDecls _ [] = return (emptyMap, usempty)
algorithmUDecls is (DeclValue {declName = dname, declAccess = access, valueValue = expr} : ds) = do
  -- gather all constraint from this function.
  -- we want to capture constraints per function, so we first listen
  -- and then censor, cleaning the environment.
  ((tp, ue1), we) <- censor (const mempty) (listen $ algorithmUDecl is dname access expr)
  -- infer rest of the functions in this module
  (mcs, ue2) <- algorithmUDecls is ds
  -- combine usage environments
  ue <- cAnd ue1 ue2
  -- return map extended with the writer environment and type
  return (insertMap dname (we, tp) mcs, ue)
-- Do nothing in other cases
algorithmUDecls is (_ : ds) = algorithmUDecls is ds

algorithmUDecl :: IdMap UAnn -> Id -> Access -> Expr -> Infer (Type, UsEnv)
algorithmUDecl is dname access expr = do
  (t, u, ue) <- algorithmUExpr expr
  -- seperate private definitions from public ones
  let (ue1, ue2) = partitionWithKeyS (\k _ -> elemMap k is) ue
  -- for exported and imported definitions, usage is shared
  sequence_ (foldrS (\u' cs -> addAEqConstraint u' UShared : cs) [] ue2)
  -- if function is exported then usage is shared otherwise add quality constraint
  -- between value in the map and the usage returned from this function.
  case accessPublic access of
    True -> addAEqConstraint UShared u
    False -> addAEqConstraint (getMap dname is) u
  return (t, ue1)

---------------------------------------------------------------
-- Collect constraints on expressions
---------------------------------------------------------------

algorithmUExpr :: Expr -> Infer (Type, UAnn, UsEnv)
algorithmUExpr (Let b e) = do
  -- create type environment for bindings
  let benv = addBindsToEnv b
  -- use this environment in inferring the body of the bindings
  -- and return binder usage and usage environment.
  -- we need WEnv to create equality constraints for recursive let bindings
  (ks, tps, vs, ue1) <- inEnvsT benv (algorithmUBinds b)
  -- get the mset
  ms <- askM
  -- run algorithm for body of let; create for nested-types polymorphic instantiation constraints
  (t2, u, ue2) <- addLetTConstraints ks tps (S.fromList vs <> ms) (inEnvsT benv (algorithmUExpr e))
  -- merge the two environments: definition and body, and generate && constraints
  ue <- cAnd ue1 ue2
  -- The usage of a binder is at most as big as in the body
  zipWithM_ (\k v -> maybe (return ()) (addAInEqConstraint v) (lookupS k ue)) ks vs
  -- return type, usage, and usage environment with let definitions removed
  return (t2, u, foldr removeS ue ks)
algorithmUExpr (Match i xs) = do
  -- get visibility, annotated, and type
  (v, a, t) <- lookupT i <$> askT
  -- instantiate type given the visibility and annotated
  (st, su) <- instantiate i t v a
  -- get the return type
  (tp, u, ue) <- algorithmUAlts su st xs
  -- if scrutinee is not in the usage environment, add it.
  let ue' = maybe (extendS (i, su) ue) (const ue) (lookupS i ue)
  -- return type, usage and usage environment
  return (tp, u, ue')
algorithmUExpr (Lam _ (Variable i tArg) e) = do
  -- lambda functions should be monomorphic and in whole function be the same
  tArg' <- initEnvFType tArg
  -- collect the annotations on the argument, they will be added to the mset
  let ms = getAnnotations tArg'
  (tReturn, u2, ue) <- inREnv (i, (Local, AYes, tArg')) ms (algorithmUExpr e)
  -- get the usage from this variable, if the variable is not used, introduce a fresh variable
  u1 <- findWithDefaultS i ue
  -- Add inequality constraints: the usage of a variable must be at least as great as the contained annotations
  mapM_ (addAInEqConstraint u1) ms
  -- remove the usage of this variable from the usage environment
  let ue' = removeS i ue
  -- create containment constraints
  u0 <- cTimes ue'
  -- annotate the function, according to type rule
  let tArg'' = addUAnnToType u1 tArg'
      tAr = addUAnnToType u0 (TCon TConFun)
      tReturn' = addUAnnToType u2 tReturn
  -- return fresh usage for this lambda expression
  u <- fresh
  return (TAp (TAp tAr tArg'') tReturn', u, ue')
algorithmUExpr (Forall q e) = do
  -- retrieve type from expression, usage, and usage environment
  (t, u, us) <- algorithmUExpr e
  -- return type, usage, and usage environment
  return (TForall q t, u, us)
algorithmUExpr a@(Ap _ _) = case getTypeOfApplication a of
                             -- Function application
                             True -> algorithmUFAp [] a
                             -- Constructor application
                             False -> algorithmUCAp a
algorithmUExpr (Var i) = do
  (t, u) <- algorithmUVar i
  return (t, u, singletonS (i, u))
algorithmUExpr (Lit lit) = do
  -- get type of literal
  let tp = typeOfLiteral lit
  -- Generate fresh annotation variable
  u <- fresh
  return (tp, u, usempty)
algorithmUExpr t = algorithmUCAp t

algorithmUVar :: Id -> Infer (Type, UAnn)
algorithmUVar i = do
  -- get visibility, annotated, and type
  (v, a, t) <- lookupT i <$> askT
  -- instantiate type given the visibility and annotated
  instantiate i t v a

---------------------------------------------------------------
-- Collect constraints on let bindings
---------------------------------------------------------------

algorithmUBinds :: Binds -> Infer ([Id], [Type], [UAnn], UsEnv)
algorithmUBinds (Strict b) = do
  -- generate constraints for strict let bindings
  (i, tp, u, ue) <- algorithmUBind b
  return ([i], [tp], [u], ue)
algorithmUBinds (NonRec b) = do
  -- generate constraints for non-recursive let bindings
  (i, tp, u, ue) <- algorithmUBind b
  return ([i], [tp], [u], ue)
algorithmUBinds (Rec bs) = pass $ do
  -- generate constraints for recursive let bindings
  (is, tps, us, ue) <- algorithmURecBinds bs
  -- for nested types, we add monomorphic type constraints. mset is mempty
  return ((is, tps, us, ue), flip (foldr (uncurry (addLetTConstraint False mempty))) (zip is tps))

algorithmURecBinds :: [Bind] -> Infer ([Id], [Type], [UAnn], UsEnv)
algorithmURecBinds [] = return (mempty, mempty, mempty, usempty)
algorithmURecBinds (b : bs) = do
  -- generate constraints for bind
  (i, tp, u, ue1) <- algorithmUBind b
  -- and recursively generate constraints for other binds
  (is, tps, us, ue2) <- algorithmURecBinds bs
  -- a recursive bind is smallest recursive group, so if a variable occurs in multiple binds
  -- it is defenitely used, and thus shared
  ue <- cAnd ue1 ue2
  --- return identifiers, types, usages, and usage environment
  return (i : is, tp : tps, u : us, ue)

algorithmUBind :: Bind -> Infer (Id, Type, UAnn, UsEnv)
algorithmUBind (Bind (Variable i _) e) = do
  -- generate constraints for bind expression
  (tp, u, ue) <- algorithmUExpr e
  -- return identifier, type, usage, and usage environment
  return (i, tp, u, ue)

---------------------------------------------------------------
-- Collect constraints on case patterns
---------------------------------------------------------------

algorithmUAlts :: UAnn -> Type -> [Alt] -> Infer (Type, UAnn, UsEnv)
algorithmUAlts su st [x] = do
  (t, u, ue) <- algorithmUAlt su st x
  return (t, u, ue)
algorithmUAlts su st (x : xs) = do
  (t1, u1, ue1) <- algorithmUAlt su st x
  (t2, u2, ue2) <- algorithmUAlts su st xs
  -- usage in return type of all branches must be the same
  addTEqConstraint t1 t2
  -- When we match, the returned usage must be the same for all branches
  addAEqConstraint u1 u2
  -- The variables in every branch may be used differently
  ue <- cOr ue1 ue2
  -- return the type, usage environment
  return (t1, u1, ue)
algorithmUAlts _ _ [] = error "Alt should not be empty"

algorithmUAlt :: UAnn -> Type -> Alt -> Infer (Type, UAnn, UsEnv)
algorithmUAlt su st (Alt (PatCon (ConId i) ts is) e) = do
  -- lookup type
  (v, a, t) <- lookupT i <$> askT
  -- apply substitutions from ts to type and instantiate
  t' <- flip typeApplyList ts <$> instantiate' i t v a
  -- create an environment that maps every constructor argument to its type.
  -- these types are already annotated so we do not need constraints between types, only for the return type.
  -- Also returns the return type
  let (treturn, aenv) = getAltEnv t' is
  -- add type equality between type of scrutinee and return type of constructor
  addTEqConstraint st treturn
  -- get return usage of Alt and every usage of constructor argument
  let (ureturn, ius) = getUsagesFromAlt t' is
  -- add type equality between usage of scrutinee and return type of constructor
  addAEqConstraint su ureturn
  -- collect constraints from the body
  (te, u, ue) <- inEnvsT aenv $ algorithmUExpr e
  -- map usage from the variables in the body to the argument
  let ut = M.mapMaybe (\(i', u') -> (u',) <$> lookupS i' ue) ius
  -- add equality constraints
  mapM_ (uncurry addAInEqConstraint) ut
  -- remove the variables from the usage environment
  let ue' = foldr (removeS . fst) ue ius
  -- return type, usage and usage environment
  return (te, u, ue')
algorithmUAlt _ _ (Alt _ e) = algorithmUExpr e

---------------------------------------------------------------
-- Collect constraints on function applications
---------------------------------------------------------------

algorithmUFAp :: [UAnn] -> Expr -> Infer (Type, UAnn, UsEnv)
algorithmUFAp xs (ApType (Var i) (TAnn _ fu)) = do
  -- Add FConstraint:
  -- - If one of the members resolves to shared then create substitution shared otherwise none
  addAFConstraint fu xs
  -- get type, usage and usage environment from function name
  (t, u) <- algorithmUVar i
  -- return type, usage, and usage environment
  return (t, u, singletonS (i, u))
algorithmUFAp xs (Ap e1 (Var i)) = do
  -- Generate a fresh variable for FConstraint
  ffv <- fresh
  -- Retrieve u_1 and the type of t_1
  (t1, p1, ue) <- algorithmUFAp (ffv : xs) e1
  -- get type, usage, and usage environment from argument
  (t2, p3) <- algorithmUVar i
  -- Get the annotations, argument type, and return type of ft
  let ([p, p2, p0], [ftreturn, ftarg]) = getFAnnotations t1
  -- Add the constraint on the arrow
  addAInEqConstraint p1 p0
  -- add argument inequality constraint
  addTInEqConstraint t2 ftarg
  -- if p2 = shared and p3 = unique then p2 = ffv = shared, otherwise p2 = unique and ffv = none
  -- Add an aargConstraint:
  addAArgConstraint ffv p3 p2
  -- combine two environments
  ue' <- cAnd1 i p3 ue
  -- return the type, usage, and new environment
  return (ftreturn, p, ue')
-- Function applied to a type, instantiates TForall. the type t2 in TForall does not need annotation variables
-- since no extra constraints are generated.
algorithmUFAp xs (ApType e t2) = do
  -- instantiate type with type t2 given as argument
  ~(TForall (Quantor idx _ _) t1, u, ue) <- algorithmUFAp xs e
  -- return substituted type, usage , and usage environment
  return (typeSubstitute idx t2 t1, u, ue)
algorithmUFAp _ e = error ("algorithmUFAp: unsupported expr" ++ show (pretty e))

---------------------------------------------------------------
-- Collect constraints on constructor applications
---------------------------------------------------------------

-- Function for inference of constructor application
algorithmUCAp :: Expr -> Infer (Type, UAnn, UsEnv)
algorithmUCAp e = do
  -- Collect type, and the usage env
  (tp, ue) <- algorithmUCAp' e
  case tp of
    (TAp (TAnn _ u) tp') -> return (tp', u, ue)
    _ -> error (show (pretty e))
  -- return the type, usage, and usage environment

algorithmUCm :: Expr -> Infer (Type, Id)
algorithmUCm (Con (ConId i) (Just m)) = do
  -- Lookup the type of the constructor
  (v, a, t) <- lookupT i <$> askT
  -- Instantiate type
  t' <- instantiate' i t v a
  -- return type of the constructor and the memory reuse variable id
  return (t', m)
algorithmUCm (Con (ConTuple arity) (Just m)) = do
  let tp = typeTuple arity
  t' <- initEnvCType tp >>= instantiateType
  return (t', m)
algorithmUCm _ = error ("algorithmUCm: unsupported expr")

algorithmUCAp' :: Expr -> Infer (Type, UsEnv)
algorithmUCAp' (ApType e (TAnn _ cu)) = do
  (tp, m) <- algorithmUCm e
  -- Since we have a memory reuse, annotation on variable m must be unique
  addAEqConstraint cu UUnique
  -- Return tp and empty usage environment: usage is already added to usage list
  return (tp, singletonS (m, cu))
algorithmUCAp' (Ap e1 (Var i)) = do
  -- get the argument (ignore) and return type, the usage annotation,
  -- and the usage environment
  ~(TAp (TAp (TCon TConFun) (TAp (TAnn _ u1) t1)) tReturn, ue) <- algorithmUCAp' e1
  -- get type of the argument, usage, and usage environment
  (t2, u2) <- algorithmUVar i
  -- add equality annotation constraint: constructors are already polyvariant
  addAEqConstraint u2 u1
  -- add type constraint
  addTEqConstraint t1 t2
  -- Add (i,u2) to usage environment.
  ue' <- cAnd1 i u2 ue
  -- return the return type and the updated usage environment
  return (tReturn, ue')
algorithmUCAp' (ApType e t2) = do
  -- instantiate type with type given as argument
  ~(TForall (Quantor idx _ _) t1, ue) <- algorithmUCAp' e
  -- return substituted type, usage , and usage environment
  return (typeSubstitute idx t2 t1, ue)
algorithmUCAp' (Con (ConId i) _) = do
  -- Get information about this identifier
  (v, a, t) <- lookupT i <$> askT
  t' <- instantiate' i t v a
  -- return type, annotation variable
  return (t', usempty)
algorithmUCAp' (Con (ConTuple arity) _) = do
  let t = typeTuple arity
  t' <- initEnvCType t >>= instantiateType
  return (t', usempty)
algorithmUCAp' _ = error ("algorithmUCAp': unsupported expr")
