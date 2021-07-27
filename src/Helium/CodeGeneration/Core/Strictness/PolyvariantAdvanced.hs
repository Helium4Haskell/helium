module Helium.CodeGeneration.Core.Strictness.PolyvariantAdvanced (polyvariantStrictness) where

-- THIS ANALYSIS IS DEPRECATED

import Data.List
import qualified Data.Set as S

import Helium.CodeGeneration.Core.BindingGroup
import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.Strictness.DataAdvanced
import Helium.CodeGeneration.Core.Strictness.Solve
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

import Text.PrettyPrint.Leijen (pretty)

-- Analysis data type, containing return expression, set of constraints, environment containing the annotations and solved constraints
data Analysis a = Analysis a Constraints AnnotationEnvironment SolvedConstraints BindMap

mergeAnalysis :: (SAnn -> SAnn -> SAnn) -> [Analysis a] -> Analysis [a]
mergeAnalysis _ [] = Analysis [] S.empty emptyMap emptyMap emptyMap
mergeAnalysis f (x:xs) = Analysis (v:v') (S.union c c') (unionMapWith f a a') (unionMap sc sc') (unionMap r r')
    where
        Analysis v c a sc r = x
        Analysis v' c' a' sc' r' = mergeAnalysis f xs

type GroupData = (PolyMap, TypeEnvironment, NameSupply)
type CoreGroup = BindingGroup Expr

polyvariantStrictness :: NameSupply -> CoreModule -> CoreModule
polyvariantStrictness supply m = m{moduleDecls = map (setValue (forallify Nothing . annotateTypeAbstract env supply3) values') $ moduleDecls m}
  where
    (supply1, supply') = splitNameSupply supply
    (supply2, supply3) = splitNameSupply supply'
    -- Ignore declarations which have already been analysed
    (decls1, decls2) = partition (any isCustomAnn . declCustoms) $ moduleDecls m
    -- Split module in functions and others (constructors, abstract, synonyms)
    (values, others) = partition isDeclValue decls2
    -- For declarations which have been annotated, set strictness type to declType
    decls1' = map setStrictnessType decls1
    -- Annotate others
    others' = mapWithSupply (annotateDeclaration (typeEnvForModule m)) supply1 others
    -- Create starting environment
    env = typeEnvForModule m{moduleDecls = others' ++ decls1'}
    -- Binding group analysis for functions
    groups = coreBindingGroups values
    (values', _, _) = foldl groupStrictness (emptyMap, env, supply2) groups

groupStrictness :: GroupData -> CoreGroup -> GroupData
-- Single declaration
groupStrictness (v, env, supply) (BindingNonRecursive d) = (v', env', supply2)
  where
    (supply1, supply2) = splitNameSupply supply
    -- Analyse function
    Analysis e cs ae sc1 r = analyseDeclaration env supply1 d
    -- Solve constraints
    sc2 = solveConstraints ae cs
    sc3 = mapMap (replaceVar sc2) sc1
    sc = unionMap sc2 sc3
    -- Transform expression using solved constraints
    e' = transformExpression sc r $ valueValue d
    -- Get type, apply transformations and forallify
    t' = forallify Nothing $ transformType sc $ normalTypeOfCoreExpression env e
    -- Add function to environment for next function
    env' = typeEnvAddGlobalValue (declName d) t' env
    -- Add new value
    v' = insertMap (declName d) (e', t') v
-- Group of recursive declarations
groupStrictness (vs, env, supply) (BindingRecursive ds) = (vs', env'', supply3)
  where
    (supply1, supply') = splitNameSupply supply
    (supply2, supply3) = splitNameSupply supply'
    -- Annotate type signatures and add them to the envorinment
    ts = mapWithSupply (\s d -> annotateType env s $ declType d) supply1 ds
    env' = typeEnvAddGlobalValues (map (\(d, t) -> (declName d, t)) (zip ds ts)) env
    -- Run analysis on all bodies, merge information with meet
    Analysis es cs ae sc1 r = mergeAnalysis meet $ mapWithSupply (analyseDeclaration env') supply2 ds
    -- Get type of function bodies
    ts' = map (normalTypeOfCoreExpression env') es
    -- Analyse type to solve the annotations which where put there at the beginning
    cs2 = zipWith (analyseType env) ts ts'  
    -- Solve constraints
    sc2 = solveConstraints ae (S.union cs (S.unions cs2))
    sc3 = mapMap (replaceVar sc2) sc1
    sc = unionMap sc2 sc3
    -- Transform all expressions using solved constraints
    es' = map (transformExpression sc r . valueValue) ds
    -- Apply solved constraints to types and forallify
    ts'' = map (forallify Nothing . transformType sc) ts'
    -- Add types to environment for next functions
    env'' = typeEnvAddGlobalValues (map (\(d, t) -> (declName d, t)) (zip ds ts'')) env
    -- Add new values
    vs' = foldl (\v (d, e, t) -> insertMap (declName d) (e, t) v) vs $ zip3 ds es' ts''
groupStrictness d (BindingNonFunction _) = d -- Split occurs before binding group analysis

{-
    Analyse
-}

analyseDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> Analysis Expr
analyseDeclaration tyEnv supply decl@DeclValue{} = analyseExpression env S (AnnVar i) supply2 ie
    where
        (i, supply') = freshId supply
        (supply1, supply2) = splitNameSupply supply'
        -- Instantiate forallified expressions
        ie = instantiateExpression tyEnv supply1 $ valueValue decl
        env = Environment tyEnv emptyMap emptyMap

analyseExpression :: Environment -> SAnn -> SAnn -> NameSupply -> Expr -> Analysis Expr
analyseExpression env rel app supply (Let b e) = Analysis (Let b' e') (S.union c1 c2) (unionMapWith meet a1 as) (unionMap sc1 sc2) (unionMap r1 r2)
    where
        (supply1, supply') = splitNameSupply supply
        (supply2, supply3) = splitNameSupply supply'
        -- Analyse binds
        Analysis b' c1 a1 sc1 r1 = analyseBinds env supply1 rel b
        -- Add annotated binds to environment
        env' = envAddBinds b' env
        -- Instantiate quantified functions
        e1 = instantiateExpression (typeEnv env') supply2 e
        -- Analyse body, set contexts to S
        Analysis e' c2 a2 sc2 r2 = analyseExpression env' S app supply3 e1
        -- Containment on old environment
        as = containment env rel a2
analyseExpression env rel app supply (Match i a) = Analysis (Match i a') c (unionMapWith meet ae1 ae2) sc r
    where
        Analysis _ _ ae1 _ _ = analyseExpression env rel app supply (Var i)
        -- Merge with join as strictness has to occur in every case
        Analysis a' c ae2 sc r = mergeAnalysis join $ mapWithSupply (analyseAlt env rel app) supply a
analyseExpression env rel app supply (Ap e1 e2) = Analysis (Ap e1' e2') cs (unionMapWith meet ae1 ae2) (unionMap sc1 sc2) (unionMap r1 r2)
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse function, with applicative context set to relevance
        Analysis e1' c1 ae1 sc1 r1 = analyseExpression env rel rel supply1 e1
        -- Get type of function and application
        t1 = normalTypeOfCoreExpression (typeEnv env) e1'
        t2 = normalTypeOfCoreExpression (typeEnv env) e2'
        -- Get the annotations on the function arrow, and unifications between the function and the given argument
        -- If it is an application to a tuple, take L and no constraints
        (a1, r, a2, c3) = case t1 of
            (TAp (TAp (TCon TConFun) (TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') t1')))) _) -> (a1', r', a2', analyseType (typeEnv env) t1' t2)
            _ -> (L, L, L, S.empty)
        -- Analyse argument with context of the previous annotations
        Analysis e2' c2 ae2 sc2 r2 = analyseExpression env (join rel r) (join rel a1) supply2 e2
        -- Add constraint on applicativeness
        cs = S.insert (app `Constraint` a2) $ S.unions [c1, c2, c3]
analyseExpression env rel app supply (ApType e t) = Analysis (ApType e' t') c a sc r
    where
        (supply1, supply2) = splitNameSupply supply
        -- Annotate type
        t' = annotateType (typeEnv env) supply1 t
        -- Analyse expression
        Analysis e' c a sc r = analyseExpression env rel app supply2 e
analyseExpression env _ app supply (Lam s (Variable x t) e) = Analysis (Lam s v' e') c a' sc r'
    where
        (id1, id2, id3, supply') = threeIds supply
        (supply1, supply2) = splitNameSupply supply'
        -- Annotate type in variable
        t' = annotateType (typeEnv env) supply1 t
        -- If lambda was strict, set its annotation variable equal to S
        ann2 = if s then S else AnnVar id2
        -- Give extra annotation to variable
        v' = Variable x (TAp (TAnn $ AnnVar id1) (TAp (TAnn ann2) (TAp (TAnn $ AnnVar id3) t')))
        -- Add variable to environment
        env' = envAddVariable v' env
        -- Analyse expression, set relevance to S
        Analysis e' c a sc r = analyseExpression env' S (AnnVar id3) supply2 e
        -- Containment on old environment
        a' = containment env app a
        -- If not strict, add variable to map which might turn to strict
        r' = if s then r else insertMap x (AnnVar id2) r
analyseExpression env rel app supply (Forall q k e) = Analysis (Forall q k e') c a sc r
    where
        -- Forall can be ignored
        Analysis e' c a sc r = analyseExpression env rel app supply e
analyseExpression env _ _ _ (Con c) = Analysis (Con c) S.empty (getLConstraints env) emptyMap emptyMap -- Set all annotation variables to L
analyseExpression env rel app _ (Var v) = Analysis (Var v) S.empty (unionMapWith meet (getLConstraints env) ae) emptyMap emptyMap
    where
        -- Set all annotation variables to L except the annotations related to this variable, which are set to context
        ae = getAnnotations env rel app v
analyseExpression env _ _ _ (Lit l) = Analysis (Lit l) S.empty (getLConstraints env) emptyMap emptyMap -- Set all annotation variables to L

analyseBinds :: Environment -> NameSupply -> SAnn -> Binds -> Analysis Binds
analyseBinds env supply rel (Rec bs) = Analysis (Rec b1) cs ae (unionMap sc sc') r
    where
        (supply1, supply2) = splitNameSupply supply
        -- Annotate types beforehand because they occur in the body
        bs' = mapWithSupply (annotateBind env) supply1 bs
        -- Add binds to environment
        env' = envAddBinds (Rec bs') env
        -- Run analysis on every bind separately
        (xs, is') = unzip $ mapWithSupply (analyseRecBind env' rel) supply2 bs'
        -- Merge the results with meet, as being strict in one bind is enough
        Analysis bs'' c a sc' r = mergeAnalysis meet xs
        -- Calculate set of annotation variables which can be solved
        is = diffSet (unionSets $ map getVariablesBind bs'') (setFromList $ concat is')
        -- Run simplifier to get solved local constraints
        Analysis _ cs ae sc _ = simplify is c a
        -- Apply solved constraints to get type signatures for all binds
        b1 = map (simplifyBind is sc) bs''
analyseBinds env supply rel (NonRec (Bind (Variable x _) e)) = Analysis (NonRec b) cs' ae' (unionMap sc sc') r'
    where
        -- Fresh variable for relevance annotation
        (id1, id2, _, supply') = threeIds supply
        -- Run analysis on binding with relevance set to context
        Analysis e' cs ae sc r = analyseExpression env (join rel (AnnVar id2)) (join rel (AnnVar id1)) supply' e
        -- Calculate set of annotation variables which can be solved
        is = getVariablesExpr e'
        -- Run simplifier to get solved local constraints
        Analysis _ cs' ae' sc' _ = simplify is cs ae
        -- Apply solved constraints to get type signature for bind
        t' = forallify (Just is) $ simplifyType sc' $ normalTypeOfCoreExpression (typeEnv env) e'
        -- Add annotations outside the type
        b = Bind (Variable x (TAp (TAnn $ AnnVar id1) (TAp (TAnn $ AnnVar id2) (TAp (TAnn S) t')))) e'
        -- Bind is NonRec, add to map of those which might be turned to strict
        r' = insertMap x (AnnVar id2) r
analyseBinds env supply rel (Strict (Bind (Variable x _) e)) = Analysis (Strict b) cs' ae' (unionMap sc sc') r
    where
        -- Fresh variables for relevance and both applicativeness
        (i, supply') = freshId supply
        -- Run analysis on binding with relevance set to context
        Analysis e' cs ae sc r = analyseExpression env rel (join rel (AnnVar i)) supply' e   
        -- Calculate set of annotation variables which can be solved
        is = getVariablesExpr e'
        -- Run simplifier to get solved local constraints
        Analysis _ cs' ae' sc' _ = simplify is cs ae
        -- Apply solved constraints to get type signature for bind
        t' = forallify (Just is) $ simplifyType sc' $ normalTypeOfCoreExpression (typeEnv env) e'
        -- Add annotations outside the type
        b = Bind (Variable x (TAp (TAnn $ AnnVar i) (TAp (TAnn S) (TAp (TAnn S) t')))) e'

analyseRecBind :: Environment -> SAnn -> NameSupply -> Bind -> (Analysis Bind, [Id])
analyseRecBind env rel supply (Bind v e) = (Analysis (Bind (Variable x t'') e') (S.union cs1 cs2) ae sc r, map fromAnn [a1, rel', a2])
    where
        -- Get annotation from variable previously annotated
        Variable x (TAp (TAnn a1) (TAp (TAnn rel') (TAp (TAnn a2) t))) = v
        -- Run analysis on binding with relevance set to context
        Analysis e' cs1 ae sc r = analyseExpression env (join rel rel') (join rel a1) supply e
        -- Get type of body
        t' = normalTypeOfCoreExpression (typeEnv env) e'
        t'' = TAp (TAnn a1) (TAp (TAnn rel') (TAp (TAnn a2) t'))
        -- As recursive binding, find the new values for the placed annotations
        cs2 = analyseType (typeEnv env) t t'
        
analyseAlt :: Environment -> SAnn -> SAnn -> NameSupply -> Alt -> Analysis Alt
analyseAlt env rel app supply (Alt p e) = Analysis (Alt p e') c a sc r
    where
        -- Run analysis 
        Analysis e' c a sc r = analyseExpression (envAddPattern p env) rel app supply e

-- Analyse type
analyseType :: TypeEnvironment -> Type -> Type -> Constraints
analyseType env t1 t2
    | t1 /= t1' || t2 /= t2' = analyseType env t1' t2' -- Normalization changes types, try again
    | t1 == t2               = S.empty                 -- Types equal, analysis completed
        where
            t1' = typeNormalizeHead env t1
            t2' = typeNormalizeHead env t2
analyseType env (TAp (TAp (TCon TConFun) t11) t12) (TAp (TAp (TCon TConFun) t21) t22) = cs
    -- Function arrows, analyse every pair of annotations on them
  where
    (TAp (TAnn a1 ) (TAp (TAnn r ) (TAp (TAnn a2 ) t1'))) = t11
    (TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') t2'))) = t21
    c1 = analyseType env t1' t2'
    c2 = analyseType env t12 t22
    cs = S.insert (a1' `Constraint` a1) $ S.insert (r' `Constraint` r) $ S.insert (a2' `Constraint` a2) $ S.union c1 c2
analyseType env (TAp t11 t12) (TAp t21 t22) = S.union c1 c2
    where
        c1 = analyseType env t11 t21
        c2 = analyseType env t12 t22
analyseType env (TForall _ _ t1) (TForall _ _ t2) = analyseType env t1 t2
analyseType env (TStrict t1) t2 = analyseType env t1 t2
analyseType env t1 (TStrict t2) = analyseType env t1 t2 -- Remove all strict type information
analyseType _ (TVar _) (TVar _) = S.empty -- Lift has a bug which might distort type variables, exact index doesn't matter
analyseType _ t1 t2 = error $ "analyseType: type mismatch: " ++ show (pretty t1) ++ " and " ++ show (pretty t2)

{-
    Annotate
-}

annotateDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> CoreDecl
annotateDeclaration env supply decl@DeclAbstract{} = decl{declType = forallify Nothing $ annotateTypeAbstract env supply (declType decl)}
annotateDeclaration env supply decl@DeclCon{} = decl{declType = forallify Nothing $ annotateTypeAbstract env supply (declType decl)}
annotateDeclaration _ _ decl = decl -- Value is handled outside this method, others don't need anything

{-
    Transform
-}

-- Apply strict annotations on types
transformType :: SolvedConstraints -> Type -> Type
transformType sc (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1)))) t2) =
  TAp (TAp (TCon TConFun) t1') t2'
    where
      a1' = lookupVar a1 sc
      r'  = lookupVar r sc
      a2' = lookupVar a2 sc
      t1' = TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') (transformType sc t1)))
      t2' = transformType sc t2
transformType sc (TAp t1 t2) = TAp (transformType sc t1) (transformType sc t2)
transformType sc (TAnn a) = TAnn $ lookupVarMono a sc
transformType sc (TStrict t) = transformType sc t
transformType sc (TForall q k t) = TForall q k $ transformType sc t
transformType _ t = t

-- Apply strict annotations on expressions
transformExpression :: SolvedConstraints -> BindMap -> Expr -> Expr
transformExpression sc r (Let b e) = Let (transformBinds sc r b) $ transformExpression sc r e
transformExpression sc r (Match i as) = Match i $ map transformAlt as
    where
        transformAlt (Alt p e) = Alt p $ transformExpression sc r e
transformExpression sc r (Ap e1 e2) = Ap e1' e2'
  where
    e1' = transformExpression sc r e1
    e2' = transformExpression sc r e2
transformExpression sc r (ApType e t) = ApType (transformExpression sc r e) t
transformExpression sc r (Lam s v@(Variable x _) e) = Lam s' v e'
  where
     -- Lam can be made strict if it is strict when fully applied, when sa becomes S
    s' = if s then s else lookupVar (findMap x r) sc == S
    e' = transformExpression sc r e
transformExpression sc r (Forall q k e) = Forall q k $ transformExpression sc r e
transformExpression _ _ e = e -- Con, Lit and Var

-- Apply strict transformations on binds
transformBinds :: SolvedConstraints -> BindMap -> Binds -> Binds
transformBinds sc r (Strict (Bind v e)) = Strict $ Bind v (transformExpression sc r e)
transformBinds sc r (NonRec (Bind v@(Variable x _) e)) = b'
  where
    b' = case lookupVar (findMap x r) sc of
        S -> Strict $ Bind v e'
        _ -> NonRec $ Bind v e'
    e' = transformExpression sc r e
transformBinds sc r (Rec bs) = Rec $ map transformBind bs
    where
        transformBind (Bind v e) = Bind v $ transformExpression sc r e

{-
    Instantiate
-}

-- Instantiate expression
instantiateExpression :: TypeEnvironment -> NameSupply -> Expr -> Expr
-- Don't instantiate in the expression as the binding might end up quantified
-- After a let binding, analyseExpression has to call instantiateExpression again
instantiateExpression env supply (Let b e) = Let (instantiateBinds env supply b) e
instantiateExpression env supply (Match x a) = Match x $ mapWithSupply (instantiateAlt env) supply a
instantiateExpression env supply (Ap e1 e2) = Ap e1' e2'
    where
        (supply1, supply2) = splitNameSupply supply
        e1' = instantiateExpression env supply1 e1
        e2' = instantiateExpression env supply2 e2
instantiateExpression env supply (ApType e t) = ApType (instantiateExpression env supply e) t
instantiateExpression env supply (Lam s v e) = Lam s v $ instantiateExpression (typeEnvAddVariable v env) supply e
instantiateExpression env supply (Forall q k e) = Forall q k $ instantiateExpression env supply e
instantiateExpression env supply e@(Var v) = instantiate env supply v e
instantiateExpression env supply e@(Con (ConId c)) = instantiate env supply c e
instantiateExpression _ _ e = e

-- Instantiate binds
instantiateBinds :: TypeEnvironment -> NameSupply -> Binds -> Binds
instantiateBinds env supply (Strict b) = Strict $ instantiateBind env supply b
instantiateBinds env supply (NonRec b) = NonRec $ instantiateBind env supply b
instantiateBinds env supply b@(Rec bs) = Rec $ mapWithSupply (instantiateBind env') supply bs
    where
        env' = typeEnvAddBinds b env

-- Instantiate bind
instantiateBind :: TypeEnvironment -> NameSupply -> Bind -> Bind
instantiateBind env supply (Bind (Variable x t) e) = Bind (Variable x t) $ instantiateExpression env supply e

-- Instantiate alt
instantiateAlt :: TypeEnvironment -> NameSupply -> Alt -> Alt
instantiateAlt env supply (Alt p e) = Alt p' e'
    where
        (supply1, supply2) = splitNameSupply supply
        p' = instantiatePat env supply1 p
        e' = instantiateExpression (typeEnvAddPattern p' env) supply2 e

-- Instantiate pat  
instantiatePat :: TypeEnvironment -> NameSupply -> Pat -> Pat
instantiatePat env supply (PatCon (ConTuple n) ts i) = PatCon (ConTuple n) t' i
    where
        -- Place three ids, but L as datatypes are not supported
        t' = mapWithSupply (\s t -> TAp (TAnn L) (TAp (TAnn L) (TAp (TAnn L) (annotateType env s t)))) supply ts
instantiatePat env supply (PatCon (ConId c) ts i) = PatCon (ConId c) t' i
    where
        (supply1, supply2) = splitNameSupply supply
        -- Add more ids for the extra foralls
        t' = map (TAnn . AnnVar) ids ++ mapWithSupply (annotateType env) supply1 ts
        ids = mapWithSupply (\x _ -> fst $ freshId x) supply2 n
        n = getForalls env $ typeOfId env c
instantiatePat _ _ p = p

-- Instantiate variable or constructor
instantiate :: TypeEnvironment -> NameSupply -> Id -> Expr -> Expr
instantiate env supply i e = foldr (\x e' -> ApType e' (TAnn (AnnVar x))) e ids
    where
        -- Get all foralls, add an ApType with fresh variable
        ids = mapWithSupply (\x _ -> fst $ freshId x) supply $ getForalls env (typeOfId env i)

{-
    Simplification
-}

-- Solve part of the constraint set in a let-binding
simplify :: IdSet -> Constraints -> AnnotationEnvironment -> Analysis ()
simplify is cs ae = Analysis () (S.map (mapConstraint sc) rc) (mapMap (replaceVar sc) ra) sc emptyMap
    where
        -- Partition constraint in those allowed to be solved and not
        (lc, rc) = S.partition (blockedConstraint is) cs
        -- Partition annotation environment in those allowed to be solved and not
        (la, ra) = partitionMapWithId (\i _ -> i `elemSet` is) ae
        sc = solveConstraints la lc

-- Simplify the type of a bind
simplifyBind :: IdSet -> SolvedConstraints -> Bind -> Bind
simplifyBind is sc (Bind (Variable x (TAp a1 (TAp r (TAp a2 t)))) e) = Bind (Variable x t') e
  where
    -- Get type of binding, apply solved constraints and forallify
    t' = TAp a1 $ TAp r $ TAp a2 $ forallify (Just is) $ simplifyType sc t

-- Simplify type signatures
simplifyType :: SolvedConstraints -> Type -> Type
simplifyType sc (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1)))) t2) =
  TAp (TAp (TCon TConFun) t1') t2'
    where
      a1' = lookupVar a1 sc
      r'  = lookupVar r sc
      a2' = lookupVar a2 sc
      t1' = TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') (simplifyType sc t1)))
      t2' = simplifyType sc t2
simplifyType sc (TAp t1 t2) = TAp (simplifyType sc t1) (simplifyType sc t2)
simplifyType sc (TAnn a) = TAnn $ lookupVar a sc
simplifyType sc (TStrict t) = simplifyType sc t
simplifyType sc (TForall q k t) = TForall q k $ simplifyType sc t
simplifyType _ t = t

getVariablesBind :: Bind -> IdSet
getVariablesBind (Bind (Variable _ (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) _)))) e) = unionSet i1 i2
    where
        i1 = getVariablesExpr e
        i2 = insertSet' [a1, r , a2]

getVariablesExpr :: Expr -> IdSet
getVariablesExpr (Let b e) = unionSet (getVariablesBinds b) (getVariablesExpr e)
getVariablesExpr (Match _ as) = unionSets (map getVariablesAlt as)
getVariablesExpr (Ap e1 e2) = unionSet (getVariablesExpr e1) (getVariablesExpr e2)
getVariablesExpr (ApType e _) = getVariablesExpr e
getVariablesExpr (Lam _ (Variable _ (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) _)))) e) = unionSets [getVariablesExpr e, insertSet' [a1, r, a2]]
getVariablesExpr (Forall _ _ e) = getVariablesExpr e
getVariablesExpr (Con _) = emptySet
getVariablesExpr (Var _) = emptySet
getVariablesExpr (Lit _) = emptySet

getVariablesBinds :: Binds -> IdSet
getVariablesBinds (Rec bs) = unionSets $ map getVariablesBind bs
getVariablesBinds (NonRec b) = getVariablesBind b
getVariablesBinds (Strict b) = getVariablesBind b

getVariablesAlt :: Alt -> IdSet
getVariablesAlt (Alt _ e) = getVariablesExpr e

insertSet' :: [SAnn] -> IdSet
insertSet' = setFromList . map fromAnn . filter isAnn
