module Helium.CodeGeneration.Core.Strictness.PolyvariantAdvanced (polyvariantStrictness) where

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

type GroupData = (ValueMap, TypeEnvironment, NameSupply)
type CoreGroup = BindingGroup Expr

polyvariantStrictness :: NameSupply -> CoreModule -> CoreModule
polyvariantStrictness supply mod = mod {moduleDecls = map (setValue values') $ moduleDecls mod}
  where
    (supply1, supply2) = splitNameSupply supply
    -- Ignore declarations which have already been analysed
    (decls1, decls2) = partition (any isCustomAnn . declCustoms) $ moduleDecls mod
    -- Split module in functions and others (constructors, abstract, synonyms)
    (values, others) = partition isDeclValue decls2
    -- For declarations which have been annotated, set strictness type to declType
    decls1' = map setStrictnessType decls1
    -- Annotate others
    others' = mapWithSupply (annotateDeclaration (typeEnvForModule mod)) supply1 others
    -- Create starting environment
    env' = typeEnvForModule mod{moduleDecls = others' ++ decls1'}
    -- Binding group analysis for functions
    groups = coreBindingGroups values
    (values', _, _) = foldl groupStrictness (emptyMap, env', supply2) groups

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
    t' = forallify Nothing $ transformType sc $ typeOfCoreExpression env e
    -- Add function to environment for next function
    env' = typeEnvAddGlobalValue (declName d) t' env
    -- Add new value
    v' = insertMap (declName d) (e', t') v
-- Group of recursive declarations
groupStrictness (vs, env, supply) (BindingRecursive ds) = (vs', env'', supply2)
  where
    (supply1, supply2) = splitNameSupply supply
    -- Annotate type signatures and add them to the envorinment
    ts = map (annotateTypeRec env . declType) ds
    env' = typeEnvAddGlobalValues (map (\(d, t) -> (declName d, t)) (zip ds ts)) env
    -- Run analysis on all bodies, merge information with meet
    Analysis es cs ae sc1 r = mergeAnalysis meet $ mapWithSupply (analyseDeclaration env') supply1 ds
    -- Solve constraints
    sc2 = solveConstraints ae cs
    sc3 = mapMap (replaceVar sc2) sc1
    sc = unionMap sc2 sc3
    -- Transform all expressions using solved constraints
    es' = map (transformExpression sc r . valueValue) ds
    -- Get types from body, apply solved constraints and forallify
    ts' = map (forallify Nothing . transformType sc . typeOfCoreExpression env') es
    -- Add types to environment for next functions
    env'' = typeEnvAddGlobalValues (map (\(d, t) -> (declName d, t)) (zip ds ts')) env
    -- Add new values
    vs' = foldl (\v (d, e, t) -> insertMap (declName d) (e, t) v) vs $ zip3 ds es' ts'

{-
    Analyse
-}

analyseDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> Analysis Expr
analyseDeclaration typeEnv supply decl@DeclValue{} = analyseExpression env S S supply2 ie
    where
        (supply1, supply2) = splitNameSupply supply
        -- Instantiate forallified expressions
        ie = instantiateExpression typeEnv supply1 $ valueValue decl
        env = Environment typeEnv emptyMap emptyMap

analyseExpression :: Environment -> SAnn -> SAnn -> NameSupply -> Expr -> Analysis Expr
analyseExpression env rel app supply (Let b e) = Analysis (Let b' e') cs (unionMapWith meet a1 as) (unionMap sc1 sc2) (unionMap r1 r2)
    where
        (supply1, supply') = splitNameSupply supply
        (supply2, supply3) = splitNameSupply supply'
        -- Analyse binds
        (Analysis b' c1 a1 sc1 r1, app') = analyseBinds env supply1 rel b
        -- Add annotated binds to environment
        env' = envAddBinds b' env
        -- Instantiate quantified functions
        e1 = instantiateExpression (typeEnv env') supply2 e
        -- Analyse body, set contexts to S
        Analysis e' c2 a2 sc2 r2 = analyseExpression env' S S supply3 e1
        -- Containment on old environment
        as = unionMapWith join a2 $ containment env app
        -- Add constraint on applicativeness
        cs = S.insert (app `Constraint` app') $ S.union c1 c2
analyseExpression env rel app supply (Match id a) = Analysis (Match id a') c ae sc r
    where
        -- Merge with join as strictness has to occur in every case
        Analysis a' c ae sc r = mergeAnalysis join $ mapWithSupply (analyseAlt env rel app id) supply a
analyseExpression env rel app supply (Ap e1 e2) = Analysis (Ap e1' e2') cs (unionMapsWith meet [ae1, ae2, ae3]) (unionMap sc1 sc2) (unionMap r1 r2)
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse function, with applicative context set to relevance
        Analysis e1' c1 ae1 sc1 r1 = analyseExpression env rel app supply1 e1
        -- Get type of function
        t = typeNormalizeHead (typeEnv env) $ typeOfCoreExpression (typeEnv env) e1'
        -- Get the annotations on the function arrow
        (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t')))) _) = t
        -- Analyse argument with context of the previous annotations
        Analysis e2' c2 ae2 sc2 r2 = analyseExpression env (join rel r) (join rel a1) supply2 e2
        -- Annotation unifications between the function and the given argument
        (ae3, c3) = analyseType env t' $ typeOfCoreExpression (typeEnv env) e2'
        -- Add constraint on applicativeness
        cs = S.insert (app `Constraint` a2) $ S.unions [c1, c2, c3]
analyseExpression env rel app supply (ApType e t) = Analysis (ApType e' t') c a sc r
    where
        (supply1, supply2) = splitNameSupply supply
        -- Annotate type, if it is a tuple place extra annotations
        t' = if isTupAp e then annotateVarType env supply1 t else annotateType (typeEnv env) supply1 t
        -- Analyse expression
        Analysis e' c a sc r = analyseExpression env rel app supply2 e
analyseExpression env _ app supply (Lam s (Variable x t) e) = Analysis (Lam s v' e') c a' sc r'
    where
        (id1, id2, id3, supply') = threeIds supply
        (supply1, supply2) = splitNameSupply supply'
        -- Annotate type in variable
        t' = annotateType (typeEnv env) supply1 t
        -- If lambda was strict, set its annotation variables equal to S
        ann1 = if s then S else AnnVar id1
        ann2 = if s then S else AnnVar id2
        -- Give extra annotation to variable
        v' = Variable x (TAp (TAnn ann1) (TAp (TAnn ann2) (TAp (TAnn $ AnnVar id3) t')))
        -- Add variable to environment
        env' = envAddVariable v' env
        -- Analyse expression, set relevance to S and context to 0
        Analysis e' c a sc r = analyseExpression env' S (AnnVar id3) supply2 e
        -- Containment on old environment
        a' = unionMapWith join a $ containment env app
        -- If not strict, add variable to map which might turn to strict
        r' = if s then r else insertMap x (Join (AnnVar id1) (AnnVar id2)) r
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

analyseBinds :: Environment -> NameSupply -> SAnn -> Binds -> (Analysis Binds, SAnn)
analyseBinds env supply rel (Rec bs) = (Analysis (Rec b1) cs ae (unionMap sc sc') r, foldr join S app)
    where
        (supply1, supply2) = splitNameSupply supply
        -- Annotate types beforehand because they occur in the body
        bs''= mapWithSupply (annotateBind env) supply1 bs
        -- Add binds to environment
        env' = envAddBinds (Rec bs'') env
        -- Run analysis on every bind separately
        (xs, app, is') = unzip3 $ mapWithSupply (analyseRecBind env' rel) supply2 bs''
        -- Merge the results with meet, as being strict in one bind is enough
        Analysis bs' c a sc' r = mergeAnalysis meet xs
        -- Calculate set of annotation variables which can be solved
        is = diffSet (unionSets $ map getVariablesBind bs') (unionSets is')
        -- Run simplifier to get solved local constraints
        Analysis _ cs ae sc _ = simplify is c a
        -- Apply solved constraints to get type signatures for all binds
        b1 = map (simplifyBind env' is sc) bs'
analyseBinds env supply rel (NonRec (Bind (Variable x _) e)) = (Analysis (NonRec b) cs' ae' (unionMap sc sc') r', AnnVar id3)
    where
        -- Fresh variable for relevance annotation
        (id1, id2, id3, supply') = threeIds supply
        -- Run analysis on binding with relevance set to context
        Analysis e' cs ae sc r = analyseExpression env (join rel (AnnVar id2)) (join rel (AnnVar id1)) supply' e
        -- Calculate set of annotation variables which can be solved
        is = getVariablesExpr e'
        -- Run simplifier to get solved local constraints
        Analysis _ cs' ae' sc' _ = simplify is cs ae
        -- Apply solved constraints to get type signature for bind
        t' = forallify (Just is) $ transformType sc' $ typeOfCoreExpression (typeEnv env) e'
        -- Add annotations outside the type
        b = Bind (Variable x (TAp (TAnn $ AnnVar id1) (TAp (TAnn $ AnnVar id2) (TAp (TAnn $ AnnVar id3) t')))) e'
        -- Bind is NonRec, add to map of those which might be turned to strict
        r' = insertMap x (Join (AnnVar id1) (AnnVar id2)) r
analyseBinds env supply rel (Strict (Bind (Variable x _) e)) = (Analysis (Strict b) cs' ae' (unionMap sc sc') r, AnnVar id)
    where
        -- Fresh variables for relevance and both applicativeness
        (id, supply') = freshId supply
        -- Run analysis on binding with relevance set to context
        Analysis e' cs ae sc r = analyseExpression env rel rel supply' e   
        -- Calculate set of annotation variables which can be solved
        is = getVariablesExpr e'
        -- Run simplifier to get solved local constraints
        Analysis _ cs' ae' sc' _ = simplify is cs ae
        -- Apply solved constraints to get type signature for bind
        t' = forallify (Just is) $ transformType sc' $ typeOfCoreExpression (typeEnv env) e'
        -- Add annotations outside the type
        b = Bind (Variable x (TAp (TAnn S) (TAp (TAnn S) (TAp (TAnn (AnnVar id)) t')))) e'

analyseRecBind :: Environment -> SAnn -> NameSupply -> Bind -> (Analysis Bind, SAnn, IdSet)
analyseRecBind env rel supply (Bind v e) = (Analysis (Bind v e') c a sc r, a2, getVariablesType True t)
    where
        -- Get annotation from variable previously annotated
        Variable _ t@(TAp (TAnn a1) (TAp (TAnn rel') (TAp (TAnn a2) _))) = v
        -- Run analysis on binding with relevance set to context
        Analysis e' c a sc r = analyseExpression env (join rel rel') (join rel a1) supply e 
        
analyseAlt :: Environment -> SAnn -> SAnn -> Id -> NameSupply -> Alt -> Analysis Alt
analyseAlt env rel app id supply (Alt p e) = Analysis (Alt p' e') (S.union c1 c2) (unionMapWith meet a1 a2) sc r
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse the pattern
        Analysis p' c1 a1 _ _ = analysePat env id supply1 p
        -- Add pattern to environment
        env' = envAddPattern p' env
        -- Run analysis 
        Analysis e' c2 a2 sc r = analyseExpression env' rel app supply2 e

analysePat :: Environment -> Id -> NameSupply -> Pat -> Analysis Pat
analysePat env id supply (PatCon (ConTuple n) t i) = Analysis (PatCon (ConTuple n) t' i) cs ae emptyMap emptyMap
    where
        -- In case of a tuple, all types need three extra annotations to communicate the return annotations of the tuple
        t' = mapWithSupply (annotateVarType env) supply t
        -- Get equalities between type of id matched on and type of pattern
        (ae, cs) = analyseType env (typeOfId (typeEnv env) id) (foldl TAp (TCon (TConTuple n)) t')
analysePat env id supply (PatCon c t i) = Analysis (PatCon c t' i) cs ae emptyMap emptyMap
    where
        -- Annotate all types given to constructor
        t' = mapWithSupply (annotateType (typeEnv env)) supply t
        -- Add pattern to environment
        env' = envAddPattern (PatCon c t' i) env
        -- Construct expression equivalent to constructor
        e = foldl Ap (foldl ApType (Con c) t') (map Var i)
        -- Analyse type of matched id with type of constructor
        (ae, cs) = analyseType env (typeOfId (typeEnv env) id) (typeOfCoreExpression (typeEnv env') e)
analysePat _ _ _ p = Analysis p S.empty emptyMap emptyMap emptyMap -- Literal or default, no information to be gained

-- Analyse type
analyseType :: Environment -> Type -> Type -> (AnnotationEnvironment, Constraints)
analyseType env t1 t2
    | t1 /= t1' || t2 /= t2' = analyseType env t1' t2' -- Normalization changes types, try again
    | t1 == t2               = (emptyMap, S.empty) -- Types equal, analysis completed
        where
            t1' = typeNormalizeHead (typeEnv env) t1
            t2' = typeNormalizeHead (typeEnv env) t2
analyseType env (TAp (TAp (TCon TConFun) t11) t12) (TAp (TAp (TCon TConFun) t21) t22) = (unionMapWith join ae1 ae2, cs)
    -- Function arrows, analyse every pair of annotations on them
  where
    (TAp (TAnn a1 ) (TAp (TAnn r ) (TAp (TAnn a2 ) t1'))) = t11
    (TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') t2'))) = t21
    (ae1, c1) = analyseType env t1' t2'
    (ae2, c2) = analyseType env t12 t22
    cs = S.insert (a1' `Constraint` a1) $ S.insert (r' `Constraint` r) $ S.insert (a2' `Constraint` a2) $ S.union c1 c2
-- analyseType env (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) t1)))))) t2 = analyseType env t1' t2
--     -- Double annotations in case of newtypes. Since they are strict by design we can forget them and place S
--     where
--         t1' = TAp (TAnn S) (TAp (TAnn S) (TAp (TAnn S) t1))
-- analyseType env t1 (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) t2)))))) = analyseType env t1 t2'
--     -- Double annotations in case of newtypes. Since they are strict by design we can forget them and place S
--     where
--         t2' = TAp (TAnn S) (TAp (TAnn S) (TAp (TAnn S) t2))
analyseType env (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1)))
       (TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') t2))) = (unionMapsWith join [ae1, ae2, ae3, ae4], cs)
    -- Annotations on datatypes, evaluate per pair
    where
        ae1 = analyseAnn a1 a1'
        ae2 = analyseAnn r r'
        ae3 = analyseAnn a2 a2'
        (ae4, cs) = analyseType env t1 t2
analyseType env (TAp t11 t12) (TAp t21 t22) = (unionMapWith join ae1 ae2, S.union c1 c2)
    -- Unannotated applications
    where
        (ae1, c1) = analyseType env t11 t21
        (ae2, c2) = analyseType env t12 t22
analyseType env (TForall _ _ t1) (TForall _ _ t2) = analyseType env t1 t2
analyseType env (TStrict t1) t2 = analyseType env t1 t2
analyseType env t1 (TStrict t2) = analyseType env t1 t2 -- Remove all strict type information
analyseType _ (TVar _) (TVar _) = (emptyMap, S.empty) -- Lift has a bug which might distort type variables, exact index doesn't matter
analyseType _ t1 t2 = error $ "analyseType: type mismatch: " ++ show (pretty t1) ++ " and " ++ show (pretty t2)

analyseAnn :: SAnn -> SAnn -> AnnotationEnvironment
analyseAnn (AnnVar x) y = singleMap x y
analyseAnn x (AnnVar y) = singleMap y x
analyseAnn _ _ = emptyMap

{-
    Annotate
-}

annotateDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> CoreDecl
annotateDeclaration env supply decl@DeclAbstract{} = decl{declType = fst $ annotateTypeAbstract env supply (declType decl)}
annotateDeclaration env supply decl@DeclCon{} = decl{declType = fst $ annotateTypeAbstract env supply (declType decl)}
-- annotateDeclaration env supply decl@DeclTypeSynonym{}
--     -- String is the only type synonym which has to be annotated because it is partly hardcoded in the type system
--     | declName decl == idFromString "String" = decl{declType = forallify Nothing $ annotateType env supply (declType decl)}
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
transformType sc (TAnn a) = TAnn $ lookupVar a sc
transformType sc (TStrict t) = transformType sc t
transformType sc (TForall q k t) = TForall q k $ transformType sc t
transformType _ t = t

-- Apply strict annotations on expressions
transformExpression :: SolvedConstraints -> BindMap -> Expr -> Expr
transformExpression sc r (Let b e) = Let (transformBinds sc r b) $ transformExpression sc r e
transformExpression sc r (Match id as) = Match id $ map transformAlt as
    where
        transformAlt (Alt p e) = Alt p $ transformExpression sc r e
transformExpression sc r (Ap e1 e2) = Ap e1' e2'
  where
    e1' = transformExpression sc r e1
    e2' = transformExpression sc r e2
transformExpression sc r (ApType e t) = ApType (transformExpression sc r e) t
transformExpression sc r (Lam s v@(Variable x _) e) = Lam s' v e'
  where
    (Join a' r') = findMap x r
    (sa, sr) = (lookupVar a' sc, lookupVar r' sc)
     -- Lam can be made strict if it is strict when fully applied, when sa becomes S
    s' = if s then s else uncontain (getVariablesAnn sa) sr == S
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
-- instantiateExpression _ supply e@(Lit (LitBytes _)) = e'
--     where
--         -- String is stored as type synonym forall a b c -> [a b c Char]
--         -- Add annotations to make them unique
--         (id1, id2, id3, _) = threeIds supply
--         is = [id1, id2, id3]
--         e' = foldl (\e'' i -> ApType e'' (TAnn (AnnVar i))) e is
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
instantiatePat env supply (PatCon (ConId c) t i) = PatCon (ConId c) t' i
    where
        -- Add more ids for the extra foralls
        t' = map (TAnn . AnnVar) ids ++ t
        ids = mapWithSupply (\x _ -> fst $ freshId x) supply n
        n = getForalls env $ typeOfId env c
instantiatePat _ _ p = p

-- Instantiate variable or constructor
instantiate :: TypeEnvironment -> NameSupply -> Id -> Expr -> Expr
instantiate env supply id e = foldr (\x e' -> ApType e' (TAnn (AnnVar x))) e ids
    where
        -- Get all foralls, add an ApType with fresh variable
        ids = mapWithSupply (\x _ -> fst $ freshId x) supply $ getForalls env (typeOfId env id)

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
        (la, ra) = partitionMapWithId (\id _ -> id `elemSet` is) ae
        sc = solveConstraints la lc

-- Simplify the type of a bind
simplifyBind :: Environment -> IdSet -> SolvedConstraints -> Bind -> Bind
simplifyBind env is sc (Bind (Variable x (TAp a1 (TAp r (TAp a2 _)))) e) = Bind (Variable x t'') e
  where
    -- Get type of binding, apply solved constraints and forallify
    t' = forallify (Just is) $ transformType sc $ typeOfCoreExpression (typeEnv env) e
    -- Reinstate annotations belonging to variable itself which are yet to be answered
    t'' = TAp a1 $ TAp r $ TAp a2 t'

getVariablesBind :: Bind -> IdSet
getVariablesBind (Bind (Variable _ (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t)))) e) = unionSets [i1, i2, i3]
    where
        i1 = getVariablesType False t
        i2 = getVariablesExpr e
        i3 = insertSet' [a1, r , a2]

getVariablesExpr :: Expr -> IdSet
getVariablesExpr (Let b e) = unionSet (getVariablesBinds b) (getVariablesExpr e)
getVariablesExpr (Match _ as) = unionSets (map getVariablesAlt as)
getVariablesExpr (Ap e1 e2) = unionSet (getVariablesExpr e1) (getVariablesExpr e2)
getVariablesExpr (ApType e t) = unionSet (getVariablesExpr e) (getVariablesType False t)
getVariablesExpr (Lam _ (Variable _ (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t)))) e)
    = unionSets [getVariablesType False t, getVariablesExpr e, insertSet' [a1, r, a2]]
getVariablesExpr (Forall _ _ e) = getVariablesExpr e
getVariablesExpr (Con _) = emptySet
getVariablesExpr (Var _) = emptySet
getVariablesExpr (Lit _) = emptySet

getVariablesBinds :: Binds -> IdSet
getVariablesBinds (Rec bs) = unionSets $ map getVariablesBind bs
getVariablesBinds (NonRec b) = getVariablesBind b
getVariablesBinds (Strict b) = getVariablesBind b

getVariablesAlt :: Alt -> IdSet
getVariablesAlt (Alt p e) = unionSet (getVariablesPat p) (getVariablesExpr e)

getVariablesPat :: Pat -> IdSet
getVariablesPat (PatCon _ t _) = unionSets $ map (getVariablesType False) t
getVariablesPat _ = emptySet

insertSet' :: [SAnn] -> IdSet
insertSet' = setFromList . map fromAnn . filter isAnn
