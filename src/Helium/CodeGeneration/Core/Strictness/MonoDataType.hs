module Helium.CodeGeneration.Core.Strictness.MonoDataType (monovariantStrictness) where

import Data.List
import qualified Data.Set as S

import Helium.CodeGeneration.Core.BindingGroup
import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.Strictness.Solve
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

import Text.PrettyPrint.Leijen (pretty)

-- Analysis data type, containing return expression, set of constraints and the environment containing the annotations
data Analysis a = Analysis a Constraints AnnotationEnvironment BindMap IdSet

mergeAnalysis :: (SAnn -> SAnn -> SAnn) -> [Analysis a] -> Analysis [a]
mergeAnalysis _ []     = Analysis [] S.empty emptyMap emptyMap emptySet
mergeAnalysis f (x:xs) = Analysis (v : v') (S.union c c') (unionMapWith f a a') (unionMap r r') (unionSet s s')
    where
        Analysis v c a r s = x
        Analysis v' c' a' r' s' = mergeAnalysis f xs

type GroupData = (PolyMap, TypeEnvironment, NameSupply)
type CoreGroup = BindingGroup Expr

monovariantStrictness :: NameSupply -> CoreModule -> CoreModule
monovariantStrictness supply m = m{moduleDecls = map (setValue (annotateTypeAbstract env supply3) values') $ moduleDecls m}
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
    Analysis t cs ae r is = analyseDeclaration env supply1 d
    -- Solve constraints
    sc = solveConstraints ae cs
    -- Apply transformations on type
    t' = transformType sc t
    -- Get applicativeness annotation to use in solving lambdas
    anns = unionSet is $ getApplicatives t'
    -- Transform expression using solved constraints
    e' = transformExpression sc anns r $ valueValue d
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
    Analysis ts' cs ae r is = mergeAnalysis meet $ mapWithSupply (analyseDeclaration env') supply2 ds
    -- Analyse type to solve the annotations which where put there at the beginning
    cs2 = zipWith (analyseType2 env) ts ts'
    -- Solve constraints
    sc = solveConstraints ae (S.union cs (S.unions cs2))
    -- Apply solved constraints to types
    ts'' = map (transformType sc) ts'
    -- Get applicativeness annotation to use in solving lambdas
    anns = map (unionSet is . getApplicatives) ts''
    -- Transform all expressions using solved constraints
    es' = map (\(d, a) -> transformExpression sc a r $ valueValue d) (zip ds anns)
    -- Add types to environment for next functions
    env'' = typeEnvAddGlobalValues (map (\(d, t) -> (declName d, t)) (zip ds ts'')) env
    -- Add new values
    vs' = foldl (\v (d, e, t) -> insertMap (declName d) (e, t) v) vs $ zip3 ds es' ts''
groupStrictness d (BindingNonFunction _) = d -- Split occurs before binding group analysis

{-
    Analyse
-}

analyseDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> Analysis Type
analyseDeclaration tyEnv supply decl@DeclValue{} = analyseExpression env S (AnnVar i) supply' $ valueValue decl
    where
        (i, supply') = freshId supply
        env = Environment tyEnv emptyMap emptyMap

analyseExpression :: Environment -> SAnn -> SAnn -> NameSupply -> Expr -> Analysis Type
analyseExpression env rel app supply (Let b e) = Analysis t (S.union c1 c2) (unionMapWith meet a1 as) (unionMap r1 r2) (unionSet i1 i2)
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse binds
        Analysis env' c1 a1 r1 i1 = analyseBinds env supply1 rel b
        -- Analyse body, set context to S
        Analysis t c2 a2 r2 i2 = analyseExpression env' S app supply2 e
        -- Containment on old environment
        as = containment env rel a2
analyseExpression env rel app supply (Match i a) = Analysis tr cs (unionMapWith meet ae1 ae2) r is
    where
        Analysis _ _ ae1 _ _ = analyseExpression env S app supply (Var i)
        -- Merge with join as strictness has to occur in every case
        Analysis (t:ts) cs ae2 r is = mergeAnalysis join $ mapWithSupply (analyseAlt env rel app i) supply a
        tr = foldl unifyAnnotations t ts
analyseExpression env rel app supply (Ap e1 e2) = Analysis tr cs (unionMapsWith meet [ae1, ae2, ae3]) (unionMap r1 r2) (unionSet i1 i2)
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse function, with applicative context set to relevance
        Analysis t1 c1 ae1 r1 i1 = analyseExpression env rel rel supply1 e1
        -- Get the annotations on the function arrow
        (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1')))) tr) = t1
        -- Analyse argument with context of the previous annotations
        Analysis t2 c2 ae2 r2 i2 = analyseExpression env (join rel r) (join rel a1) supply2 e2
        -- Unifications between the function and the given argument
        (c3, ae3) = analyseType (typeEnv env) t1' t2
        -- Add constraint on applicativeness
        cs = S.insert (app `Constraint` a2) $ S.unions [c1, c2, c3]
analyseExpression env rel app supply (ApType e t) = Analysis (typeApply t' t'') cs ae r i
    where
        (supply1, supply2) = splitNameSupply supply
        -- Annotate type
        t'' | isNil e = annotateTypeMax (typeEnv env) t
            | otherwise = annotateType (typeEnv env) supply1 t
        -- Analyse expression
        Analysis t' cs ae r i = analyseExpression env rel app supply2 e
analyseExpression env _ app supply (Lam s (Variable x t) e) = Analysis tr c a' r' i
    where
        (id1, id2, id3, supply') = threeIds supply
        (supply1, supply2) = splitNameSupply supply'
        -- If lambda was strict, set its annotation variable equal to S
        ann2 = if s then S else AnnVar id2
        -- Annotate type in variable
        t' = TAp (TAnn $ AnnVar id1) (TAp (TAnn ann2) (TAp (TAnn $ AnnVar id3) (annotateType (typeEnv env) supply1 t)))
        -- Add variable to environment
        env' = envAddVariable (Variable x t') env
        -- Analyse expression, set relevance to S
        Analysis tb c a r i = analyseExpression env' S (AnnVar id3) supply2 e
        -- Containment on old environment
        a' = containment env app a
        -- If not strict, add variable to map which might turn to strict
        r' = if s then r else insertMap x (AnnVar id2) r
        -- Type of lambda is a function
        tr = TAp (TAp (TCon TConFun) t') tb
analyseExpression env rel app supply (Forall q k e) = Analysis (TForall q k t) c a r i
    where
        Analysis t c a r i = analyseExpression env rel app supply e
analyseExpression env _ _ supply (Con (ConId c))
    | stringFromId c == ":" = Analysis tc S.empty (getLConstraints env) emptyMap emptySet
    | otherwise = Analysis t S.empty (getLConstraints env) emptyMap emptySet -- Set all annotation variables to L
        where
            t = typeOfId (typeEnv env) c
            tc = annotateCons supply t
analyseExpression env _ _ supply (Con (ConTuple n)) = Analysis t S.empty (getLConstraints env) emptyMap emptySet
    where
        t = annotateTuple [] supply (typeTuple n)
analyseExpression env rel app _ (Var v) = Analysis (typeOfId (typeEnv env) v) S.empty (unionMapWith meet (getLConstraints env) ae) emptyMap emptySet
    where
        -- Set all annotation variables to L except the annotations related to this variable, which are set to context
        ae = getAnnotations env rel app v
analyseExpression env _ _ supply (Lit l) = Analysis t S.empty (getLConstraints env) emptyMap emptySet -- Set all annotation variables to L
    where
        (i, _) = freshId supply
        tl = TCon $ TConDataType $ idFromString "[]"
        tc = TCon $ TConDataType $ idFromString "Char"
        t = case l of
                -- Manual string override to place annotation
                LitBytes _ -> TAp (TAp (TAnn $ AnnVar i) tl) tc
                _ -> typeOfLiteral l
analyseBinds :: Environment -> NameSupply -> SAnn -> Binds -> Analysis Environment
analyseBinds env supply rel (Rec bs) = Analysis env'' c a r i
    where
        -- Annotate types beforehand because they occur in the body
        bs' = mapWithSupply (annotateBind env) supply bs
        -- Add binds  to environment
        env' = envAddBinds (Rec bs') env
        -- Run analysis on every bind separately
        xs = mapWithSupply (analyseRecBind env' rel) supply bs'
        -- Merge the results with meet, as being strict in one bind is enough
        Analysis vs c a r i = mergeAnalysis meet xs
        env'' = foldr envAddVariable env vs 
analyseBinds env supply rel (NonRec (Bind (Variable x _) e)) = Analysis env' cs ae r' is'
    where
        -- Fresh variable for relevance annotation
        (id1, id2, _, supply') = threeIds supply
        -- Run analysis on binding with relevance set to context
        Analysis t' cs ae r is = analyseExpression env (join rel (AnnVar id2)) (join rel (AnnVar id1)) supply' e
        -- Bind is NonRec, add to map of those which might be turned to strict
        r' = insertMap x (AnnVar id2) r
        -- Add bind to environment
        env' = envAddVariable (Variable x (TAp (TAnn $ AnnVar id1) (TAp (TAnn $ AnnVar id2) (TAp (TAnn S) t')))) env
        -- Get applicativeness annotation to use in solving lambdas
        is' = unionSet is $ getApplicatives t'
analyseBinds env supply rel (Strict (Bind (Variable x _) e)) = Analysis env' cs ae r is'
    where
        -- Fresh variables for second applicativeness
        (i, supply') = freshId supply
        -- Run analysis on binding with relevance set to context
        Analysis t' cs ae r is = analyseExpression env rel (join rel (AnnVar i)) supply' e
        -- Add bind to environment
        env' = envAddVariable (Variable x (TAp (TAnn $ AnnVar i) (TAp (TAnn S) (TAp (TAnn S) t')))) env
        -- Get applicativeness annotation to use in solving lambdas
        is' = unionSet is $ getApplicatives t'

analyseRecBind :: Environment -> SAnn -> NameSupply -> Bind -> Analysis Variable
analyseRecBind env rel supply (Bind v e) = Analysis (Variable x t'') (S.union cs1 cs2) ae r is'
    where
        -- Get annotations from variable previously annotated
        Variable x (TAp (TAnn a1) (TAp (TAnn rel') (TAp (TAnn a2) t))) = v
        -- Run analysis on binding with relevance and applicative joined with context
        Analysis t' cs1 ae r is = analyseExpression env (join rel rel') (join rel a1) supply e
        t'' = TAp (TAnn a1) (TAp (TAnn rel') (TAp (TAnn a2) t'))
        -- As recursive binding, find the new values for the placed annotations
        cs2 = analyseType2 (typeEnv env) t t'
        -- Get applicativeness annotation to use in solving lambdas
        is' = unionSet is $ getApplicatives t''

analyseAlt :: Environment -> SAnn -> SAnn -> Id -> NameSupply -> Alt -> Analysis Type
analyseAlt env rel app i supply (Alt p e) = Analysis t (S.union c c') (unionMapWith meet ae1 ae2) r is
    where
        (supply1, supply2) = splitNameSupply supply
        (c, ae1, vs) = analysePat (typeEnv env) supply1 p (typeOfId (typeEnv env) i)
        -- Run analysis
        Analysis t c' ae2 r is = analyseExpression (envAddVariables vs env) rel app supply2 e

analysePat :: TypeEnvironment -> NameSupply -> Pat -> Type -> (Constraints, AnnotationEnvironment, [Variable])
analysePat env supply (PatCon (ConTuple n) ts is) tx = (cs, ae, patternVariables env p')
    where
        (ts', anns) = unzip $ mapWithSupply (annotateTuplePat env) supply ts
        p' = PatCon (ConTuple n) ts' is
        t = foldl TAp (foldr (\i' t' -> TAp (TAnn i') t') (TCon (TConTuple n)) anns) (map typeNotAnnotated ts')
        (cs, ae) = analyseType env t tx
analysePat env supply (PatCon (ConId c) ts is) tx | stringFromId c /= ":" = (cs, ae, patternVariables env p')
    where
        t' | isNil (Con (ConId c)) = map (annotateTypeMax env) ts -- Empty list, annotate as best as possible
           | otherwise = mapWithSupply (annotateType env) supply ts -- Annotate all types given to constructor
        p' = PatCon (ConId c) t' is
        t1 = typeNormalizeHead env $ foldl TAp (typeOfId env c) t'
        t3 = constructorType t1
        (cs, ae) = analyseType env t3 tx
analysePat env supply (PatCon (ConId c) ts is) tx = (cs, ae, findVars is t1)
    where
        (supply1, supply2) = splitNameSupply supply
        t' = mapWithSupply (annotateType env) supply1 ts -- Annotate all types given to constructor
        t = annotateCons supply2 (typeOfId env c)
        t1 = typeNormalizeHead env $ foldl TAp t t'
        findVars :: [Id] -> Type -> [Variable]
        findVars (x:xs) (TAp (TAp (TCon TConFun) tArg) tReturn)
            = Variable x tArg : findVars xs tReturn
        findVars [] _ = []
        t3 = constructorType t1
        (cs, ae) = analyseType env t3 tx
analysePat _ _ _ _ = (S.empty, emptyMap, []) -- Literal or default, no information to be gained

-- Analyse type
analyseType :: TypeEnvironment -> Type -> Type -> (Constraints, AnnotationEnvironment)
analyseType env t1 t2
    | t1 /= t1' || t2 /= t2' = analyseType env t1' t2' -- Normalization changes types, try again
    | t1 == t2               = (S.empty, emptyMap)     -- Types equal, analysis completed
        where
            t1' = typeNormalizeHead env t1
            t2' = typeNormalizeHead env t2
analyseType env (TAp (TAp (TCon TConFun) t11) t12) (TAp (TAp (TCon TConFun) t21) t22) = (cs, unionMapWith join ae1 ae2)
    -- Function arrows, analyse every pair of annotations on them
  where
    (TAp (TAnn a1 ) (TAp (TAnn r ) (TAp (TAnn a2 ) t1'))) = t11
    (TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') t2'))) = t21
    (c1, ae1) = analyseType env t1' t2'
    (c2, ae2) = analyseType env t12 t22
    cs = S.insert (a1' `Constraint` a1) $ S.insert (r' `Constraint` r) $ S.insert (a2' `Constraint` a2) $ S.union c1 c2
analyseType env (TAp t11 t12) (TAp t21 t22) = (S.union c1 c2, unionMapWith join ae1 ae2)
    where
        (c1, ae1) = analyseType env t11 t21
        (c2, ae2) = analyseType env t12 t22
analyseType env (TForall _ _ t1) (TForall _ _ t2) = analyseType env t1 t2
analyseType env (TStrict t1) t2 = analyseType env t1 t2
analyseType env t1 (TStrict t2) = analyseType env t1 t2 -- Remove all strict type information
analyseType _ (TVar _) (TVar _) = (S.empty, emptyMap) -- Lift has a bug which might distort type variables, exact index doesn't matter
analyseType _ (TAnn a1) (TAnn a2) = (S.empty, analyseAnn a1 a2) 
analyseType _ t1 t2 = error $ "analyseType: type mismatch: " ++ show (pretty t1) ++ " and " ++ show (pretty t2)

-- Analyse type
analyseType2 :: TypeEnvironment -> Type -> Type -> Constraints
analyseType2 env t1 t2
    | t1 /= t1' || t2 /= t2' = analyseType2 env t1' t2' -- Normalization changes types, try again
    | t1 == t2               = S.empty                  -- Types equal, analysis completed
        where
            t1' = typeNormalizeHead env t1
            t2' = typeNormalizeHead env t2
analyseType2 env (TAp t11 t12) (TAp t21 t22) = S.union c1 c2
    where
        c1 = analyseType2 env t11 t21
        c2 = analyseType2 env t12 t22
analyseType2 env (TForall _ _ t1) (TForall _ _ t2) = analyseType2 env t1 t2
analyseType2 env (TStrict t1) t2 = analyseType2 env t1 t2
analyseType2 env t1 (TStrict t2) = analyseType2 env t1 t2 -- Remove all strict type information
analyseType2 _ (TVar _) (TVar _) = S.empty -- Lift has a bug which might distort type variables, exact index doesn't matter
analyseType2 _ (TAnn a1) (TAnn a2) = S.singleton (a2 `Constraint` a1) 
analyseType2 _ t1 t2 = error $ "analyseType: type mismatch: " ++ show (pretty t1) ++ " and " ++ show (pretty t2)

{-
    Annotate
-}

annotateDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> CoreDecl
annotateDeclaration env supply decl@DeclAbstract{} = decl{declType = annotateTypeAbstract env supply (declType decl)}
annotateDeclaration env supply decl@DeclCon{}
    | declName decl == idFromString "[]" = decl{declType = annotateNil (declType decl)}
    | declName decl == idFromString ":"  = decl --decl{declType = annotateCons supply (declType decl)}
    | otherwise = decl{declType = annotateTypeAbstract env supply (declType decl)}
annotateDeclaration env supply decl@DeclValue{} = decl{declType = annotateTypeAbstract env supply (declType decl)} -- $dict
annotateDeclaration _ _ decl = decl -- Functions are handled outside this method, others don't need anything

-- [a] to S [a]
annotateNil :: Type -> Type
annotateNil (TForall q k (TAp t1 t2)) = TForall q k $ TAp (TAp (TAnn S) t1) t2

-- a -> [a] -> [a] to a -S1S> 2 [a] -S2S> (1&2) [a]
annotateCons :: NameSupply -> Type -> Type
annotateCons supply (TForall q k t) = TForall q k ta
  where
    (id1, supply') = freshId supply
    (id2, _) = freshId supply'
    TAp (TAp (TCon TConFun) t1) t' = t
    TAp (TAp (TCon TConFun) (TAp l1 t2)) (TAp l2 t3) = t'
    t1a = TAp (TAnn S) (TAp (TAnn (AnnVar id1)) (TAp (TAnn S) t1))
    ta = TAp (TAp (TCon TConFun) t1a) ta'
    t2a = TAp (TAnn S) (TAp (TAnn (AnnVar id2)) (TAp (TAnn S) t2'))
    t2' = TAp (TAp (TAnn $ AnnVar id2) l1) t2
    t3' = TAp (TAp (TAnn $ Join (AnnVar id1) (AnnVar id2)) l2) t3
    ta' = TAp (TAp (TCon TConFun) t2a) t3'

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
transformExpression :: SolvedConstraints -> IdSet -> BindMap -> Expr -> Expr
transformExpression sc a r (Let b e) = Let (transformBinds sc a r b) $ transformExpression sc a r e
transformExpression sc a r (Match i as) = Match i $ map transformAlt as
    where
        transformAlt (Alt p e) = Alt p $ transformExpression sc a r e
transformExpression sc a r (Ap e1 e2) = Ap e1' e2'
  where
    e1' = transformExpression sc a r e1
    e2' = transformExpression sc a r e2
transformExpression sc a r (ApType e t) = ApType (transformExpression sc a r e) t
transformExpression sc a r (Lam s v@(Variable x _) e) = Lam s' v e'
  where
     -- Lam can be made strict if it is strict when fully applied
    s' = if s then s else uncontain a (lookupVar (findMap x r) sc) == S
    e' = transformExpression sc a r e
transformExpression sc a r (Forall q k e) = Forall q k $ transformExpression sc a r e
transformExpression _ _ _ e = e -- Con, Lit and Var

-- Apply strict transformations on binds
transformBinds :: SolvedConstraints -> IdSet -> BindMap -> Binds -> Binds
transformBinds sc a r (Strict (Bind v e)) = Strict $ Bind v (transformExpression sc a r e)
transformBinds sc a r (NonRec (Bind v@(Variable x _) e)) = b'
  where
    b' = case lookupVar (findMap x r) sc of
        S -> Strict $ Bind v e'
        _ -> NonRec $ Bind v e'
    e' = transformExpression sc a r e
transformBinds sc a r (Rec bs) = Rec $ map transformBind bs
    where
        transformBind (Bind v e) = Bind v $ transformExpression sc a r e

-- Complete environment with type and annotation environment
data Environment = Environment { typeEnv :: TypeEnvironment,
                                 relEnv  :: RelevanceEnvironment,
                                 appEnv  :: ApplicativenessEnvironment}

-- Helper functions to add variables to both type and annotation environment
envAddVariable :: Variable -> Environment -> Environment
envAddVariable (Variable x (TAp (TAnn a1) (TAp (TAnn r) (TAp _ t)))) env = env{typeEnv = typeEnv', relEnv = relEnv', appEnv = appEnv'}
  where
    typeEnv' = typeEnvAddVariable (Variable x t) $ typeEnv env
    relEnv'  = insertMap x r $ relEnv env
    appEnv'  = insertMap x a1 $ appEnv env

envAddVariables :: [Variable] -> Environment -> Environment
envAddVariables vars env = foldr envAddVariable env vars

envAddBind :: Bind -> Environment -> Environment
envAddBind (Bind var _) = envAddVariable var

envAddBinds :: Binds -> Environment -> Environment
envAddBinds (Strict bind) env = envAddBind bind env
envAddBinds (NonRec bind) env = envAddBind bind env
envAddBinds (Rec binds) env = foldr envAddBind env binds

-- Get relevance and applicative annotations of var, set them equal to contexts
getAnnotations :: Environment -> SAnn -> SAnn -> Id -> AnnotationEnvironment
getAnnotations env rel app var = unionMapWith join (f (relEnv env) rel) (f (appEnv env) app)
  where
    f env' con = case lookupMap var env' of
      Just (AnnVar a) -> singleMap a con
      _ -> emptyMap

-- Make a L constraint for all annotation variables
getLConstraints :: Environment -> AnnotationEnvironment
getLConstraints = mapFromList . map (\x -> (x, L)) . getAnnotationVariablesEnv

-- Get all annotation variables in the environment to introduce constraints
getAnnotationVariablesEnv :: Environment -> [Id]
getAnnotationVariablesEnv env = f (relEnv env) ++ f (appEnv env) ++ g
  where
    f env' = map snd $ listFromMap $ mapMap fromAnn $ filterMap isAnn env'
    g = listFromSet $ unionSets $ map snd $ listFromMap $ mapMap getAnnotationsType $ typeEnvLocalValues $ typeEnv env

getAnnotationsType :: Type -> IdSet
getAnnotationsType (TAp (TAp (TCon TConFun) _) _) = emptySet
getAnnotationsType (TAp t1 t2) = unionSet (getAnnotationsType t1) (getAnnotationsType t2)
getAnnotationsType (TStrict t) = getAnnotationsType t
getAnnotationsType (TForall _ _ t) = getAnnotationsType t
getAnnotationsType (TAnn a) = setFromList $ getVariablesAnn a
getAnnotationsType _ = emptySet

-- Containment
containment :: Environment -> SAnn -> AnnotationEnvironment -> AnnotationEnvironment
containment env con ae = unionMapWith join ae $ mapFromList $ map (\x -> (x, con)) $ getAnnotationVariablesEnv env

{-
    Annotate
-}

annotateType :: TypeEnvironment -> NameSupply -> Type -> Type
annotateType env supply t
    -- Type is not in weak head normal form
    | t /= t' = annotateType env supply t'
        where
            t' = typeNormalizeHead env t
annotateType env supply (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1a) t2'
    -- Function, place three annotations on the second argument (printed on the arrow)
    where
        (id1, id2, id3, supply') = threeIds supply
        (supply1, supply2) = splitNameSupply supply'
        t1' = annotateType env supply1 t1
        t1a = case t1 of
          TStrict _ -> TAp (TAnn $ AnnVar id1) $ TAp (TAnn $ AnnVar id3) $ TAp (TAnn $ AnnVar id3) t1'
          _         -> TAp (TAnn $ AnnVar id1) $ TAp (TAnn $ AnnVar id2) $ TAp (TAnn $ AnnVar id3) t1'
        t2' = annotateType env supply2 t2
annotateType env supply (TAp t1 t2) = TAp t1' t2'
    -- Annotate applications to datatypes
    where
        (supply1, supply2) = splitNameSupply supply
        t1' = annotateType env supply1 t1
        t2' = annotateType env supply2 t2 
annotateType env supply (TForall q k t) = TForall q k $ annotateType env supply t -- Non-strictness forall needs to stay
annotateType env supply (TStrict t) = TStrict $ annotateType env supply t
annotateType _ supply (TCon (TConTuple n)) = foldr (\i t -> TAp (TAnn i) t) (TCon (TConTuple n)) ids
    where
        ids = mapWithSupply (\s _ -> AnnVar $ fst $ freshId s) supply [1 .. n]
annotateType _ supply t@(TCon (TConDataType c)) | stringFromId c == "[]" = TAp (TAnn $ AnnVar i) t -- Place extra annotation for list
    where
        (i, _) = freshId supply
annotateType _ _ t = t

annotateTypeAbstract :: TypeEnvironment -> NameSupply -> Type -> Type
annotateTypeAbstract env supply t = t' 
  where
    (t', _, _) = annotateTypeAbstract' env supply t

annotateTypeAbstract' :: TypeEnvironment -> NameSupply -> Type -> (Type, SAnn, SAnn)
annotateTypeAbstract' env supply t
    -- Type is not in weak head normal form
    | t /= t' = annotateTypeAbstract' env supply t'
        where
            t' = typeNormalizeHead env t
annotateTypeAbstract' env supply (TAp (TAp (TCon TConFun) t1) t2) = (TAp (TAp (TCon TConFun) t1a) t2', a', r')
    -- Function, place an annotation on the second argument (printed on the arrow)
    where
        (i, supply') = freshId supply
        ann = AnnVar i
        (supply1, supply2) = splitNameSupply supply'
        (t1', _, _) = annotateTypeAbstract' env supply1 t1
        (t2', a, r) = annotateTypeAbstract' env supply2 t2
        a' = join ann a
        r' = if arityFromType t2' == 0 then S else join ann r
        t1a = case t1' of
            (TStrict t) -> TAp (TAnn a') (TAp (TAnn r') (TAp (TAnn ann) t  ))
            _           -> TAp (TAnn L)  (TAp (TAnn L ) (TAp (TAnn ann) t1'))
annotateTypeAbstract' env supply (TAp t1 t2) = (TAp t1' t2', S, S)
    -- Annotate applications to datatypes
    where
        (supply1, supply2) = splitNameSupply supply
        (t1', _, _) = annotateTypeAbstract' env supply1 t1
        (t2', _, _) = annotateTypeAbstract' env supply2 t2
annotateTypeAbstract' env supply (TForall q k t) = (TForall q k t', a, r)
    where
        (t', a, r) = annotateTypeAbstract' env supply t -- Non-strictness forall needs to stay
annotateTypeAbstract' env supply (TStrict t) = (TStrict t', a, r)
    where
        (t', a, r) = annotateTypeAbstract' env supply t -- Strictness information is moved to annotations
annotateTypeAbstract' _ _ (TCon (TConTuple n)) = (t, S, S)
    where
        t = foldr (\i t' -> TAp (TAnn i) t') (TCon (TConTuple n)) (replicate n L)
annotateTypeAbstract' _ _ t@(TCon (TConDataType c)) | stringFromId c == "[]" = (TAp (TAnn L) t, S, S) -- Place extra annotation for list
annotateTypeAbstract' _ _ t = (t, S, S)

annotateTuple :: [SAnn] -> NameSupply -> Type -> Type
annotateTuple a supply (TForall q k t) = TForall q k $ annotateTuple a supply t
annotateTuple a supply (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1') t2'
    where
        (id1, id2, id3, supply') = threeIds supply
        t1' = TAp (TAnn $ AnnVar id1) (TAp (TAnn $ AnnVar id2) (TAp (TAnn $ AnnVar id3) t1))
        t2' = annotateTuple (AnnVar id2 : a) supply' t2
annotateTuple a supply (TAp t1 t2) = TAp (annotateTuple a supply t1) t2
annotateTuple a _ (TCon (TConTuple n)) = foldl (\t i -> TAp (TAnn i) t) (TCon (TConTuple n)) a
annotateTuple _ _ t = t

annotateTuplePat :: TypeEnvironment -> NameSupply -> Type -> (Type, SAnn)
annotateTuplePat env supply t = (t', AnnVar id2)
    where
        (id1, id2, id3, supply') = threeIds supply
        t' = TAp (TAnn $ AnnVar id1) (TAp (TAnn $ AnnVar id2) (TAp (TAnn $ AnnVar id3) (annotateType env supply' t)))


annotateTypeMax :: TypeEnvironment -> Type -> Type
annotateTypeMax env t
    -- Type is not in weak head normal form
    | t /= t' = annotateTypeMax env t'
        where
            t' = typeNormalizeHead env t
annotateTypeMax env (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1') t2'
    where
    -- Function, place an annotation on the second argument (printed on the arrow)
        t1' = TAp (TAnn S) (TAp (TAnn S) (TAp (TAnn S) (annotateTypeMax env t1)))
        t2' = annotateTypeMax env t2
annotateTypeMax env (TAp t1 t2) = TAp t1' t2'
    -- Annotate applications to datatypes (Tuple)
    where
        t1' = annotateTypeMax env t1
        t2' = annotateTypeMax env t2
annotateTypeMax env (TStrict t) = TStrict $ annotateTypeMax env t
annotateTypeMax env (TForall q k t) = TForall q k $ annotateTypeMax env t
annotateTypeMax _ t@(TCon (TConDataType c)) | stringFromId c == "[]" = TAp (TAnn S) t -- Place extra annotation for list
annotateTypeMax _ t@(TCon (TConTuple n)) = foldr (\i t' -> TAp (TAnn i) t') t (replicate n S)
annotateTypeMax _ t = t

annotateBind :: Environment -> NameSupply -> Bind -> Bind
annotateBind env supply (Bind (Variable x t) e) = Bind (Variable x t') e
  where
    -- Fresh variables for relevance and both applicativeness
    (id1, id2, id3, supply') = threeIds supply
    -- Annotate inner type
    t' = TAp (TAnn (AnnVar id1)) (TAp (TAnn (AnnVar id2)) (TAp (TAnn (AnnVar id3)) (annotateType (typeEnv env) supply' t)))

getApplicatives :: Type -> IdSet
getApplicatives (TAp (TAp (TCon TConFun) (TAp _ (TAp _ (TAp (TAnn (AnnVar i)) _)))) t2) = insertSet i (getApplicatives t2)
getApplicatives (TForall _ _ t) = getApplicatives t
getApplicatives (TStrict t) = getApplicatives t
getApplicatives _ = emptySet

uncontain :: IdSet -> SAnn -> SAnn
uncontain a (AnnVar x) | x `elemSet` a = S
uncontain a (Join x y) = join (uncontain a x) (uncontain a y)
uncontain a (Meet x y) = meet (uncontain a x) (uncontain a y)
uncontain _ ann        = ann

-- Unify the annotations on function arrows with a join
unifyAnnotations :: Type -> Type -> Type
unifyAnnotations (TAp t11 t12) (TAp t21 t22) = TAp t1 t2
  where
    t1 = unifyAnnotations t11 t21
    t2 = unifyAnnotations t12 t22
unifyAnnotations (TStrict t1) t2 = unifyAnnotations t1 t2
unifyAnnotations t1 (TStrict t2) = unifyAnnotations t1 t2
unifyAnnotations (TForall q k t1) (TForall _ _ t2) = TForall q k $ unifyAnnotations t1 t2
unifyAnnotations (TAnn a1) (TAnn a2) = TAnn (join a1 a2)
unifyAnnotations t1 _ = t1

constructorType :: Type -> Type
constructorType (TAp (TAp (TCon TConFun) _) t2) = constructorType t2
constructorType t = t
