module Helium.CodeGeneration.Core.Strictness.MonovariantAdvanced (monovariantStrictness) where

import Data.List
import qualified Data.Set as S

import Helium.CodeGeneration.Core.BindingGroup
import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.Strictness.DataAdvanced
import Helium.CodeGeneration.Core.Strictness.Solve
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

import Text.PrettyPrint.Leijen (pretty)

-- Analysis data type, containing return expression, set of constraints and the environment containing the annotations
data Analysis a = Analysis a Constraints AnnotationEnvironment BindMap

mergeAnalysis :: (SAnn -> SAnn -> SAnn) -> [Analysis a] -> Analysis [a]
mergeAnalysis _ [] = Analysis [] S.empty emptyMap emptyMap
mergeAnalysis f (x:xs) = Analysis (v:v') (S.union c c') (unionMapWith f a a') (unionMap r r')
    where
        Analysis v c a r = x
        Analysis v' c' a' r' = mergeAnalysis f xs

type GroupData = (MonoMap, SolvedConstraints, BindMap, TypeEnvironment, NameSupply)
type CoreGroup = BindingGroup Expr

monovariantStrictness :: NameSupply -> CoreModule -> CoreModule
monovariantStrictness supply mod = mod {moduleDecls = values''}
  where
    (supply1, supply') = splitNameSupply supply
    (supply2, supply3) = splitNameSupply supply'
    -- Ignore declarations which have already been analysed
    (decls1, decls2) = partition (any isCustomAnn . declCustoms) $ moduleDecls mod
    -- Split module in functions and others (constructors, abstract, synonyms)
    (values, others) = partition isDeclValue decls2
    -- For declarations which have been annotated, set strictness type to declType
    decls1' = map setStrictnessType decls1
    -- Annotate others
    others' = mapWithSupply (annotateDeclaration (typeEnvForModule mod)) supply1 others
    -- Create starting environment
    env = typeEnvForModule mod{moduleDecls = others' ++ decls1'}
    -- Binding group analysis for functions
    groups = coreBindingGroups values
    (values', sc, r, _, _) = foldl groupStrictness (emptyMap, emptyMap, emptyMap, env, supply2) groups
    -- Transform declarations based on solved constraints
    values'' = map (transformDeclaration (annotateTypeAbstract' env supply3) values' sc r) $ moduleDecls mod

groupStrictness :: GroupData -> CoreGroup -> GroupData
-- Single declaration
groupStrictness (v, sc, r, env, supply) (BindingNonRecursive d) = (v', sc'', r'', env', supply2)
  where
    (supply1, supply2) = splitNameSupply supply
    -- Analyse function
    Analysis e cs ae r' = analyseDeclaration env supply1 d
    -- Solve constraints
    sc' = solveConstraints ae cs
    -- Get annotated type of body
    t = transformType sc' $ typeOfCoreExpression env e
    -- Add strictness type to environment
    env' = typeEnvAddGlobalValue (declName d) t env
    -- Update values for next binding group
    v' = insertMap (declName d) t v 
    sc'' = unionMapWith join sc sc'
    r'' = unionMap r r'
-- Group of recursive declarations
groupStrictness (v, sc, r, env, supply) (BindingRecursive ds) = (v', sc'', r'', env'', supply2)
  where
    (supply1, supply2) = splitNameSupply supply
    -- Annotate type signatures and add them to the environment
    ts = map (annotateTypeRec env . declType) ds
    env' = typeEnvAddGlobalValues (map (\(d, t) -> (declName d, t)) (zip ds ts)) env
    -- Run analysis on all bodies, merge information with meet
    Analysis es cs ae r' = mergeAnalysis meet $ mapWithSupply (analyseDeclaration env') supply1 ds
    -- Solve constraints
    sc' = solveConstraints ae cs
    -- Get annotated types of bodies
    ts' = map (transformType sc' . typeOfCoreExpression env') es
    -- Add strictness types to environment
    env'' = typeEnvAddGlobalValues (map (\(d, t) -> (declName d, t)) (zip ds ts')) env
    -- Update values for next binding group
    v' = foldl (\v'' (d, t) -> insertMap (declName d) t v'') v (zip ds ts')
    sc'' = unionMapWith join sc sc'
    r'' = unionMap r r'

{-
    Analyse
-}

analyseDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> Analysis Expr
analyseDeclaration typeEnv supply decl@DeclValue{} = analyseExpression env S S supply $ valueValue decl
    where
        env = Environment typeEnv emptyMap emptyMap

analyseExpression :: Environment -> SAnn -> SAnn -> NameSupply -> Expr -> Analysis Expr
analyseExpression env rel app supply (Let b e) = Analysis (Let b' e') cs (unionMapWith meet a1 as) (unionMap r1 r2)
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse binds
        (Analysis b' c1 a1 r1, app') = analyseBinds env supply1 rel b
        -- Add annotated binds to environment
        env' = envAddBinds b' env
        -- Analyse body, set contexts to S
        Analysis e' c2 a2 r2 = analyseExpression env' S S supply2 e
        -- Containment on old environment
        as = unionMapWith join a2 $ containment env rel
        -- Add constraint on applicativeness
        cs = S.insert (app `Constraint` app') $ S.union c1 c2
analyseExpression env rel app supply (Match id a) = Analysis (Match id a') cs ae r
    where
        -- Merge with join as strictness has to occur in every case
        Analysis a' cs ae r = mergeAnalysis join $ mapWithSupply (analyseAlt env rel app id) supply a
analyseExpression env rel app supply (Ap e1 e2) = Analysis (Ap e1' e2') cs (unionMapsWith meet [ae1, ae2, ae3]) (unionMap r1 r2)
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse function, with applicative context set to relevance
        Analysis e1' c1 ae1 r1 = analyseExpression env rel app supply1 e1
        -- Get type of function
        t = typeNormalizeHead (typeEnv env) $ typeOfCoreExpression (typeEnv env) e1'
        -- Get the annotations on the function arrow
        (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t')))) _) = t
        -- Analyse argument with context of the previous annotations
        Analysis e2' c2 ae2 r2 = analyseExpression env (join rel r) (join rel a1) supply2 e2
        -- Annotation unifications between the function and the given argument
        (ae3, c3) = analyseType env t' $ typeOfCoreExpression (typeEnv env) e2'
        -- Add constraint on applicativeness
        cs = S.insert (app `Constraint` a2) $ S.unions [c1, c2, c3]
analyseExpression env rel app supply (ApType e t) = Analysis (ApType e' t') cs ae r
    where
        (supply1, supply2) = splitNameSupply supply
        -- Annotate type, if it is a tuple place extra annotations
        t' = if isTupAp e then annotateVarType env supply1 t else annotateType (typeEnv env) supply1 t
        -- Analyse expression
        Analysis e' cs ae r = analyseExpression env rel app supply2 e
analyseExpression env _ app supply (Lam s (Variable x t) e) = Analysis (Lam s v' e') c a' r'
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
        -- Analyse expression, set relevance to S
        Analysis e' c a r = analyseExpression env' S (AnnVar id3) supply2 e
        -- Containment on old environment
        a' = unionMapWith join a $ containment env app
        -- If not strict, add variable to map which might turn to strict
        r' = if s then r else insertMap x (Join (AnnVar id1) (AnnVar id2)) r
analyseExpression env rel app supply (Forall q k e) = Analysis (Forall q k e') c a r
    where
        -- Forall can be ignored
        Analysis e' c a r = analyseExpression env rel app supply e
analyseExpression env _ _ _ (Con c) = Analysis (Con c) S.empty (getLConstraints env) emptyMap -- Set all annotation variables to L
analyseExpression env rel app _ (Var v) = Analysis (Var v) S.empty (unionMapWith meet (getLConstraints env) ae) emptyMap
    where
        -- Set all annotation variables to L except the annotations related to this variable, which are set to context
        ae = getAnnotations env rel app v
analyseExpression env _ _ _ (Lit l) = Analysis (Lit l) S.empty (getLConstraints env) emptyMap -- Set all annotation variables to L

analyseBinds :: Environment -> NameSupply -> SAnn -> Binds -> (Analysis Binds, SAnn)
analyseBinds env supply rel (Rec bs) = (Analysis (Rec bs'') c a r, foldr join S app)
    where
        -- Annotate types beforehand because they occur in the body
        bs' = mapWithSupply (annotateBind env) supply bs
        -- Add binds  to environment
        env' = envAddBinds (Rec bs') env
        -- Run analysis on every bind separately
        (xs, app) = unzip $ mapWithSupply (analyseRecBind env' rel) supply bs'
        -- Merge the results with meet, as being strict in one bind is enough
        Analysis bs'' c a r = mergeAnalysis meet xs
analyseBinds env supply rel (NonRec (Bind (Variable x _) e)) = (Analysis (NonRec b) cs ae r', AnnVar id3)
    where
        -- Fresh variable for relevance annotation
        (id1, id2, id3, supply') = threeIds supply
        -- Run analysis on binding with relevance set to context
        Analysis e' cs ae r = analyseExpression env (join rel (AnnVar id2)) (join rel (AnnVar id1)) supply' e
        -- Get type of bind to store in signature
        t' = typeOfCoreExpression (typeEnv env) e'
        -- Add annotations outside the type
        b = Bind (Variable x (TAp (TAnn $ AnnVar id1) (TAp (TAnn $ AnnVar id2) (TAp (TAnn $ AnnVar id3) t')))) e'
        -- Bind is NonRec, add to map of those which might be turned to strict
        r' = insertMap x (Join (AnnVar id1) (AnnVar id2)) r
analyseBinds env supply rel (Strict (Bind (Variable x _) e)) = (Analysis (Strict b) cs ae r, AnnVar id)
    where
        -- Fresh variables for second applicativeness
        (id, supply') = freshId supply
        -- Run analysis on binding with relevance set to context
        Analysis e' cs ae r = analyseExpression env rel rel supply' e
        -- Get type of bind to store in signature
        t' = typeOfCoreExpression (typeEnv env) e'
        -- Add annotations outside the type
        b = Bind (Variable x (TAp (TAnn S) (TAp (TAnn S) (TAp (TAnn $ AnnVar id) t')))) e'

analyseRecBind :: Environment -> SAnn -> NameSupply -> Bind -> (Analysis Bind, SAnn)
analyseRecBind env rel supply (Bind v e) = (Analysis (Bind (Variable x t') e') c a r, a2)
    where
        -- Get annotations from variable previously annotated
        Variable x (TAp (TAnn a1) (TAp (TAnn rel') (TAp (TAnn a2) _))) = v
        -- Run analysis on binding with relevance and applicative joined with context
        Analysis e' c a r = analyseExpression env (join rel rel') (join rel a1) supply e
        -- Get type of body
        t' = TAp (TAnn a1) (TAp (TAnn rel') (TAp (TAnn a2) (typeOfCoreExpression (typeEnv env) e')))
        
analyseAlt :: Environment -> SAnn -> SAnn -> Id -> NameSupply -> Alt -> Analysis Alt
analyseAlt env rel app id supply (Alt p e) = Analysis (Alt p' e') (S.union c1 c2) (unionMapWith meet a1 a2) r
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse the pattern
        Analysis p' c1 a1 _ = analysePat env id supply1 p
        -- Add pattern to environment
        env' = envAddPattern p' env
        -- Run analysis 
        Analysis e' c2 a2 r = analyseExpression env' rel app supply2 e

analysePat :: Environment -> Id -> NameSupply -> Pat -> Analysis Pat
analysePat env id supply (PatCon (ConTuple n) t i) = Analysis (PatCon (ConTuple n) t' i) cs ae emptyMap
    where
        -- In case of a tuple, all types need three extra annotations to communicate the return annotations of the tuple
        t' = mapWithSupply (annotateVarType env) supply t
        -- Get equalities between type of id matched on and type of pattern
        (ae, cs) = analyseType env (typeOfId (typeEnv env) id) (foldl TAp (TCon (TConTuple n)) t')
analysePat env id supply (PatCon c t i) = Analysis (PatCon c t' i) cs ae emptyMap
    where
        -- Annotate all types given to constructor
        t' = mapWithSupply (annotateType (typeEnv env)) supply t
        -- Add pattern to environment
        env' = envAddPattern (PatCon c t' i) env
        -- Construct expression equivalent to constructor
        e = foldl Ap (foldl ApType (Con c) t') (map Var i)
        -- Analyse type of matched id with type of constructor
        (ae, cs) = analyseType env (typeOfId (typeEnv env) id) (typeOfCoreExpression (typeEnv env') e)
analysePat _ _ _ p = Analysis p S.empty emptyMap emptyMap -- Literal or default, no information to be gained

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
annotateDeclaration env supply decl@DeclAbstract{} = decl{declType = annotateTypeAbstract' env supply (declType decl)}
annotateDeclaration env supply decl@DeclCon{} = decl{declType = annotateTypeAbstract' env supply (declType decl)}
-- annotateDeclaration env supply decl@DeclTypeSynonym{}
--     -- String is the only type synonym which has to be annotated because it is partly hardcoded in the type system
--     | declName decl == idFromString "String" = decl{declType = annotateType env supply (declType decl)}
annotateDeclaration _ _ decl = decl -- Value is handled outside this method, others don't need anything

annotateTypeAbstract' :: TypeEnvironment -> NameSupply -> Type -> Type
annotateTypeAbstract' env supply t = fst $ annotateTypeAbstract env supply t

{-
    Transform
-}

-- Apply strict annotations on declarations
transformDeclaration :: (Type -> Type) -> MonoMap -> SolvedConstraints -> BindMap -> CoreDecl -> CoreDecl
transformDeclaration _ vs sc r decl@DeclValue{}
    | elemMap (declName decl) vs = decl{valueValue = e, declCustoms = c}
    where
        t = findMap (declName decl) vs
        e = transformExpression sc r $ valueValue decl
        c = strictnessToCustom (transformType sc t) $ declCustoms decl
transformDeclaration f _ _ _ decl
  | isUpdate decl = decl{declCustoms = c}
  | otherwise     = decl
    where
      c = strictnessToCustom (f $ declType decl) (declCustoms decl)

-- Apply strict annotations on types
transformType :: SolvedConstraints -> Type -> Type
transformType sc (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1)))) t2) =
  TAp (TAp (TCon TConFun) t1') t2'
    where
      a1' = lookupVarMono a1 sc
      r'  = lookupVarMono r sc
      a2' = lookupVarMono a2 sc
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

-- Lookup annotation of variables
lookupVarMono :: SAnn -> SolvedConstraints -> SAnn
lookupVarMono (AnnVar x) sc | elemMap x sc = case findMap x sc of
  S -> S
  _ -> L
lookupVarMono S _ = S
lookupVarMono _ _ = L
