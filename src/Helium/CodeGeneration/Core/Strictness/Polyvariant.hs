module Helium.CodeGeneration.Core.Strictness.Polyvariant where

import qualified Data.Set as S

import Helium.CodeGeneration.Core.Strictness.Transform
import Helium.CodeGeneration.Core.Strictness.Solve
import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

import Text.PrettyPrint.Leijen (pretty)

{-
Analyse
-}

analyseDeclaration :: TypeEnvironment -> IdSet -> NameSupply -> CoreDecl -> Analysis Expr
analyseDeclaration typeEnv is supply decl@DeclValue{} = Analysis e cs ae sc
    where
        (supply1, supply2) = splitNameSupply supply
        -- Instantiate forallified expressions
        (ie, is2) = instantiateExpression typeEnv supply1 $ valueValue decl
        -- Create empty environment
        env = Environment typeEnv emptyMap emptyMap (unionSet is is2)
        -- Run analysis, always start in S context
        Analysis e cs ae sc = analyseExpression env S S supply2 ie

analyseExpression :: Environment -> SAnn -> SAnn -> NameSupply -> Expr -> Analysis Expr
analyseExpression env rel app supply (Let b e) = Analysis (Let b' e') cs (unionMapWith meet a1 as) (unionMap sc1 sc2)
    where
        (supply1, supply') = splitNameSupply supply
        (supply2, supply3) = splitNameSupply supply'
        -- Analyse binds
        (Analysis b' c1 a1 sc1, app', is1) = analyseBinds env supply1 rel b
        -- Add annotated binds to environment
        env' = envAddBinds b' env
        -- Instantiate quantified functions
        (e1, is2) = instantiateExpression (typeEnv env') supply2 e
        -- Add used annotation variables to IdSet
        env'' = envAddVars (unionSet is1 is2) env'
        -- Analyse body, set contexts to S
        Analysis e' c2 a2 sc2 = analyseExpression env'' S S supply3 e1
        -- Containment on old environment
        as = unionMapWith join a2 $ containment env rel
        -- Add constraint on applicativeness
        cs = S.insert (app `Constraint` app') $ S.union c1 c2
analyseExpression env rel app supply (Match id a) = Analysis (Match id a') c ae sc
    where
        -- Merge with join as strictness has to occur in every case
        Analysis a' c ae sc = mergeAnalysis join $ mapWithSupply (analyseAlt env rel app id) supply a
analyseExpression env rel app supply (Ap e1 e2) = Analysis (Ap e1' e2') cs (unionMapsWith meet [ae1, ae2, ae3]) (unionMap sc1 sc2)
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse function, with applicative context set to relevance
        Analysis e1' c1 ae1 sc1 = analyseExpression env rel rel supply1 e1
        -- Get type of function
        t = typeNormalizeHead (typeEnv env) $ typeOfCoreExpression (typeEnv env) e1'
        -- Get the annotations on the function arrow
        (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t')))) _) = t
        -- Analyse argument with context of the previous annotations
        Analysis e2' c2 ae2 sc2 = analyseExpression env (join rel r) (join rel a1) supply2 e2
        -- Add constraint on applicativeness
        cs = S.insert (app `Constraint` a2) $ S.union c1 c2
        -- Annotation unifications between the function and the given argument
        t2 = typeOfCoreExpression (typeEnv env) e2'
        ae3 = analyseType env t' t2
analyseExpression env rel app supply (ApType e t) = Analysis (ApType e' t') c a sc
    where
        (supply1, supply2) = splitNameSupply supply
        -- Annotate type, if it is a tuple place extra annotations
        (t', is) = if isTupAp e then annotateVarType env supply1 t else annotateType (typeEnv env) supply1 t
        -- Add used annotation variables to IdSet
        env' = envAddVars is env
        -- Analyse expression
        Analysis e' c a sc = analyseExpression env' rel app supply2 e
analyseExpression env _ app supply (Lam s (Variable x t) e) = Analysis (Lam s v' e') c a'' sc
    where
        (id1, id2, id3, supply') = threeIds supply
        (supply1, supply2) = splitNameSupply supply'
        -- Annotate type in variable
        (t', is) = annotateType (typeEnv env) supply1 t
        -- Add variable and used annotations to environment
        v' = Variable x (TAp (TAnn (AnnVar id1)) (TAp (TAnn (AnnVar id2)) (TAp (TAnn (AnnVar id3)) t')))
        is' = insertSet id1 $ insertSet id2 $ insertSet id3 is
        env' = envAddVars is' $ envAddVariable v' env
        -- Analyse expression, set relevance to S
        Analysis e' c a sc = analyseExpression env' S (AnnVar id3) supply2 e
        -- Containment on old environment
        a' = unionMapWith join a $ containment env app
        -- If lambda was strict, set its annotation variables equal to the second applicative
        a'' = if s then updateMap id1 (AnnVar id3) (updateMap id2 (AnnVar id3) a') else a'
analyseExpression env rel app supply (Forall q k e) = Analysis (Forall q k e') c a sc
    where
        -- Forall can be ignored
        Analysis e' c a sc = analyseExpression env rel app supply e
analyseExpression env _ _ _ (Con c) = Analysis (Con c) S.empty (getLConstraints env) emptyMap -- Set all annotation variables to L
analyseExpression env rel app _ (Var v) = Analysis (Var v) S.empty (unionMapWith meet (getLConstraints env) ae) emptyMap
    where
        -- Set all annotation variables to L except the annotations related to this variable, which are set to context
        ae = getAnnotations env rel app v
analyseExpression env _ _ _ (Lit l) = Analysis (Lit l) S.empty (getLConstraints env) emptyMap -- Set all annotation variables to L

analyseBinds :: Environment -> NameSupply -> SAnn -> Binds -> (Analysis Binds, SAnn, IdSet)
analyseBinds env supply rel (Rec bs) = (Analysis (Rec b1) cs ae (unionMap sc sc'), foldr join S app, unionSet (unionSets is1) (unionSets i2))
    where
        -- Annotate types beforehand because they occur in the body
        (bs'', is1) = unzip $ mapWithSupply (annotateBind env) supply bs
        -- Add binds and used annotation variables to environment
        env' = envAddVars (unionSets is1) $ envAddBinds (Rec bs'') env
        -- Run analysis on every bind separately
        (xs, app) = unzip $ mapWithSupply (analyseRecBind env' rel) supply bs''
        -- Merge the results with meet, as being strict in one bind is enough
        Analysis bs' c a sc' = mergeAnalysis meet xs
        -- Run simplifier to get solved local constraints
        Analysis _ cs ae sc = simplify c a env'
        -- Apply solved constraints to get type signatures for all binds
        (b1, i2) = unzip $ map (transformBind' env' sc) bs'
analyseBinds env supply rel (NonRec b) = (Analysis (NonRec b1) cs ae (unionMap sc sc'), app, unionSet i2 is)
    where
        -- Run analysis on bind
        (Analysis b' c a sc', app, is) = analyseBind env rel supply b
        -- Run simplifier to get solved local constraints
        Analysis _ cs ae sc = simplify c a (envAddVars is env)
        -- Apply solved constraints to get type signature for all bind
        (b1, i2) = transformBind' env sc b'
analyseBinds env supply rel (Strict b) = (Analysis (Strict b1) cs ae (unionMap sc sc'), app, unionSet i2 is)
    where
        -- Run analysis on bind
        (Analysis b' c a sc', app, is) = analyseBind env rel supply b
        -- Set variables associated to this strict bind to strict
        a' = strictBind b' a
        -- Run simplifier to get solved local constraints
        Analysis _ cs ae sc = simplify c a' (envAddVars is env)
        -- Apply solved constraints to get type signature for all bind
        (b1, i2) = transformBind' env sc b'

analyseRecBind :: Environment -> SAnn -> NameSupply -> Bind -> (Analysis Bind, SAnn)
analyseRecBind env rel supply (Bind v e) = (Analysis (Bind v e') c a sc, a2)
    where
        -- Get annotations from variable previously annotated
        Variable _ (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) _))) = v
        -- Run analysis on binding with relevance and applicative joined with context
        Analysis e' c a sc = analyseExpression env (join rel r) (join rel a1) supply e 

analyseBind :: Environment -> SAnn -> NameSupply -> Bind -> (Analysis Bind, SAnn, IdSet)
analyseBind env rel supply (Bind (Variable x t) e) = (Analysis (Bind (Variable x t') e') c a sc, AnnVar id3, is)
    where
        -- Fresh variables for relevance and both applicativeness
        (id1, id2, id3, supply') = threeIds supply
        -- Add annotations outside the type
        t' = TAp (TAnn (AnnVar id1)) (TAp (TAnn (AnnVar id2)) (TAp (TAnn (AnnVar id3)) t))
        -- Add ids to set of used ids
        is = setFromList [id1, id2, id3]
        env' = envAddVars is env
        -- Run analysis on binding with relevance and applicative joined with context
        Analysis e' c a sc = analyseExpression env' (join rel (AnnVar id2)) (join rel (AnnVar id1)) supply' e   
        
analyseAlt :: Environment -> SAnn -> SAnn -> Id -> NameSupply -> Alt -> Analysis Alt
analyseAlt env rel app id supply (Alt p e) = Analysis (Alt p' e') c2 (unionMapWith meet a1 a2) sc
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse the pattern, only the annotation environment has possibly additional information
        (Analysis p' _ a1 _, is) = analysePat env id supply1 p
        -- Add pattern and used identifiers to environment
        env' = envAddVars is $ envAddPattern p' env
        -- Run analysis 
        Analysis e' c2 a2 sc = analyseExpression env' rel app supply2 e

analysePat :: Environment -> Id -> NameSupply -> Pat -> (Analysis Pat, IdSet)
analysePat env id supply (PatCon (ConTuple n) t i) = (Analysis (PatCon (ConTuple n) t' i) S.empty ae emptyMap, unionSets is)
  where
    -- In case of a tuple, all types need three extra annotations to communicate the return annotations of the tuple
    (t', is) = unzip $ mapWithSupply (annotateVarType env) supply t
    -- Get equalities between type of id matched on and type of pattern
    ae = analyseType env (typeOfId (typeEnv env) id) (foldl TAp (TCon (TConTuple n)) t')
analysePat env _ supply (PatCon c t i) = (Analysis (PatCon c t' i) S.empty emptyMap emptyMap, unionSets is)
    where
        -- Annotate all types given to constructor
        (t', is) = unzip $ mapWithSupply (annotateType (typeEnv env)) supply t
analysePat _ _ _ p = (Analysis p S.empty emptyMap emptyMap, emptySet) -- Literal or default, no information to be gained

-- Analyse type
analyseType :: Environment -> Type -> Type -> AnnotationEnvironment
analyseType env t1 t2
    | t1 /= t1' || t2 /= t2' = analyseType env t1' t2' -- Normalization changes types, try again
    | t1 == t2               = emptyMap -- Types equal, analysis completed
        where
            t1' = typeNormalizeHead (typeEnv env) t1
            t2' = typeNormalizeHead (typeEnv env) t2
analyseType env (TAp (TAp (TCon TConFun) t11) t12) (TAp (TAp (TCon TConFun) t21) t22) = unionMapsWith join [ae1, ae2, ae3, ae4, ae5]
    -- Function arrows, analyse every pair of annotations on them
  where
    (TAp (TAnn a1 ) (TAp (TAnn r ) (TAp (TAnn a2 ) t1'))) = t11
    (TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') t2'))) = t21
    ae1 = analyseAnn a1 a1'
    ae2 = analyseAnn r r'
    ae3 = analyseAnn a2 a2'
    ae4 = analyseType env t1' t2'
    ae5 = analyseType env t12 t22
analyseType env (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) t1)))))) t2 = analyseType env t1' t2
    -- Double annotations in case of newtypes. Since they are strict by design we can forget them and place S
    where
        t1' = TAp (TAnn S) (TAp (TAnn S) (TAp (TAnn S) t1))
analyseType env t1 (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) (TAp (TAnn _) t2)))))) = analyseType env t1 t2'
    -- Double annotations in case of newtypes. Since they are strict by design we can forget them and place S
    where
        t2' = TAp (TAnn S) (TAp (TAnn S) (TAp (TAnn S) t2))
analyseType env (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1)))
       (TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') t2))) = unionMapsWith join [ae1, ae2, ae3, ae4]
    -- Annotations on datatypes, evaluate per pair
    where
        ae1 = analyseAnn a1 a1'
        ae2 = analyseAnn r r'
        ae3 = analyseAnn a2 a2'
        ae4 = analyseType env t1 t2
analyseType env (TAp t11 t12) (TAp t21 t22) = unionMapWith join ae1 ae2
    -- Unannotated applications
    where
        ae1 = analyseType env t11 t21
        ae2 = analyseType env t12 t22
analyseType env (TForall _ _ t1) (TForall _ _ t2) = analyseType env t1 t2
analyseType env (TStrict t1) t2 = analyseType env t1 t2
analyseType env t1 (TStrict t2) = analyseType env t1 t2 -- Remove all strict type information
analyseType _ (TVar _) (TVar _) = emptyMap -- Lift has a bug which might distort type variables, exact index doesn't matter
analyseType _ t1 t2 = error $ "analyseType: type mismatch: " ++ show (pretty t1) ++ " and " ++ show (pretty t2)

analyseAnn :: SAnn -> SAnn -> AnnotationEnvironment
analyseAnn (AnnVar x) y = singleMap x y
analyseAnn x (AnnVar y) = singleMap y x
analyseAnn _ _ = emptyMap

{-
Annotate
-}

annotateDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> (CoreDecl, IdSet)
annotateDeclaration env supply decl@DeclAbstract{} = (decl{declType = forallify True t}, is)
    where
        (t, is) = annotateType env supply (declType decl)
annotateDeclaration env supply decl@DeclCon{} = (decl{declType = forallify True t}, is)
    where
        (t, is) = annotateType env supply (declType decl)
annotateDeclaration env supply decl@DeclTypeSynonym{}
    -- String is the only type synonym which has to be annotated because it is partly hardcoded in the type system
    | declName decl == idFromString "String" = (decl{declType = forallify True t}, is)
    where
        (t, is) = annotateType env supply (declType decl)
annotateDeclaration _ _ decl = (decl, emptySet) -- Value is handled outside this method, others don't need anything

annotateType :: TypeEnvironment -> NameSupply -> Type -> (Type, IdSet)
annotateType env supply t
    -- Type is not in weak head normal form
    | t /= t' = annotateType env supply t'
        where
            t' = typeNormalizeHead env t
annotateType env supply t@(TForall _ KAnn _) = (t'', insertSet id is)
    -- Starts with strictness quantification, instantiate with fresh variable
    where
        (id, supply') = freshId supply
        (t', _) = annApplyList' t (AnnVar id) [] env
        (t'', is) = annotateType env supply' t'
annotateType env supply (TAp (TAp (TCon TConFun) t1) t2) = (TAp (TAp (TCon TConFun) t1'') t2', is)
    -- Function, place three annotations on the second argument (printed on the arrow)
    where
        (id1, id2, id3, supply') = threeIds supply
        (supply1, supply2) = splitNameSupply supply'
        (t1', is1) = annotateType env supply1 t1
        t1'' = TAp (TAnn $ AnnVar id1) $ TAp (TAnn $ AnnVar id2) $ TAp (TAnn $ AnnVar id3) t1'
        (t2', is2) = annotateType env supply2 t2
        is = insertSet id1 $ insertSet id2 $ insertSet id3 $ unionSet is1 is2
annotateType env supply (TAp t1 (TAp (TAnn a) (TAp (TAnn r) (TAp (TAnn a2) t2))))
    = (TAp t1' (TAp (TAnn a) (TAp (TAnn r) (TAp (TAnn a2) t2'))), unionSet i1 i2)
    -- Already annotated, no need to annotate again
    where
        (supply1, supply2) = splitNameSupply supply
        (t1', i1) = annotateType env supply1 t1
        (t2', i2) = annotateType env supply2 t2
annotateType env supply (TAp t1 t2) = (TAp t1' t2a, unionSets [is1, is2, is3])
    -- Annotate applications to datatypes
    where
        (id1, id2, id3, supply') = threeIds supply
        (supply1, supply2) = splitNameSupply supply'
        (t1', is1) = annotateType env supply1 t1
        (t2', is2) = annotateType env supply2 t2      
        t2a = TAp (TAnn $ AnnVar id1) (TAp (TAnn $ AnnVar id2) (TAp (TAnn $ AnnVar id3) t2'))
        is3 = setFromList [id1, id2, id3]
annotateType env supply (TForall q k t) = (TForall q k t', is)
    -- Non-strictness forall needs to stay
    where
        (t', is) = annotateType env supply t
annotateType env supply (TStrict t) = annotateType env supply t -- Strictness information is moved to annotations
annotateType _ _ t = (t, emptySet)

annotateBind :: Environment -> NameSupply -> Bind -> (Bind, IdSet)
annotateBind env supply (Bind (Variable x t) e) = (Bind (Variable x t') e, is)
  where
    (t', is) = annotateVarType env supply t

annotateVarType :: Environment -> NameSupply -> Type -> (Type, IdSet)
annotateVarType env supply t = (TAp (TAnn (AnnVar id1)) (TAp (TAnn (AnnVar id2)) (TAp (TAnn (AnnVar id3)) t')), is')
  where
    -- Fresh variables for relevance and both applicativeness
    (id1, id2, id3, supply') = threeIds supply
    -- Determine if the inner type has to be annotated as well
    (t', is) = annotateType (typeEnv env) supply' t
    -- Add ids to set of used ids
    is' = insertSet id1 $ insertSet id2 $ insertSet id3 is

{-
    Instantiate
-}

-- Instantiate expression
instantiateExpression :: TypeEnvironment -> NameSupply -> Expr -> (Expr, IdSet)
instantiateExpression env supply (Let b e) = (Let b' e, is)
    where
        -- Don't instantiate in the expression as the binding might end up quantified
        -- After a let binding, analyseExpression has to call instantiateExpression again
        (b', is) = instantiateBinds env supply b
instantiateExpression env supply (Match x a) = (Match x as, unionSets is)
    where
        (as, is) = unzip $ mapWithSupply (instantiateAlt env) supply a
instantiateExpression env supply (Ap e1 e2) = (Ap e1' e2', unionSet is1 is2)
    where
        (supply1, supply2) = splitNameSupply supply
        (e1', is1) = instantiateExpression env supply1 e1
        (e2', is2) = instantiateExpression env supply2 e2
instantiateExpression env supply (ApType e t) = (ApType e' t, is)
    where
        (e', is) = instantiateExpression env supply e
instantiateExpression env supply (Lam s v e) = (Lam s v e', is)
    where
        (e', is) = instantiateExpression (typeEnvAddVariable v env) supply e
instantiateExpression env supply (Forall q k e) = (Forall q k e', is)
    where
        (e', is) = instantiateExpression env supply e
instantiateExpression env supply e@(Var v) = instantiate env supply v e
instantiateExpression env supply e@(Con (ConId c)) = instantiate env supply c e
instantiateExpression _ supply e@(Lit (LitBytes _)) = (e', setFromList is)
    where
        (id1, id2, id3, _) = threeIds supply
        is = [id1, id2, id3]
        e' = foldl (\e'' i -> ApType e'' (TAnn (AnnVar i))) e is
instantiateExpression _ _ e = (e, emptySet)

-- Instantiate binds
instantiateBinds :: TypeEnvironment -> NameSupply -> Binds -> (Binds, IdSet)
instantiateBinds env supply (Strict b) = (Strict b', is)
    where
        (b', is) = instantiateBind env supply b
instantiateBinds env supply (NonRec b) = (NonRec b', is)
    where
        (b', is) = instantiateBind env supply b
instantiateBinds env supply b@(Rec bs) = (Rec bs', unionSets is)
    where
        env' = typeEnvAddBinds b env
        (bs', is) = unzip $ mapWithSupply (instantiateBind env') supply bs

-- Instantiate bind
instantiateBind :: TypeEnvironment -> NameSupply -> Bind -> (Bind, IdSet)
instantiateBind env supply (Bind (Variable x t) e) = (Bind (Variable x t) e', is)
    where
        (e', is) = instantiateExpression env supply e

-- Instantiate alt
instantiateAlt :: TypeEnvironment -> NameSupply -> Alt -> (Alt, IdSet)
instantiateAlt env supply (Alt p e) = (Alt p' e', unionSet is1 is2)
    where
        (supply1, supply2) = splitNameSupply supply
        (p', is1) = instantiatePat env supply1 p
        (e', is2) = instantiateExpression (typeEnvAddPattern p' env) supply2 e

-- Instantiate pat  
instantiatePat :: TypeEnvironment -> NameSupply -> Pat -> (Pat, IdSet)
instantiatePat env supply (PatCon (ConId c) t i) = (PatCon (ConId c) t' i, setFromList ids)
    where
        -- Add more ids for the extra foralls
        t' = map (TAnn . AnnVar) ids ++ t
        ids = mapWithSupply (\x _ -> fst $ freshId x) supply n
        n = getForalls env $ typeOfId env c
instantiatePat _ _ p = (p, emptySet)

-- Instantiate variable or constructor
instantiate :: TypeEnvironment -> NameSupply -> Id -> Expr -> (Expr, IdSet)
instantiate env supply id e = (foldr (\x e' -> ApType e' (TAnn (AnnVar x))) e ids, setFromList ids)
    where
        -- Get all foralls, add an ApType with fresh variable
        ids = mapWithSupply (\x _ -> fst $ freshId x) supply $ getForalls env (typeOfId env id)

{-
    Simplification and transformation
-}

-- Solve part of the constraint set in a let-binding
simplify :: Constraints -> AnnotationEnvironment -> Environment -> Analysis ()
simplify cs ae env = Analysis () (S.map (mapConstraint sc) lc) (mapMap (replaceVar sc) la) sc
    where
        is = vars env
        -- Partition constraint in those allowed to be solved and not
        (lc, rc) = S.partition (blockedConstraint is) cs
        -- Partition annotation environment in those allowed to be solved and not
        (la, ra) = partitionMapWithId (\id _ -> id `elemSet` is) ae
        ac = annEnvToConstraints ra
        cs' = S.union rc ac
        sc = solveConstraints cs'

-- Apply strict annotations on bind
transformBind' :: Environment -> SolvedConstraints -> Bind -> (Bind, IdSet)
transformBind' env sc (Bind (Variable x (TAp a1 (TAp r (TAp a2 _)))) e) = (Bind (Variable x t'') e, is)
  where
    -- Get type of binding, apply solved constraints and forallify
    t' = forallify False $ transformType sc True False $ typeOfCoreExpression (typeEnv env) e
    -- Reinstate annotations belonging to variable itself which are yet to be answered
    t'' = TAp a1 $ TAp r $ TAp a2 t'
    -- Add used annotation variables
    is = setFromList $ getVariablesType True t'
