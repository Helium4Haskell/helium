module Helium.CodeGeneration.Core.Strictness.Monovariant (monovariantStrictness) where

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
data Analysis a = Analysis a Constraints AnnotationEnvironment

mergeAnalysis :: (SAnn -> SAnn -> SAnn) -> [Analysis a] -> Analysis [a]
mergeAnalysis _ [] = Analysis [] S.empty emptyMap
mergeAnalysis f (x:xs) = Analysis (v:v') (S.union c c') (unionMapWith f a a')
    where
        Analysis v c a = x
        Analysis v' c' a' = mergeAnalysis f xs

type GroupData = ([CoreDecl], Constraints, TypeEnvironment, NameSupply)
type CoreGroup = BindingGroup Expr

monovariantStrictness :: NameSupply -> CoreModule -> CoreModule
monovariantStrictness supply mod = mod {moduleDecls = decls1 ++ map resetDeclaration others' ++ values''}
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
    (values', cs, env'', _) = foldl groupStrictness ([], S.empty, env', supply2) groups
    -- Solve constraints
    sc = solveConstraints cs
    -- Transform declarations based on solved constraints
    values'' = map (transformDeclaration sc env'') values'

groupStrictness :: GroupData -> CoreGroup -> GroupData
-- Single declaration
groupStrictness (b, cs, env, supply) (BindingNonRecursive d) = (b ++ [d'], S.union cs cs2, env', supply2)
  where
    (supply1, supply2) = splitNameSupply supply
    -- Analyse function
    Analysis e cs' ae = analyseDeclaration env supply1 d
    -- Update declaration
    d' = d{valueValue = e}
    -- Add strictness type to environment
    env' = typeEnvAddGlobalValue (declName d) (typeOfCoreExpression env e) env
    -- Convert merge environment to constraints
    cs2 = S.union cs' $ annEnvToConstraints ae
-- Group of recursive declarations
groupStrictness (b, cs, env, supply) (BindingRecursive ds) = (b ++ ds', S.union cs cs2, env'', supply3)
  where
    (supply1, supply') = splitNameSupply supply
    (supply2, supply3) = splitNameSupply supply'
    -- Annotate type signatures and add them to the environment
    ts = mapWithSupply (\s d -> annotateType env s $ declType d) supply1 ds
    env' = typeEnvAddGlobalValues (map (\(d, t) -> (declName d, t)) (zip ds ts)) env
    -- Run analysis on all bodies, merge information with meet
    Analysis es cs' ae = mergeAnalysis meet $ mapWithSupply (analyseDeclaration env') supply2 ds
    -- Update declarations
    ds' = map (\(d, e) -> d{valueValue = e}) (zip ds es)
    -- Add strictness types to environment
    ts' = map (typeOfCoreExpression env') es
    env'' = typeEnvAddGlobalValues (map (\(d, t) -> (declName d, t)) (zip ds ts')) env
    -- Convert merge environment to constraints
    cs2 = S.union cs' $ annEnvToConstraints ae

{-
    Analyse
-}

analyseDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> Analysis Expr
analyseDeclaration typeEnv supply decl@DeclValue{} = Analysis e cs ae
    where
        -- Create empty environment
        env = Environment typeEnv emptyMap emptyMap emptySet
        -- Run analysis, always start in S contexts
        Analysis e cs ae = analyseExpression env S S supply $ valueValue decl

analyseExpression :: Environment -> SAnn -> SAnn -> NameSupply -> Expr -> Analysis Expr
analyseExpression env rel app supply (Let b e) = Analysis (Let b' e') cs (unionMapWith meet a1 as)
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse binds
        (Analysis b' c1 a1, app') = analyseBinds env supply1 rel b
        -- Add annotated binds to environment
        env' = envAddBinds b' env
        -- Analyse body, set contexts to S
        Analysis e' c2 a2 = analyseExpression env' S S supply2 e
        -- Containment on old environment
        as = unionMapWith join a2 $ containment env rel
        -- Add constraint on applicativeness
        cs = S.insert (app `Constraint` app') $ S.union c1 c2
analyseExpression env rel app supply (Match id a) = Analysis (Match id a') c ae
    where
        -- Merge with join as strictness has to occur in every case
        Analysis a' c ae = mergeAnalysis join $ mapWithSupply (analyseAlt env rel app id) supply a
analyseExpression env rel app supply (Ap e1 e2) = Analysis (Ap e1' e2') cs (unionMapsWith meet [ae1, ae2, ae3])
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse function, with applicative context set to relevance
        Analysis e1' c1 ae1 = analyseExpression env rel rel supply1 e1
        -- Get type of function
        t = typeNormalizeHead (typeEnv env) $ typeOfCoreExpression (typeEnv env) e1'
        -- Get the annotations on the function arrow
        (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t')))) _) = t
        -- Analyse argument with context of the previous annotations
        Analysis e2' c2 ae2 = analyseExpression env (join rel r) (join rel a1) supply2 e2
        -- Add constraint on applicativeness
        cs = S.insert (app `Constraint` a2) $ S.union c1 c2
        -- Annotation unifications between the function and the given argument
        ae3 = analyseType env t' $ typeOfCoreExpression (typeEnv env) e2'
analyseExpression env rel app supply (ApType e t) = Analysis (ApType e' t') c a
    where
        (supply1, supply2) = splitNameSupply supply
        -- Annotate type, if it is a tuple place extra annotations
        t' = if isTupAp e then annotateVarType env supply1 t else annotateType (typeEnv env) supply1 t
        -- Analyse expression
        Analysis e' c a = analyseExpression env rel app supply2 e
analyseExpression env _ app supply (Lam s (Variable x t) e) = Analysis (Lam s v' e') c a''
    where
        (id1, id2, id3, supply') = threeIds supply
        (supply1, supply2) = splitNameSupply supply'
        -- Annotate type in variable
        t' = annotateType (typeEnv env) supply1 t
        -- Give three annotations to variable
        v' = Variable x (TAp (TAnn (AnnVar id1)) (TAp (TAnn (AnnVar id2)) (TAp (TAnn (AnnVar id3)) t')))
        -- Add variable  to environment
        env' = envAddVariable v' env
        -- Analyse expression, set relevance to S
        Analysis e' c a = analyseExpression env' S (AnnVar id3) supply2 e
        -- Containment on old environment
        a' = unionMapWith join a $ containment env app
        -- If lambda was strict, set its annotation variables equal to the second applicative
        a'' = if s then updateMap id1 (AnnVar id3) (updateMap id2 (AnnVar id3) a') else a'
analyseExpression env rel app supply (Forall q k e) = Analysis (Forall q k e') c a
    where
        -- Forall can be ignored
        Analysis e' c a = analyseExpression env rel app supply e
analyseExpression env _ _ _ (Con c) = Analysis (Con c) S.empty (getLConstraints env) -- Set all annotation variables to L
analyseExpression env rel app _ (Var v) = Analysis (Var v) S.empty (unionMapWith meet (getLConstraints env) ae)
    where
        -- Set all annotation variables to L except the annotations related to this variable, which are set to context
        ae = getAnnotations env rel app v
analyseExpression env _ _ _ (Lit l) = Analysis (Lit l) S.empty (getLConstraints env) -- Set all annotation variables to L

analyseBinds :: Environment -> NameSupply -> SAnn -> Binds -> (Analysis Binds, SAnn)
analyseBinds env supply rel (Rec bs) = (Analysis (Rec bs') c a, foldr join S app)
    where
        -- Annotate types beforehand because they occur in the body
        bs'' = mapWithSupply (annotateBind env) supply bs
        -- Add binds  to environment
        env' = envAddBinds (Rec bs'') env
        -- Run analysis on every bind separately
        (xs, app) = unzip $ mapWithSupply (analyseRecBind env' rel) supply bs''
        -- Merge the results with meet, as being strict in one bind is enough
        Analysis bs' c a = mergeAnalysis meet xs
analyseBinds env supply rel (NonRec b) = (Analysis (NonRec b') c a, app)
    where
        -- Run analysis on bind
        (Analysis b' c a, app) = analyseBind env rel supply b
analyseBinds env supply rel (Strict b) = (Analysis (Strict b') c a', app)
    where
        -- Run analysis on bind
        (Analysis b' c a, app) = analyseBind env rel supply b
        -- Set variables associated to this strict bind to strict
        a' = strictBind b' a

analyseRecBind :: Environment -> SAnn -> NameSupply -> Bind -> (Analysis Bind, SAnn)
analyseRecBind env rel supply (Bind v e) = (Analysis (Bind v e') c a, a2)
    where
        -- Get annotations from variable previously annotated
        Variable _ (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) _))) = v
        -- Run analysis on binding with relevance and applicative joined with context
        Analysis e' c a = analyseExpression env (join rel r) (join rel a1) supply e 

analyseBind :: Environment -> SAnn -> NameSupply -> Bind -> (Analysis Bind, SAnn)
analyseBind env rel supply (Bind (Variable x _) e) = (Analysis (Bind (Variable x t') e') c a, AnnVar id3)
    where
        -- Fresh variables for relevance and both applicativeness
        (id1, id2, id3, supply') = threeIds supply
        -- Add annotations outside the type
        t = typeOfCoreExpression (typeEnv env) e'
        t' = TAp (TAnn (AnnVar id1)) (TAp (TAnn (AnnVar id2)) (TAp (TAnn (AnnVar id3)) t))
        -- Run analysis on binding with relevance and applicative joined with context
        Analysis e' c a = analyseExpression env (join rel (AnnVar id2)) (join rel (AnnVar id1)) supply' e   
        
analyseAlt :: Environment -> SAnn -> SAnn -> Id -> NameSupply -> Alt -> Analysis Alt
analyseAlt env rel app id supply (Alt p e) = Analysis (Alt p' e') c2 (unionMapWith meet a1 a2)
    where
        (supply1, supply2) = splitNameSupply supply
        -- Analyse the pattern, only the annotation environment has possibly additional information
        Analysis p' _ a1 = analysePat env id supply1 p
        -- Add pattern to environment
        env' = envAddPattern p' env
        -- Run analysis 
        Analysis e' c2 a2 = analyseExpression env' rel app supply2 e

analysePat :: Environment -> Id -> NameSupply -> Pat -> Analysis Pat
analysePat env id supply (PatCon (ConTuple n) t i) = Analysis (PatCon (ConTuple n) t' i) S.empty ae
  where
    -- In case of a tuple, all types need three extra annotations to communicate the return annotations of the tuple
    t' = mapWithSupply (annotateVarType env) supply t
    -- Get equalities between type of id matched on and type of pattern
    ae = analyseType env (typeOfId (typeEnv env) id) (foldl TAp (TCon (TConTuple n)) t')
analysePat env _ supply (PatCon c t i) = Analysis (PatCon c t' i) S.empty emptyMap
    where
        -- Annotate all types given to constructor
        t' = mapWithSupply (annotateType (typeEnv env)) supply t
analysePat _ _ _ p = Analysis p S.empty emptyMap -- Literal or default, no information to be gained

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

annotateDeclaration :: TypeEnvironment -> NameSupply -> CoreDecl -> CoreDecl
annotateDeclaration env supply decl@DeclAbstract{} = decl{declType = annotateType env supply (declType decl)}
annotateDeclaration env supply decl@DeclCon{} = decl{declType = annotateType env supply (declType decl)}
annotateDeclaration env supply decl@DeclTypeSynonym{}
    -- String is the only type synonym which has to be annotated because it is partly hardcoded in the type system
    | declName decl == idFromString "String" = decl{declType = annotateType env supply (declType decl)}
annotateDeclaration _ _ decl = decl -- Value is handled outside this method, others don't need anything

annotateType :: TypeEnvironment -> NameSupply -> Type -> Type
annotateType env supply t
    -- Type is not in weak head normal form
    | t /= t' = annotateType env supply t'
        where
            t' = typeNormalizeHead env t
annotateType env supply (TAp (TAp (TCon TConFun) t1) t2) = TAp (TAp (TCon TConFun) t1'') t2'
    -- Function, place three annotations on the second argument (printed on the arrow)
    where
        (id1, id2, id3, supply') = threeIds supply
        (supply1, supply2) = splitNameSupply supply'
        t1'  = annotateType env supply1 t1
        t1'' = TAp (TAnn $ AnnVar id1) $ TAp (TAnn $ AnnVar id2) $ TAp (TAnn $ AnnVar id3) t1'
        t2'  = annotateType env supply2 t2
annotateType env supply (TAp t1 (TAp (TAnn a) (TAp (TAnn r) (TAp (TAnn a2) t2))))
    = TAp t1' (TAp (TAnn a) (TAp (TAnn r) (TAp (TAnn a2) t2')))
    -- Already annotated, no need to annotate again
    where
        (supply1, supply2) = splitNameSupply supply
        t1' = annotateType env supply1 t1
        t2' = annotateType env supply2 t2
annotateType env supply (TAp t1 t2) = TAp t1' t2a
    -- Annotate applications to datatypes
    where
        (id1, id2, id3, supply') = threeIds supply
        (supply1, supply2) = splitNameSupply supply'
        t1' = annotateType env supply1 t1
        t2' = annotateType env supply2 t2      
        t2a = TAp (TAnn $ AnnVar id1) (TAp (TAnn $ AnnVar id2) (TAp (TAnn $ AnnVar id3) t2'))
annotateType env supply (TForall q k t) = TForall q k $ annotateType env supply t -- Non-strictness forall needs to stay
annotateType env supply (TStrict t) = annotateType env supply t -- Strictness information is moved to annotations
annotateType _ _ t = t

annotateBind :: Environment -> NameSupply -> Bind -> Bind
annotateBind env supply (Bind (Variable x t) e) = Bind (Variable x t') e
  where
    t' = annotateVarType env supply t

annotateVarType :: Environment -> NameSupply -> Type -> Type
annotateVarType env supply t = TAp (TAnn (AnnVar id1)) (TAp (TAnn (AnnVar id2)) (TAp (TAnn (AnnVar id3)) t'))
  where
    -- Fresh variables for relevance and both applicativeness
    (id1, id2, id3, supply') = threeIds supply
    -- Determine if the inner type has to be annotated as well
    t' = annotateType (typeEnv env) supply' t

{-
    Transform
-}

-- Apply strict annotations on declarations
transformDeclaration :: SolvedConstraints -> TypeEnvironment -> CoreDecl -> CoreDecl
transformDeclaration sc env decl@DeclValue{} = decl{valueValue = v, declCustoms = c}
  where
    v = transformExpression sc $ valueValue decl
    t = transformType sc (accessPublic $ declAccess decl) $ typeOfCoreExpression env $ valueValue decl
    c = strictnessToCustom t $ declCustoms decl
transformDeclaration sc _ decl@DeclAbstract{}    = transformDeclarationAbstract sc decl
transformDeclaration sc _ decl@DeclCon{}         = transformDeclarationAbstract sc decl
transformDeclaration sc _ decl@DeclTypeSynonym{} = transformDeclarationAbstract sc decl
transformDeclaration _  _ decl                   = decl

transformDeclarationAbstract :: SolvedConstraints -> CoreDecl -> CoreDecl
transformDeclarationAbstract sc decl = decl{declType = transformType sc (accessPublic $ declAccess decl) $ declType decl}

-- Apply strict annotations on types
transformType :: SolvedConstraints -> Bool -> Type -> Type
transformType sc acc (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1)))) t2) =
  TAp (TAp (TCon TConFun) t1') t2'
    where
      -- If the function is exported and we're not in the last argument, we have to set applicativeess to L
      export = (arityFromType t2 /= 0) && acc
      a1' = lookupVarMono a1 sc export
      r'  = lookupVarMono r sc False
      a2' = lookupVarMono a2 sc export
      t1' = TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') (transformType sc acc t1)))
      t2' = transformType sc acc t2
transformType sc acc (TAp t1 t2) = TAp (transformType sc acc t1) (transformType sc acc t2)
transformType sc _ (TAnn a) = TAnn $ lookupVarMono a sc False
transformType sc acc (TStrict t) = transformType sc acc t
transformType sc acc (TForall q k t) = TForall q k $ transformType sc acc t
transformType _ _ t = t

-- Apply strict annotations on expressions
transformExpression :: SolvedConstraints -> Expr -> Expr
transformExpression sc (Let b e) = Let (transformBinds sc b) $ transformExpression sc e
transformExpression sc (Match i alts) = Match i $ map (transformAlt sc) alts
transformExpression sc (Ap e1 e2) = Ap e1' e2'
  where
    e1' = transformExpression sc e1
    e2' = transformExpression sc e2
transformExpression sc (ApType e t) = case t of
  TAnn _ -> transformExpression sc e
  _      -> ApType (transformExpression sc e) (typeRemoveAnnotations t)
transformExpression sc (Lam s (Variable x (TAp (TAnn a) (TAp (TAnn r) (TAp _ t)))) e) = Lam (s || s') (Variable x t') e' 
  where
    -- Lookup variables, polyvariant search because we need to check if it is not L
    a' = lookupVar a sc
    r' = lookupVar r sc
    -- Lam can be made strict if it is strict when fully applied, i.e. when a' becomes S
    s' = uncontain (getVariablesAnn a') r' == S
    e' = transformExpression sc e
    t' = typeRemoveAnnotations t
transformExpression sc (Forall q k e) = Forall q k $ transformExpression sc e
transformExpression _ e = e -- Con, Lit and Var

-- Apply strict transformations on binds
transformBinds :: SolvedConstraints -> Binds -> Binds
transformBinds sc (Strict b) = Strict $ transformBind sc b
transformBinds sc (NonRec b) = if bindToStrict sc b then Strict b' else NonRec b'
  where
    b' = transformBind sc b
transformBinds sc (Rec bs) = Rec $ map (transformBind sc) bs

-- Apply strict annotations on bind
transformBind :: SolvedConstraints -> Bind -> Bind
transformBind sc (Bind (Variable x (TAp _ (TAp _ (TAp _ t)))) e) = Bind (Variable x t') e'
  where
    t' = typeRemoveAnnotations t
    e' = transformExpression sc e

-- Apply strict transformations on alts
transformAlt :: SolvedConstraints -> Alt -> Alt
transformAlt sc (Alt p e) = Alt p' e'
  where
    p' = transformPat p
    e' = transformExpression sc e

-- Apply strict transformations on pats
transformPat :: Pat -> Pat
transformPat (PatCon c t i) = PatCon c (map typeRemoveAnnotations $ removeAnn t) i
transformPat p = p

-- Lookup annotation of variables
lookupVarMono :: SAnn -> SolvedConstraints -> Bool -> SAnn
lookupVarMono (AnnVar x) sc export | elemMap x sc = case findMap x sc of
  S -> if export then L else S
  _ -> L
lookupVarMono S _ _ = S
lookupVarMono _ _ _ = L
