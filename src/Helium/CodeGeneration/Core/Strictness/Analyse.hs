module Helium.CodeGeneration.Core.Strictness.Analyse (analyseModule, analyseDeclaration, analyseValue) where

import qualified Data.Set as S

import Helium.CodeGeneration.Core.Strictness.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type

import Text.PrettyPrint.Leijen (pretty)

-- Run strictness analysis on module
analyseModule :: CoreModule -> Constraints
analyseModule mod = S.unions $ map (analyseDeclaration $ typeEnvForModule mod) (moduleDecls mod)

-- Run strictness analysis on declaration
analyseDeclaration :: TypeEnvironment -> CoreDecl -> Constraints
analyseDeclaration env decl@DeclValue{} = analyseValue env (valueValue decl, declType decl)
analyseDeclaration _ _ = S.empty

-- Run strictness analysis on function
analyseValue :: TypeEnvironment -> (Expr, Type) -> Constraints
analyseValue env (e, t) = S.unions [c1, c2, c3]
  where
    env' = Environment env emptyMap emptyMap
    -- Annotation environment and constraints from body
    (ae, c1) = analyseExpression env' S (setApplicativeness env' t) e
    -- Turn annotation environment into constraints
    c2 = annEnvToConstraints ae
    -- Constraints on type-body relations
    c3 = analyseType env' True t (typeOfCoreExpression env True e)

-- Run strictness analysis on expressions
analyseExpression :: Environment -> SAnn -> SAnn -> Expr -> (AnnotationEnvironment, Constraints)
analyseExpression env rel app (Let b e) = (ae, cs)
  where
    ae = unionMapWith meet a1 a2'
    -- Analyse bind
    (a1, c1, app') = analyseBinds env rel b
    -- Analyse body      
    (a2, c2) = analyseExpression (envAddBinds b env) S app' e
    a2' = unionMapWith join a2 $ containment env rel
    cs = S.insert (app `Constraint` app') $ S.union c1 c2
analyseExpression env rel app (Match _ alts) = (unionMapsWith join ae, S.unions cs)
  where
    -- Only if an expression is strict on all alts it is strict
    (ae, cs) = unzip $ map (analyseAlt env rel app) alts
analyseExpression env rel app (Ap e1 e2) = (ae, cs)
  where
    ae = unionMapWith meet ae1 ae2
    cs = S.insert (app `Constraint` a2) $ S.unions [c1, c2, c3]
    -- Analyse function
    (ae1, c1) = analyseExpression env rel rel e1
    -- Get annotation from function
    t = typeNormalizeHead (typeEnv env) $ typeOfCoreExpression (typeEnv env) True e1
    (TAp (TAp (TCon TConFun) (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t')))) _) = t
    -- If argument is function, get constraints for the instantiation
    c3 = analyseType env False t' $ typeOfCoreExpression (typeEnv env) True e2
    -- Analyse applicant under the join of the annotations and the relevance context
    (ae2, c2) = analyseExpression env (join rel r) (join rel a1) e2
analyseExpression env rel app (ApType e _) = analyseExpression env rel app e
analyseExpression env _ app (Lam _ v@(Variable _ (TAp _ (TAp _ (TAp (TAnn a2) _)))) e) = (ae', cs)
  where
    -- Expression in S relevance to see if the variable is strict, but contain with applicative
    (ae, cs) = analyseExpression (envAddVariable v env) S a2 e
    ae' = unionMapWith join ae $ containment env app
analyseExpression env rel app (Forall _ _ e) = analyseExpression env rel app e
analyseExpression env rel app (Var v) = (unionMapWith meet (getLConstraints env) ae, S.empty)
  where
    ae = getAnnotations env rel app v
analyseExpression env _ _ _ = (getLConstraints env, S.empty) -- Lit and Con

-- Run strictness analysis on alts
analyseAlt :: Environment -> SAnn -> SAnn -> Alt -> (AnnotationEnvironment, Constraints)
analyseAlt env rel app (Alt pat e) = analyseExpression (envAddPattern pat env) rel app e

-- Run strictness analysis on binds
analyseBinds :: Environment -> SAnn -> Binds -> (AnnotationEnvironment, Constraints, SAnn)
analyseBinds env rel (Strict b) = analyseBind env rel b
analyseBinds env rel (NonRec b) = analyseBind env rel b
analyseBinds env rel b@(Rec bs) = (unionMapsWith meet ae, S.unions cs, foldr join S ap)
  where
    (ae, cs, ap) = unzip3 $ map (analyseBind (envAddBinds b env) rel) bs

-- Run strictness analysis on bind
analyseBind :: Environment -> SAnn -> Bind -> (AnnotationEnvironment, Constraints, SAnn)
analyseBind env rel (Bind (Variable _ (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t)))) e) = (ae, S.union c1 c2, a2)
  where
    (ae, c1) = analyseExpression env (join rel r) (join rel a1) e
    c2 = analyseType env True t $ typeOfCoreExpression (typeEnv env) True e

-- Analyse type
analyseType :: Environment -> Bool -> Type -> Type -> Constraints
analyseType env err (TAp (TAp (TCon TConFun) t11) t12) (TAp (TAp (TCon TConFun) t21) t22) = S.union c1 c2
  where
    -- Functions
    c1 = analyseType env err t11 t21
    c2 = analyseType env err t12 t22
analyseType env err (TAp (TAnn a1) (TAp (TAnn r) (TAp (TAnn a2) t1))) (TAp (TAnn a1') (TAp (TAnn r') (TAp (TAnn a2') t2))) = S.union c1 c2
  where
    -- Annotated arrows
    c1 = S.fromList [a1' `Constraint` a1, r' `Constraint` r, a2' `Constraint` a2]
    c2 = analyseType env err t1 t2
analyseType env err (TAp t11 t12) (TAp t21 t22) | t11 == t21 = S.union c1 c2
  where
    -- Other applications
    c1 = analyseType env err t11 t21
    c2 = analyseType env err t12 t22
analyseType env err (TStrict t1) t2 = analyseType env err t1 t2
analyseType env err t1 (TStrict t2) = analyseType env err t1 t2 -- Remove all strict type information
analyseType env err (TForall _ _ t1) t2 = analyseType env err t1 t2
analyseType env err t1 (TForall _ _ t2) = analyseType env err t1 t2 -- Remove all foralls
analyseType env err t1 t2
  | t1 == t2               = S.empty
  | t1 /= t1' || t2 /= t2' = analyseType env err t1' t2' -- Normalization changed type, try again
  | err                    = error $ "analyseType: type mismatch: " ++ show (pretty t1) ++ " and " ++ show (pretty t2)
  | otherwise              = S.empty -- Ignore errors with DeBruijn indices in applications
    where
      t1' = typeNormalizeHead (typeEnv env) t1
      t2' = typeNormalizeHead (typeEnv env) t2

-- Make a L constraint for all annotation variables
getLConstraints :: Environment -> ApplicativenessEnvironment
getLConstraints = mapFromList . map (\x -> (x, L)) . getAnnotationVariablesEnv

-- Get relevance and applicative annotations of var, set them equal to contexts
getAnnotations :: Environment -> SAnn -> SAnn -> Id -> ApplicativenessEnvironment
getAnnotations (Environment _ relEnv appEnv) rel app var = unionMap (f relEnv rel) (f appEnv app)
  where
    f env con = case lookupMap var env of
      Just (AnnVar a) -> singleMap a con
      _ -> emptyMap

-- Containment
containment :: Environment -> SAnn -> AnnotationEnvironment
containment env con = mapFromList $ map (\x -> (x, con)) (getAnnotationVariablesEnv env)

-- Set applicative context to S or L depending on the arity of the type
setApplicativeness :: Environment -> Type -> SAnn
setApplicativeness (Environment env _ _) t = case arityFromType $ typeNormalizeHead env t of
  0 -> S
  _ -> L
