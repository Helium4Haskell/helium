module Helium.CodeGeneration.Core.Strictness.Transform (transformModule) where

import Helium.CodeGeneration.Core.Strictness.Analyse
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Type
import Lvm.Core.Module

-- Apply strict annotations on module
transformModule :: Constraints -> CoreModule -> CoreModule
transformModule cs mod = mod{moduleDecls = map (transformDeclaration cs) (moduleDecls mod)}  

-- Apply strict annotations on declarations
transformDeclaration :: Constraints -> CoreDecl -> CoreDecl
transformDeclaration env decl@DeclValue{} = decl{valueValue = transformExpression env $ valueValue decl}
transformDeclaration _ decl = decl

-- Apply strict annotations on expressions
transformExpression :: Constraints -> Expr -> Expr
transformExpression env (Let (Rec b) e) = Let (Rec b) $ transformExpression env e
transformExpression env (Let (NonRec (Bind (Variable x (TAnn (AnnVar a) t)) e1)) e2) = Let b e2' -- No transformation possible
  where
    r = if findMap a env == S then Strict else NonRec -- Turn bind to strict if annotated with S
    b = r (Bind (Variable x t) e1')
    e1' = transformExpression env e1
    e2' = transformExpression env e2
transformExpression env (Let (Strict (Bind (Variable x (TAnn (AnnVar _) t)) e1)) e2) = Let b e2'
  where
    b = Strict (Bind (Variable x t) e1') -- Bind is already strict so annotation is irrelevant
    e1' = transformExpression env e1
    e2' = transformExpression env e2
transformExpression env (Match i alts) = Match i $ map (transformAlt env) alts
transformExpression env (Ap e1 e2) = Ap e1' e2'
  where
    e1' = transformExpression env e1
    e2' = transformExpression env e2
transformExpression env (ApType e t) = ApType (transformExpression env e) t
transformExpression env (Lam s (Variable x (TAnn (AnnVar a) t)) e) = Lam s' (Variable x t) e' 
  where
    s'  = s || (findMap a env == S) -- Lambda might already be strict
    e' = transformExpression env e
transformExpression env (Forall q k e) = Forall q k $ transformExpression env e
transformExpression _ expr = expr -- Con and Lit

-- Apply strict annotations on alts
transformAlt :: Constraints -> Alt -> Alt
transformAlt env (Alt p e) = Alt p $ transformExpression env e