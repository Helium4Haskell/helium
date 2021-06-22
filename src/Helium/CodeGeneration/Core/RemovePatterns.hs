module Helium.CodeGeneration.Core.RemovePatterns (coreRemovePatterns) where

-- Removes unreachable patterns in case expressions
-- At the moment, only default patterns when unpacking tuples are removed

import Lvm.Core.Expr
import Lvm.Core.Module

coreRemovePatterns :: CoreModule -> CoreModule
coreRemovePatterns mod = mod{moduleDecls = map analyseDeclaration $ moduleDecls mod}

analyseDeclaration :: CoreDecl -> CoreDecl
analyseDeclaration decl@DeclValue{} = decl{valueValue = analyseExpression $ valueValue decl}
analyseDeclaration decl = decl

analyseExpression :: Expr -> Expr
analyseExpression (Let b e) = Let (analyseBinds b) $ analyseExpression e
analyseExpression (Match id as) = Match id $ analyseAlts as
analyseExpression (Ap e1 e2) = Ap (analyseExpression e1) $ analyseExpression e2
analyseExpression (ApType e t) = ApType (analyseExpression e) t
analyseExpression (Lam s v e) = Lam s v $ analyseExpression e
analyseExpression (Forall q k e) = Forall q k $ analyseExpression e
analyseExpression e = e -- Con, Var and Lit

analyseBinds :: Binds -> Binds
analyseBinds (Strict b) = Strict $ analyseBind b
analyseBinds (NonRec b) = NonRec $ analyseBind b
analyseBinds (Rec bs)   = Rec $ map analyseBind bs

analyseBind :: Bind -> Bind
analyseBind (Bind v e) = Bind v $ analyseExpression e

analyseAlts :: Alts -> Alts
analyseAlts (a:as) = case a of
    -- First case is tuple, only that case is enough
    Alt (PatCon (ConTuple _) _ _) _ -> [analyseAlt a]
    -- First case is not a tuple, keep entire alts
    _                               -> map analyseAlt (a:as)
-- Untriggerable case as every alts should have at least one alt, but just in case...
analyseAlts [] = []

analyseAlt :: Alt -> Alt
analyseAlt (Alt p e) = Alt p $ analyseExpression e
