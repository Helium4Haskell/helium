module Helium.CodeGeneration.Core.BindingGroup where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Common.IdSet
import Lvm.Core.Expr
import Lvm.Core.Module
import Lvm.Core.Type
import qualified Data.Graph as Graph
import Text.PrettyPrint.Leijen

import Debug.Trace

data BindingGroup a
  = BindingRecursive [Decl a]
  | BindingNonRecursive (Decl a)

instance Pretty a => Pretty (BindingGroup a) where
  pretty (BindingRecursive bs) = pretty bs
  pretty (BindingNonRecursive b) = pretty b

bindingGroupToList :: BindingGroup a -> [Decl a]
bindingGroupToList (BindingRecursive as) = as
bindingGroupToList (BindingNonRecursive a) = [a]

bindingGroupsToMap :: [BindingGroup a] -> IdMap Id
bindingGroupsToMap = foldr handleGroup emptyMap
  where
    handleGroup :: BindingGroup a -> IdMap Id -> IdMap Id
    handleGroup (BindingNonRecursive decl) env = insertMap (declName decl) (declName decl) env
    handleGroup (BindingRecursive (decl : decls)) env =
      insertMap (declName decl) (declName decl) $ foldr (\d e -> insertMap (declName d) (declName decl) e) env decls

bindingGroups :: (a -> [Id]) -> [Decl a] -> [BindingGroup a]
bindingGroups dependencies = map toBindingGroup . Graph.stronglyConnComp . map toNode
  where
    toNode decl@(DeclValue name _ _ _ _ a _) = (decl, name, dependencies a)
    toNode decl                              = (decl, declName decl, [])
    toBindingGroup (Graph.AcyclicSCC decl) = BindingNonRecursive decl
    toBindingGroup (Graph.CyclicSCC decls) = BindingRecursive decls

-- Assumes unique identifiers, i.e. rename pass is executed before binding group analysis
coreBindingGroups :: [CoreDecl] -> [BindingGroup Expr]
coreBindingGroups = bindingGroups exprDependencies
    where
        exprDependencies (Let b e)      = bindsDependencies b ++ exprDependencies e
        exprDependencies (Match _ as)   = concatMap altDependencies as
        exprDependencies (Ap e1 e2)     = exprDependencies e1 ++ exprDependencies e2
        exprDependencies (ApType e _)   = exprDependencies e
        exprDependencies (Lam _ _ e)    = exprDependencies e
        exprDependencies (Forall _ _ e) = exprDependencies e
        exprDependencies (Var x)        = [x]
        exprDependencies _              = []

        bindsDependencies (Strict b) = bindDependencies b
        bindsDependencies (NonRec b) = bindDependencies b
        bindsDependencies (Rec bs)   = concatMap bindDependencies bs
        bindDependencies  (Bind _ e) = exprDependencies e
        altDependencies   (Alt _ e)  = exprDependencies e

mapBindingGroup :: (Decl a -> Decl b) -> BindingGroup a -> BindingGroup b
mapBindingGroup f (BindingNonRecursive a) = BindingNonRecursive $ f a
mapBindingGroup f (BindingRecursive as)   = BindingRecursive $ map f as