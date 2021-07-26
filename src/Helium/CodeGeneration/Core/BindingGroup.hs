module Helium.CodeGeneration.Core.BindingGroup where

import Data.Either
import qualified Data.Graph as Graph

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Expr
import Lvm.Core.Module

import Text.PrettyPrint.Leijen

data BindingGroup a
  = BindingRecursive [Decl a] -- (Self-)recursive functions
  | BindingNonRecursive (Decl a) -- Non-recursive functions
  | BindingNonFunction [Decl a] -- Abstract, constructors, synonyms etc.

instance Pretty a => Pretty (BindingGroup a) where
  pretty (BindingRecursive bs) = pretty bs
  pretty (BindingNonRecursive b) = pretty b
  pretty (BindingNonFunction bs) = pretty bs

bindingGroupToList :: BindingGroup a -> [Decl a]
bindingGroupToList (BindingRecursive bs) = bs
bindingGroupToList (BindingNonRecursive b) = [b]
bindingGroupToList (BindingNonFunction bs) = bs

bindingGroupsToMap :: [BindingGroup a] -> IdMap Id
bindingGroupsToMap = foldr handleGroup emptyMap
  where
    handleGroup :: BindingGroup a -> IdMap Id -> IdMap Id
    handleGroup (BindingRecursive decls) env = handleMulti decls env
    handleGroup (BindingNonRecursive decl) env = insertMap (declName decl) (declName decl) env
    handleGroup (BindingNonFunction decls) env = handleMulti decls env
    handleMulti (decl : decls) env = insertMap (declName decl) (declName decl) $ foldr (\d e -> insertMap (declName d) (declName decl) e) env decls
      
bindingGroups :: (a -> [Id]) -> [Decl a] -> [BindingGroup a]
bindingGroups dependencies decls = (BindingNonFunction others) : (map toBindingGroup $ Graph.stronglyConnComp functions)
  where
    -- Split into functions and non-functions
    toNode decl@(DeclValue name _ _ _ a _) = Left (decl, name, dependencies a)
    toNode decl                            = Right decl
    (functions, others) = partitionEithers (map toNode decls)
    toBindingGroup (Graph.AcyclicSCC d) = BindingNonRecursive d
    toBindingGroup (Graph.CyclicSCC ds) = BindingRecursive ds

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
mapBindingGroup f (BindingRecursive bs)   = BindingRecursive $ map f bs
mapBindingGroup f (BindingNonRecursive b) = BindingNonRecursive $ f b
mapBindingGroup f (BindingNonFunction bs) = BindingNonFunction $ map f bs
