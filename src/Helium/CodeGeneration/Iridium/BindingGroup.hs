module Helium.CodeGeneration.Iridium.BindingGroup where

import Lvm.Common.Id
import Lvm.Common.IdMap
import qualified Data.Graph as Graph
import Helium.CodeGeneration.Iridium.Data

data BindingGroup a
  = BindingRecursive [Declaration a]
  | BindingNonRecursive (Declaration a)

bindingGroupToList :: BindingGroup a -> [Declaration a]
bindingGroupToList (BindingRecursive as) = as
bindingGroupToList (BindingNonRecursive a) = [a]

bindingGroupsToMap :: [BindingGroup a] -> IdMap Id
bindingGroupsToMap = foldr handleGroup emptyMap
  where
    handleGroup :: BindingGroup a -> IdMap Id -> IdMap Id
    handleGroup (BindingNonRecursive (Declaration name _ _ _ _)) env = insertMap name name env
    handleGroup (BindingRecursive (Declaration name _ _ _ _ : decls)) env =
      insertMap name name $ foldr (\d e -> insertMap (declarationName d) name e) env decls

bindingGroups :: (a -> [Id]) -> [Declaration a] -> [BindingGroup a]
bindingGroups dependencies = map toBindingGroup . Graph.stronglyConnComp . map toNode
  where
    toNode decl@(Declaration name _ _ _ a) = (decl, name, dependencies a)
    toBindingGroup (Graph.AcyclicSCC decl) = BindingNonRecursive decl
    toBindingGroup (Graph.CyclicSCC decls) = BindingRecursive decls

methodBindingGroups :: [Declaration Method] -> [BindingGroup Method]
methodBindingGroups = bindingGroups methodDependencies
  where
    methodDependencies :: Method -> [Id]
    methodDependencies (Method _ _ _ _ block blocks) = blockDependencies block ++ (blocks >>= blockDependencies)

    blockDependencies :: Block -> [Id]
    blockDependencies (Block _ instruction) = instructionDependencies instruction

    variableDependencies :: Variable -> [Id]
    variableDependencies (VarGlobal (GlobalVariable name _)) = [name]
    variableDependencies _ = []

    instructionDependencies :: Instruction -> [Id]
    instructionDependencies (Let _ expr next) = expressionDependencies expr ++ instructionDependencies next
    instructionDependencies (LetAlloc binds next) = (binds >>= bindDependencies) ++ instructionDependencies next
    instructionDependencies (Jump _) = []
    instructionDependencies (Match var _ _ _ next) = variableDependencies var ++ instructionDependencies next
    instructionDependencies (Case var _) = variableDependencies var
    instructionDependencies (Return var) = variableDependencies var
    instructionDependencies (Unreachable (Just var)) = variableDependencies var
    instructionDependencies (Unreachable Nothing) = []

    expressionDependencies (Literal _) = []
    expressionDependencies (Call (GlobalFunction fn _ _) args) = fn : [name | Right (VarGlobal (GlobalVariable name _)) <- args]
    expressionDependencies (Instantiate var _) = variableDependencies var
    expressionDependencies (Eval var) = variableDependencies var
    expressionDependencies (Var var) = variableDependencies var
    expressionDependencies (Cast var _) = variableDependencies var
    expressionDependencies (CastThunk var) = variableDependencies var
    expressionDependencies (Phi branches) = branches >>= (variableDependencies . phiVariable)
    expressionDependencies (PrimitiveExpr _ args) = [name | Right (VarGlobal (GlobalVariable name _)) <- args]
    expressionDependencies (Undefined _) = []
    expressionDependencies (Seq a b) = variableDependencies a ++ variableDependencies b

    bindDependencies (Bind _ target args) = bindTargetDependencies target ++ [name | Right (VarGlobal (GlobalVariable name _)) <- args]

    bindTargetDependencies (BindTargetFunction (GlobalFunction name _ _)) = [name]
    bindTargetDependencies (BindTargetThunk var) = variableDependencies var
    bindTargetDependencies _ = []
