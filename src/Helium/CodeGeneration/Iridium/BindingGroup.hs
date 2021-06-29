module Helium.CodeGeneration.Iridium.BindingGroup where

import Data.List

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import qualified Data.Graph as Graph
import Data.Either (rights)

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Core.TypeEnvironment

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
    toBindingGroup (Graph.CyclicSCC decls) = BindingRecursive $ sortOn declarationName decls

----------------------------------------------------------------
-- Methods
----------------------------------------------------------------

methodBindingGroups :: [Declaration Method] -> [BindingGroup Method]
methodBindingGroups = bindingGroups methodDependencies
  where
    methodDependencies :: Method -> [Id]
    methodDependencies (Method _ _ _ _ _ _ block blocks) = blockDependencies block ++ (blocks >>= blockDependencies)

    blockDependencies :: Block -> [Id]
    blockDependencies (Block _ instruction) = instructionDependencies instruction

    variableDependencies :: Variable -> [Id]
    variableDependencies (VarGlobal (GlobalVariable name _)) = [name]
    variableDependencies _ = []

    instructionDependencies :: Instruction -> [Id]
    instructionDependencies (Let _ expr next) = expressionDependencies expr ++ instructionDependencies next
    instructionDependencies (LetAlloc binds next) = (binds >>= bindDependencies) ++ instructionDependencies next
    instructionDependencies (NewRegion _ _ next) = instructionDependencies next
    instructionDependencies (ReleaseRegion _ next) = instructionDependencies next
    instructionDependencies (Jump _) = []
    instructionDependencies (Match _ _ _ _ next) = instructionDependencies next
    instructionDependencies (Case _ _) = []
    instructionDependencies (Return _) = []
    instructionDependencies (Unreachable _) = []

    expressionDependencies (Literal _) = []
    expressionDependencies (Call (GlobalFunction fn _ _) _ args _) = [fn]
    expressionDependencies (Instantiate _ _) = []
    expressionDependencies (Eval var) = variableDependencies var
    expressionDependencies (Var var) = variableDependencies var
    expressionDependencies (Cast _ _) = []
    expressionDependencies (CastThunk _) = []
    expressionDependencies (Phi _) = []
    expressionDependencies (PrimitiveExpr _ _) = []
    expressionDependencies (Undefined _) = []
    expressionDependencies (Seq _ _) = []

    bindDependencies (Bind _ target _ _) = bindTargetDependencies target

    bindTargetDependencies (BindTargetFunction (GlobalFunction name _ _) _ _) = [name]
    bindTargetDependencies (BindTargetThunk var _) = variableDependencies var
    bindTargetDependencies _ = []

mapBindingGroup :: (Declaration a -> Declaration b) -> BindingGroup a -> BindingGroup b
mapBindingGroup f (BindingNonRecursive a) = BindingNonRecursive $ f a
mapBindingGroup f (BindingRecursive as) = BindingRecursive $ map f as

----------------------------------------------------------------
-- DataTypes
----------------------------------------------------------------

dataTypeBindingGroups :: Bool -> [Declaration DataType] -> [BindingGroup DataType]
dataTypeBindingGroups inFs = bindingGroups (dataTypeDependencies inFs)
   where 
    dataTypeDependencies :: Bool -> DataType -> [Id]
    dataTypeDependencies inFunctions (DataType decls) = concat $ constructorDependencies inFunctions <$> (declarationValue <$> decls)
    
    constructorDependencies :: Bool -> DataTypeConstructorDeclaration -> [Id]
    constructorDependencies inFunctions (DataTypeConstructorDeclaration ty _) = 
       let (FunctionType args _) = extractFunctionTypeNoSynonyms ty 
       in rights args >>= typeDependencies inFunctions
    
    typeDependencies :: Bool -> Type -> [Id]
    typeDependencies inFunctions tp = dependencies tp []
        where
          dependencies (TAp (TAp (TCon TConFun) t1) t2) accum 
              | inFunctions = dependencies t1 $ dependencies t2 accum
              | otherwise   = accum
          dependencies (TAp t1 t2) accum = dependencies t1 $ dependencies t2 accum
          dependencies (TForall _ _ t1) accum = dependencies t1 accum
          dependencies (TStrict t1) accum = dependencies t1 accum
          dependencies (TCon (TConDataType name)) accum = name : accum
          dependencies (TCon (TConTypeClassDictionary name)) accum = dictionaryDataTypeName name : accum
          dependencies _ accum = accum
