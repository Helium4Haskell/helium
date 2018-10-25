{-| Module      :  CompileMethod
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.LLVM.CompileMethod (compileMethod, compileAbstractMethod) where

import Data.String(fromString)

import Helium.CodeGeneration.LLVM.Env
import Helium.CodeGeneration.LLVM.Utils
import Helium.CodeGeneration.LLVM.CompileType(compileType)
import Helium.CodeGeneration.LLVM.CompileBlock(compileBlock)

import Lvm.Common.Id(Id, NameSupply, freshId, splitNameSupply, mapWithSupply, idFromString)

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import LLVM.AST
import qualified LLVM.AST.Global as Global
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage

-- llvm-hs-pure requires to set a name on the argument of a declared (abstract) function. However, when pretty printing / exporting the
-- IR this is not used. We thus can use a non-unique name.
unusedArgumentName :: Id
unusedArgumentName = idFromString "_argument"

compileAbstractMethod :: Env -> Iridium.AbstractMethod -> Definition
compileAbstractMethod env (Iridium.AbstractMethod name (Iridium.FunctionType argTypes retType)) = toFunction env name args retType []
  where
    args = map (Iridium.Local unusedArgumentName) argTypes

compileMethod :: Env -> NameSupply -> Iridium.Method -> Definition
compileMethod env supply (Iridium.Method name args retType entry blocks) = toFunction env name args retType basicBlocks
  where
    parameters :: [Parameter]
    parameters = map (\(Iridium.Local name t) -> Parameter (compileType env t) (toName name) []) args
    basicBlocks :: [BasicBlock]
    basicBlocks = concat $ mapWithSupply (compileBlock env) supply (entry : blocks)

toFunction :: Env -> Id -> [Iridium.Local] -> Iridium.PrimitiveType -> [BasicBlock] -> Definition
toFunction env name args retType basicBlocks = GlobalDefinition $ Function
    -- TODO: set Linkage to Private if possible
    -- TODO: set Visibility to Hidden or Protected, if that does not give issues with function pointers
    -- TODO: check whether setting [ParameterAttribute] on arguments and return type can improve performance
  { Global.linkage = External
  , Global.visibility = Default
  , Global.dllStorageClass = Nothing
  , Global.callingConvention = Fast
  , Global.returnAttributes = []
  , Global.returnType = compileType env retType
  , Global.name = toName name
  , Global.parameters = (parameters, {- varargs: -} False)
  , Global.functionAttributes = []
  , Global.section = Nothing
  , Global.comdat = Nothing
  , Global.alignment = 0
  , Global.garbageCollectorName = Nothing
  , Global.prefix = Nothing
  , Global.basicBlocks = basicBlocks
  , Global.personalityFunction = Nothing
  , Global.metadata = []
  }
  where
    parameters :: [Parameter]
    parameters = map (\(Iridium.Local name t) -> Parameter (compileType env t) (toName name) []) args
