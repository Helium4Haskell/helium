{-| Module      :  CompileMethod
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.LLVM.CompileMethod (compileMethod) where

import Data.String(fromString)

import Helium.CodeGeneration.LLVM.Env
import Helium.CodeGeneration.LLVM.Utils
import Helium.CodeGeneration.LLVM.CompileType(compileType)
import Helium.CodeGeneration.LLVM.CompileBlock(compileBlock)

import Lvm.Common.Id(Id, NameSupply, freshId, splitNameSupply, mapWithSupply)

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import LLVM.AST
import qualified LLVM.AST.Global as Global
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage

compileMethod :: Env -> NameSupply -> Iridium.Method -> [Definition]
compileMethod env supply (Iridium.Method name retType entry@(Iridium.Block _ args _) blocks) = return $ GlobalDefinition fn
  where
    fn :: Global
    -- TODO: set Linkage to Private if possible
    -- TODO: set Visibility to Hidden or Protected, if that does not give issues with function pointers
    -- TODO: check whether setting [ParameterAttribute] on arguments and return type can improve performance
    fn = Function
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
    parameters :: [Parameter]
    parameters = map (\(Iridium.Argument name t) -> Parameter (compileType env t) (toName name) []) args
    basicBlocks :: [BasicBlock]
    basicBlocks = concat $ mapWithSupply (compileBlock env) supply (entry : blocks)
