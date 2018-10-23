{-| Module      :  CompileModule
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.LLVM.CompileModule (compileModule) where

import Helium.CodeGeneration.LLVM.CompileMethod(compileMethod)
import Helium.CodeGeneration.LLVM.CompileConstructor(dataTypeType, constructorType)
import Helium.CodeGeneration.LLVM.Env
import Helium.CodeGeneration.LLVM.Utils

import Data.String(fromString)

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium

import Lvm.Common.Id(Id, NameSupply, freshId, splitNameSupply, mapWithSupply, stringFromId)
import Lvm.Common.IdMap

import LLVM.AST
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage

compileModule :: Env -> NameSupply -> Iridium.Module -> Module
compileModule env supply (Iridium.Module name datas methods) = Module
  (fromString $ stringFromId name)
  (fromString "<TODO: Filename.hs>")
  Nothing
  Nothing
  (dataTypes ++ constructors ++ functions)
  where
    dataTypes = map (\d@(Iridium.DataType dataId cons) -> TypeDefinition (toNamePrefixed "$data_" dataId) $ Just $ dataTypeType env d $ map (\con -> let name = Iridium.constructorName con in (name, findMap name $ envConstructors env)) cons) datas
    constructors = map (\(name, con) -> TypeDefinition (toName name) $ Just $ constructorType env con) $ listFromMap $ envConstructors env
    functions = concat $ mapWithSupply (compileMethod env) supply methods
