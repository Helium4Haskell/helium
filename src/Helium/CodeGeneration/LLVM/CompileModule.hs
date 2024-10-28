{-| Module      :  CompileModule
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.LLVM.CompileModule (compileModule) where

import Helium.CodeGeneration.LLVM.CompileMethod(compileMethod, compileAbstractMethod)
import Helium.CodeGeneration.LLVM.CompileConstructor(dataTypeType, constructorType)
import Helium.CodeGeneration.LLVM.CompileType
import Helium.CodeGeneration.LLVM.Env
import Helium.CodeGeneration.LLVM.Builtins(builtinDefinitions)
import Helium.CodeGeneration.LLVM.Utils

import Data.String(fromString)

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium

import Helium.Lvm.Common.Id(Id, NameSupply, freshId, splitNameSupply, mapWithSupply, stringFromId)
import Helium.Lvm.Common.IdMap

import LLVM.AST
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage

compileModule :: Env -> NameSupply -> Iridium.Module -> Module
compileModule env supply iridium@(Iridium.Module name _ _ datas _ abstracts methods) = Module
  (fromString $ stringFromId name)
  (fromString "<TODO: Filename.hs>")
  Nothing
  Nothing
  (typeDeclarations ++ dataTypes ++ constructors ++ builtinDefinitions iridium ++ abstractFunctions ++ functions)
  where
    dataTypes = map (\d@(Iridium.Declaration dataId _ _ _ _) -> TypeDefinition (toNamePrefixed "$data_" dataId) $ Just $ dataTypeType env d $ map (\con@(Iridium.DataTypeConstructor name _) -> (name, findMap name $ envConstructors env)) $ Iridium.getConstructors d) datas
    constructors = map (\(name, con) -> TypeDefinition (toName name) $ Just $ constructorType env con) $ listFromMap $ envConstructors env
    abstractFunctions = concat $ mapWithSupply (compileAbstractMethod env) supply1 abstracts'
    functions = concat $ mapWithSupply (compileMethod env) supply2 methods
    (supply1, supply2) = splitNameSupply supply
    abstracts' = map snd $ listFromMap $ mapFromList $ map (\a -> (Iridium.declarationName a, a)) abstracts

typeDeclarations :: [Definition]
typeDeclarations = 
  [ TypeDefinition (mkName "thunk") $ Just tp ]
  where
    tp = StructureType False [IntegerType 64, thunkType, trampolineType, IntegerType 16, IntegerType 16, ArrayType 0 taggedThunkPointer]
