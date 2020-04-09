--    Module      :  Type
--    License     :  GPL
--
--    Maintainer  :  helium@cs.uu.nl
--    Stability   :  experimental
--    Portability :  portable

-- Iridium is the intermediate representation (IR) that we use between Core and LLVM. It is an imperative
-- strict language. It features pattern matching.
--
-- A method consists of blocks. The first block of a method is the entry block. Each block takes arguments,
-- the entry block describes the arguments of the method.

module Helium.CodeGeneration.Iridium.Type
  (
    FloatPrecision (..),
    typeRealWorld,
    typeUnsafePtr,
    typeTrampoline,
    typeInt,
    typeLitInt,
    typeInt16,
    typeChar,
    typeFloat,
    typeString,
    functionTypeArity,
  )
where

import Data.Either (isRight)
import Data.List (intercalate)
import Helium.CodeGeneration.Core.TypeEnvironment as Core
import Lvm.Common.Id (Id, idFromString, stringFromId)
import Lvm.Core.Type

createDataType :: String -> Type
createDataType s = TCon $ TConDataType $ idFromString s

createStrictDataType :: String -> Type
createStrictDataType = typeToStrict . createDataType

typeRealWorld, typeUnsafePtr, typeTrampoline, typeInt, typeInt16, typeChar, typeChar', typeFloat, typeString :: Type
typeRealWorld = createStrictDataType "$RealWorld"
typeUnsafePtr = createStrictDataType "$UnsafePtr"
typeTrampoline = createStrictDataType "$Trampoline"
typeInt = createStrictDataType "Int"
typeInt16 = createStrictDataType "Int16"
typeChar = typeToStrict $ typeChar'
typeChar' = createDataType "Char"
typeFloat = createStrictDataType "Float"
typeString = typeToStrict $ TAp (createDataType "[]") $ typeChar'

typeLitInt :: String -> Type
typeLitInt = createStrictDataType

data FloatPrecision = Float32 | Float64 deriving (Eq, Ord)

applyWithArity :: Int -> Type -> Type
applyWithArity 0 tp = tp
applyWithArity n (TAp (TAp (TCon TConFun) _) tp) = applyWithArity (n - 1) tp
applyWithArity _ tp = error ("Expected function type, got `" ++ showType tp ++ "' instead")

functionTypeArity :: FunctionType -> Int
functionTypeArity (FunctionType args _) = length $ filter isRight args
