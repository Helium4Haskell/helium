{-| Module      :  Type
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

-- Iridium is the intermediate representation (IR) that we use between Core and LLVM. It is an imperative
-- strict language. It features pattern matching.
--
-- A method consists of blocks. The first block of a method is the entry block. Each block takes arguments,
-- the entry block describes the arguments of the method.

module Helium.CodeGeneration.Iridium.Type
  ( typeFromFunctionType, FunctionType(..), extractFunctionTypeNoSynonyms, extractFunctionTypeWithArity
  , FloatPrecision(..), EvaluationState(..), evaluationState
  , Core.TypeEnvironment(..), Core.typeNormalizeHead, Core.typeEqual, typeIsStrict, typeToStrict
  , PrimitiveType(..), typeNotStrict
  , typeRealWorld, typeUnsafePtr, typeTrampoline, typeInt, typeChar, typeFloat, functionTypeArity
  ) where

import Lvm.Common.Id(Id, stringFromId, idFromString)
import Data.List(intercalate)
import Data.Either(isRight)
import Lvm.Core.Type
import Helium.CodeGeneration.Core.TypeEnvironment as Core

typeRealWorld, typeUnsafePtr, typeTrampoline, typeInt, typeChar, typeFloat :: Type
typeRealWorld = TStrict $ TCon $ TConDataType $ idFromString "$RealWorld"
typeUnsafePtr = TStrict $ TCon $ TConDataType $ idFromString "$UnsafePtr"
typeTrampoline = TStrict $ TCon $ TConDataType $ idFromString "$Trampoline"
typeInt = TStrict $ TCon $ TConDataType $ idFromString "Int"
typeChar = TStrict $ TCon $ TConDataType $ idFromString "Char"
typeFloat = TStrict $ TCon $ TConDataType $ idFromString "Float"

data PrimitiveType
  = TypeAny -- ^ Any value, possibly a non-evaluated thunk. Supertype of TypeAnyThunk and TypeAnyWHNF.
  | TypeAnyThunk -- ^ A thunk, not in WHNF
  | TypeAnyWHNF

  -- Subtypes of TypeAnyWHNF
  | TypeInt
  | TypeFloat FloatPrecision
  | TypeRealWorld
  | TypeDataType !Id
  | TypeTuple !Int
  | TypeFunction -- ^ Pointer to a function or a thunk in WHNF (partially applied function)
  | TypeGlobalFunction FunctionType -- ^ A global function

  -- Types used for the runtime
  | TypeUnsafePtr
  deriving (Eq, Ord)

data FloatPrecision = Float32 | Float64 deriving (Eq, Ord)

data EvaluationState = Unevaluated | EvaluationUnknown | Evaluated deriving (Show, Eq, Ord)

evaluationState :: PrimitiveType -> EvaluationState
evaluationState TypeAny = EvaluationUnknown
evaluationState TypeAnyThunk = Unevaluated
evaluationState _ = Evaluated

applyWithArity :: Int -> Type -> Type
applyWithArity 0 tp = tp
applyWithArity n (TAp (TAp (TCon TConFun) _) tp) = applyWithArity (n - 1) tp
applyWithArity _ tp = error ("Expected function type, got `" ++ showType [] tp ++ "' instead")

functionTypeArity :: FunctionType -> Int
functionTypeArity (FunctionType args _) = length $ filter isRight args
