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

module Helium.CodeGeneration.Iridium.Type where

import Lvm.Common.Id(Id, stringFromId)
import Data.List(intercalate)

data BitFlags = BitFlags [Int]

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

data FunctionType = FunctionType { functionArguments :: ![PrimitiveType], functionReturnType :: !PrimitiveType }
  deriving (Eq, Ord)
