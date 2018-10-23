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

data DataType = DataType Id [DataTypeConstructor]
  deriving (Eq, Ord)
data DataTypeConstructor = DataTypeConstructor { constructorDataType :: Id, constructorName :: Id, constructorFields :: [PrimitiveType] }
  deriving (Eq, Ord)

data BitFlags = BitFlags [Int]

data PrimitiveType
  = TypeAny -- ^ Any value, possibly a non-evaluated thunk. Supertype of TypeAnyThunk and TypeAnyWHNF.
  | TypeAnyThunk -- ^ A thunk, not in WHNF
  | TypeAnyWHNF

  -- Subtypes of TypeAnyWHNF
  | TypeInt
  | TypeDouble
  | TypeDataType Id
  | TypeFunction -- ^ Pointer to a function or a thunk in WHNF (partially applied function)
  deriving (Eq, Ord)

data EvaluationState = Unevaluated | EvaluationUnknown | Evaluated deriving (Show, Eq, Ord)

evaluationState :: PrimitiveType -> EvaluationState
evaluationState TypeAny = EvaluationUnknown
evaluationState TypeAnyThunk = Unevaluated
evaluationState _ = Evaluated

data FunctionType = FunctionType { functionArguments :: [PrimitiveType], functionReturnType :: PrimitiveType }
  deriving (Eq, Ord)

instance Show DataTypeConstructor where
  show (DataTypeConstructor dataType name args) = "@" ++ stringFromId name ++ ": " ++ showArguments args ++ " -> @" ++ stringFromId dataType

instance Show DataType where
  show (DataType name cons) = "data @" ++ stringFromId name ++ (cons >>= (("\n  " ++) . show)) ++ "\n"

instance Show PrimitiveType where
  show (TypeAny) = "any"
  show (TypeAnyThunk) = "any_thunk"
  show (TypeAnyWHNF) = "any_whnf"

  show (TypeInt) = "int"
  show (TypeDataType name) = "data<@" ++ stringFromId name ++ ">"
  show (TypeFunction) = "function"

showArguments' :: (a -> String) -> [a] -> String
showArguments' showFn = ("("++) . (++")") . intercalate ", " . map showFn

showArguments :: Show a => [a] -> String
showArguments = showArguments' show

instance Show FunctionType where
  show (FunctionType args ret) = showArguments args ++ " -> " ++ show ret
