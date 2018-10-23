-- A thunk represents a (partially) applied function. Its memory layout is as follows. The structure starts with
-- bits for the garbage collector, the same as for data types. This requires 48 bits. The remaining 16 bits of
-- of this i64 field are used to store the number of arguments of the thunk. This means that we can support
-- thunks with at most 65535 arguments.
--
-- The next field contains a pointer to either the function or a different thunk.
-- When evaluating the thunk, two things can happen:
--   1. The function has enough arguments and can be invoked.
--   2. The function does not have enough arguments.
--
-- In the first case, the function will be invoked. We put all bits in this field to 1, to denote that this
-- thunk is being evaluated. This way we can catch a loop, if the invoked function needs the value of this
-- thunk. The thunk is called a "black hole" in this state. Once the evaluation succeeds, we set all bits
-- to 0 and store the result in the next field.
--
-- In the second case, we use the first 16 bits of the flag section (described below) to denote that this thunk
-- is in WHNF. We store the number of arguments that are still missing for this function in those bits.
--
-- The next field or fields contain information on whether arguments are in WHNF, also similar to data types.
-- The first bit is reserved to denote whether this thunk is in WHNF. A thunk can namely be in WHNF, when it
-- refers to a *partially* applied function.
--
-- For a 64-bit system, this will look approximately as follows:
-- +--------------------+------------------------|------------------------------------------|--------------|
-- | GC       Arg count | State / function /     | Remaining count  WHNF flags              | Fields       |
-- | 48 bits  16 bits   | thunk pointer (64bits) | 16 bits          ?? bits (possibly > 48) | 64 * #fields |
-- +--------------------+------------------------|------------------------------------------|--------------|
--
-- 'remaining count' is zero if the target is a thunk. We put a one in the least significant bit of the target
-- to denote that the target is a function, or a zero to denote that the target points at a thunk.

module Helium.CodeGeneration.LLVM.CompileBind (compileBinds) where

import Data.Bits(shiftL, (.|.), (.&.))
import Data.Word(Word32)

import Lvm.Common.Id(Id, NameSupply, mapWithSupply, splitNameSupply)
import Lvm.Common.IdMap(findMap)
import Helium.CodeGeneration.LLVM.Env (Env(..))
import Helium.CodeGeneration.LLVM.CompileType
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.Struct
import Helium.CodeGeneration.LLVM.CompileStruct
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Utils
import qualified Helium.CodeGeneration.LLVM.Builtins as Builtins
import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import LLVM.AST as AST
import LLVM.AST.CallingConvention
import LLVM.AST.Type as Type
import LLVM.AST.AddrSpace
import LLVM.AST.Operand
import qualified LLVM.AST.Constant as Constant

compileBinds :: Env -> NameSupply -> [Iridium.Bind] -> [Named Instruction]
compileBinds env supply binds = concat inits ++ concat assigns
  where
    (inits, assigns) = unzip $ mapWithSupply (compileBind env) supply binds

compileBind :: Env -> NameSupply -> Iridium.Bind -> ([Named Instruction], [Named Instruction])
compileBind env supply b@(Iridium.Bind varId target args)
  = compileBind' env supply b $ toStruct env target $ length args

compileBind' :: Env -> NameSupply -> Iridium.Bind -> Either Int Struct -> ([Named Instruction], [Named Instruction])
compileBind' env supply (Iridium.Bind varId target _) (Left tag) = 
  ( [toName varId := AST.IntToPtr (ConstantOperand $ Constant.Int (fromIntegral $ targetWordSize $ envTarget env) value) (expectedType target) []]
  , [])
  where
    -- Put a '1' in the least significant bit to distinguish it from a pointer.
    value :: Integer
    value = fromIntegral tag * 2 + 1
compileBind' env supply (Iridium.Bind varId target args) (Right struct) =
  ( concat splitInstructions
    ++ allocate env nameVoid nameStruct t struct
    ++ [toName varId := BitCast (LocalReference voidPointer nameVoid) (expectedType target) []]
  , initialize supplyInit env (LocalReference (pointer t) nameStruct) struct argOperands
  )
  where
    t = structType env struct
    (splitInstructions, argOperands) = unzip $ mapWithSupply (splitValueFlag env) supplyArgs $ bindArguments target args
    (supplyArgs, supply1) = splitNameSupply supply
    (supplyInit, supply2) = splitNameSupply supply1
    (nameVoid, supply3) = freshName supply2
    (nameStruct, _) = freshName supply3

toStruct :: Env -> Iridium.BindTarget -> Int -> Either Int Struct
toStruct env (Iridium.BindTargetConstructor (Iridium.DataTypeConstructor _ conId _)) arity = case findMap conId (envConstructors env) of
  LayoutInline value -> Left value
  LayoutPointer struct -> Right struct
toStruct env (Iridium.BindTargetFunction var) arity = Right $ Struct Nothing 32 tag fields
  where
    tag = arity .|. (remaining `shiftL` 16)
    remaining = case var of
      Iridium.VarLocal _ -> (1 `shiftL` 16) - 1 -- All 16 bits to 1
      Iridium.VarGlobal (Iridium.Global _ (Iridium.FunctionType args _)) -> length args - arity
    fields = map (\i -> StructField Iridium.TypeAny (Just i)) [0..arity] 

-- A thunk has an additional argument, namely the function. We add that argument here
bindArguments :: Iridium.BindTarget -> [Iridium.Variable] -> [Iridium.Variable]
bindArguments (Iridium.BindTargetFunction var) = (var :)
bindArguments _ = id

expectedType :: Iridium.BindTarget -> Type
expectedType (Iridium.BindTargetConstructor (Iridium.DataTypeConstructor dataId _ _)) = NamedTypeReference $ toNamePrefixed "$data_" dataId
expectedType _ = voidPointer
