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

module Helium.CodeGeneration.LLVM.CompileThunk (compileThunks) where

import qualified Data.Bits as Bits
import Data.Word(Word32)

import Lvm.Common.Id(Id, NameSupply, mapWithSupply, splitNameSupply)
import Lvm.Common.IdMap(findMap)
import Helium.CodeGeneration.LLVM.Env (Env(..))
import Helium.CodeGeneration.LLVM.CompileType
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Utils
import Helium.CodeGeneration.LLVM.ConstructorLayout (gcBits)
import qualified Helium.CodeGeneration.LLVM.Builtins as Builtins
import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import LLVM.AST as AST
import LLVM.AST.CallingConvention
import LLVM.AST.Type as Type
import LLVM.AST.AddrSpace
import LLVM.AST.Operand
import LLVM.AST.Constant as Constant

argumentCountBits :: Int
argumentCountBits = 16 -- We assume that there are no more than 2 ^ argumentCountBits arguments in a thunk

compileThunks :: Env -> NameSupply -> [Iridium.BindThunk] -> [Named Instruction]
compileThunks env supply thunks = concat inits ++ concat assigns
  where
    (inits, assigns) = unzip $ mapWithSupply (compileThunk env) supply thunks

compileThunk :: Env -> NameSupply -> Iridium.BindThunk -> ([Named Instruction], [Named Instruction])
compileThunk env supply (Iridium.BindThunk varId fnId args) =
  ( [ toName varId := Call Nothing Fast [] (Right Builtins.alloc) [(ConstantOperand $ Int 32 8, []), (ConstantOperand $ Int 32 $ fromIntegral byteCount, [])] [] [] ]
  , [ ]
  )
  where
    argCount = length args
    pointerSize = targetPointerSize $ envTarget env
    flagBits = argCount + 16
    flagFieldCount = (flagBits + pointerSize - 1) `div` pointerSize -- ceiling of flagBits / pointerSize
    byteCount = 8 -- GC + argument count
      + 8 -- function / thunk pointer or state
      + flagFieldCount * pointerSize `div` 8 -- flags
      + argCount * pointerSize `div` 8 -- fields
