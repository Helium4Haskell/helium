{-| Module      :  CompileMethod
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.LLVM.CompileBlock (compileBlock) where

import Data.String(fromString)
import Data.Word(Word32)

import Helium.CodeGeneration.LLVM.Env
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Utils
import Helium.CodeGeneration.LLVM.CompileType
import Helium.CodeGeneration.LLVM.CompileThunk
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.CompileConstructor(compileAllocation, compileExtractFields)
import qualified Helium.CodeGeneration.LLVM.Builtins as Builtins

import Lvm.Common.Id(Id, NameSupply, freshId, splitNameSupply, mapWithSupply)
import Lvm.Common.IdMap(findMap)

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.CodeGeneration.Iridium.TypeEnvironment as Iridium
import LLVM.AST as AST
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage
import LLVM.AST.Constant (Constant(Int))
import qualified LLVM.AST.IntegerPredicate as IntegerPredicate

data Partial = Partial [Named Instruction] (Named Terminator) [BasicBlock]

infixr 3 +>
(+>) :: [Named Instruction] -> Partial -> Partial
instrs1 +> (Partial instrs2 terminator blocks) = Partial (instrs1 ++ instrs2) terminator blocks

compileBlock :: Env -> NameSupply -> Iridium.Block -> [BasicBlock]
compileBlock env supply (Iridium.Block name instruction) = BasicBlock (toName name) instrs term : blocks
  where
    Partial instrs term blocks = compileInstruction env supply instruction

{-
  | LetThunk [BindThunk] Instruction
-}

compileInstruction :: Env -> NameSupply -> Iridium.Instruction -> Partial
compileInstruction env supply (Iridium.Let name expr next) = compileExpression env supply1 expr (toName name) +> compileInstruction env' supply2 next
  where
    (supply1, supply2) = splitNameSupply supply
    env' = expand env $ Iridium.expandEnvWithLet name expr
compileInstruction env supply (Iridium.LetThunk binds next) =
  compileThunks env' supply1 binds
  +> compileInstruction env' supply2 next -- TODO: Compile thunks
  where
    (supply1, supply2) = splitNameSupply supply
    env' = expand env $ Iridium.expandEnvWithLetThunk binds
compileInstruction env supply (Iridium.Jump to) = Partial [] (Do $ Br (toName to) []) []
compileInstruction env supply (Iridium.Return var) = Partial [] (Do $ Ret (Just $ toOperand env var) []) []
-- A Match has undefined behaviour if it does not match, so we do not need to check whether it actually matches.
compileInstruction env supply (Iridium.Match var _ [] next) = compileInstruction env supply next
compileInstruction env supply (Iridium.Match (Iridium.Variable var _) conId args next)
  = [ addressName := AST.BitCast (LocalReference voidPointer $ toName var) (pointer t) []
    ]
    +> compileExtractFields env supply'' address (fromIntegral $ headerSize * targetPointerSize (envTarget env)) fieldLayouts args
    +> compileInstruction env' supply''' next
  where
    t = NamedTypeReference $ toName conId
    (addressName, supply') = freshName supply
    address = LocalReference (pointer t) addressName
    (supply'', supply''') = splitNameSupply supply'
    LayoutPointer _ _ headerSize fieldLayouts = findMap conId (envConstructors env)
    env' = expand env $ Iridium.expandEnvWithMatch conId args
compileInstruction env supply (Iridium.If (Iridium.Variable varId _) (Iridium.PatternCon conId) whenTrue whenFalse)
  = compileIfMatchConstructor env supply varId conId conLayout whenTrue whenFalse
  where
    conLayout = findMap conId (envConstructors env)

compileExpression :: Env -> NameSupply -> Iridium.Expr -> Name -> [Named Instruction]
compileExpression env supply (Iridium.Literal (Iridium.LitInt value)) name = [name := ZExt (ConstantOperand constant) (envValueType env) []]
  where
    constant :: Constant
    constant = Int (fromIntegral $ targetPointerSize $ envTarget $ env) (fromIntegral $ value)
-- TODO: Float literals
compileExpression env supply (Iridium.Call to args) name =
  [ name := Call
      { tailCallKind = Nothing
      , callingConvention = Fast
      , returnAttributes = []
      , function = Right $ toOperand env (Iridium.Variable to Iridium.TypeFunction)
      , arguments = map (\arg -> (toOperand env arg, [])) args
      , functionAttributes = []
      , metadata = []
      }
  ]
compileExpression env supply (Iridium.Eval var@(Iridium.Variable _ Iridium.TypeAny)) name =
  [ toName namePtr := ExtractValue operand [0] []
  , toName nameIsWHNF := ExtractValue operand [1] []
  , name := callEval (LocalReference voidPointer $ toName namePtr) (LocalReference bool $ toName nameIsWHNF)
  ]
  where
    operand = toOperand env var
    (namePtr, supply') = freshId supply
    (nameIsWHNF, _) = freshId supply'
compileExpression env supply (Iridium.Eval (Iridium.Variable thunk Iridium.TypeAnyThunk)) name =
  [ name := callEval (LocalReference voidPointer $ toName thunk) (ConstantOperand $ Int 1 0)
  ]
compileExpression env supply (Iridium.Eval (Iridium.Variable thunk primType)) name =
  cast env (toName thunk) name primType Iridium.TypeAnyWHNF
compileExpression env supply (Iridium.Alloc conId args) name = compileAllocation env supply conId args name
compileExpression env supply (Iridium.Var (Iridium.Variable varId t)) name = cast env (toName varId) name t t
compileExpression env supply (Iridium.Cast (Iridium.Variable varId t) toType) name = cast env (toName varId) name t toType

callEval :: Operand -> Operand -> Instruction
callEval pointer isWHNF =
  Call
  { tailCallKind = Nothing
  , callingConvention = Fast
  , returnAttributes = []
  , function = Right $ Builtins.eval
  , arguments = [(pointer, []), (isWHNF, [])]
  , functionAttributes = []
  , metadata = []
  }

compileIfMatchConstructor :: Env -> NameSupply -> Id -> Id -> ConstructorLayout -> Id -> Id -> Partial
compileIfMatchConstructor env supply varId conId (LayoutInline tag) whenTrue whenFalse
  = Partial instructions terminator []
  where
    instructions :: [Named Instruction]
    instructions =
      [ nameInt := PtrToInt (LocalReference voidPointer (toName varId)) (envValueType env) []
      , nameCond := ICmp IntegerPredicate.EQ (LocalReference (envValueType env) nameInt) expected []
      ]
    expected = ConstantOperand $ Int (fromIntegral $ targetPointerSize $ envTarget env) (fromIntegral tag * 2 + 1)
    terminator :: Named Terminator
    terminator = Do $ CondBr (LocalReference bool nameCond) (toName whenTrue) (toName whenFalse) []
    (nameInt, supply') = freshName supply
    (nameCond, supply'') = freshName supply'
compileIfMatchConstructor env supply varId conId (LayoutPointer tag (firstHeaderBit, afterHeaderBit) headerSize fieldLayouts) whenTrue whenFalse
  = Partial instructionsMain terminatorMain blocks
  where
    (nameCond, supply1) = freshName supply
    (addressName, supply2) = freshName supply1
    (headerPtrName, supply3) = freshName supply2
    (headerName, supply4) = freshName supply3
    (shiftedLeft, supply5) = freshName supply4
    (shifted, supply6) = freshName supply5
    (tagCheck, supply7) = freshName supply6
    (nameBlockCheck, supply8) = freshName supply7

    instructionsMain :: [Named Instruction]
    instructionsMain =
      -- Convert pointer to int & truncate to a single bit
      [ nameCond := PtrToInt (LocalReference voidPointer (toName varId)) bool [] ]
    terminatorMain :: Named Terminator
    -- Check if the least significant bit of the pointer was a 1. If so, this is an inlined constructor
    -- so they do not match.
    -- If it is a 0, we must read the pointer and check its tag.
    terminatorMain = Do $ CondBr (LocalReference bool nameCond) (toName whenFalse) nameBlockCheck []

    instructionsCheck :: [Named Instruction]
    instructionsCheck =
      [ addressName := AST.BitCast (LocalReference voidPointer $ toName varId) (pointer t) [] 
      , headerPtrName := getElementPtr address [0, 0]
      , headerName := Load False (LocalReference (pointer $ headerType) headerPtrName) Nothing 0 []
      , shiftedLeft := Shl False False header (ConstantOperand $ Int headerBits $ fromIntegral headerBits - fromIntegral afterHeaderBit) []
      , shifted := LShr False (LocalReference headerType shiftedLeft) (ConstantOperand $ Int headerBits $ fromIntegral headerBits - fromIntegral afterHeaderBit + fromIntegral firstHeaderBit) []
      , tagCheck := ICmp IntegerPredicate.EQ (LocalReference headerType shifted) (ConstantOperand $ Int headerBits $ fromIntegral tag) []
      ]
    terminatorCheck :: Named Terminator
    terminatorCheck = Do $ CondBr (LocalReference bool tagCheck) (toName whenTrue) (toName whenFalse) []

    address = LocalReference (pointer t) addressName
    t = NamedTypeReference $ toName conId

    headerBits :: Word32
    headerBits = fromIntegral $ headerSize * targetPointerSize (envTarget env)
    headerType = IntegerType headerBits
    header = LocalReference headerType headerName

    blocks = [BasicBlock nameBlockCheck instructionsCheck terminatorCheck]
