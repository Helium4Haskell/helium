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
compileInstruction env supply (Iridium.Let name expr next) = compileExpression env supply1 expr (toName name) +> compileInstruction env supply2 next
  where
    (supply1, supply2) = splitNameSupply supply
compileInstruction env supply (Iridium.LetThunk binds next) =
  compileThunks env supply1 binds
  +> compileInstruction env supply2 next -- TODO: Compile thunks
  where
    (supply1, supply2) = splitNameSupply supply
compileInstruction env supply (Iridium.Jump to) = Partial [] (Do $ Br (toName to) []) []
compileInstruction env supply (Iridium.Return var) = Partial [] (Do $ Ret (Just $ toOperand env var) []) []
-- A Match has undefined behaviour if it does not match, so we do not need to check whether it actually matches.
compileInstruction env supply (Iridium.Match var _ [] next) = compileInstruction env supply next
compileInstruction env supply (Iridium.Match var (Iridium.DataTypeConstructor _ conId _) args next)
  = [ addressName := AST.BitCast (toOperand env var) (pointer t) []
    ]
    +> compileExtractFields env supply'' address (fromIntegral $ headerSize * targetPointerSize (envTarget env)) fieldLayouts args
    +> compileInstruction env supply''' next
  where
    t = NamedTypeReference $ toName conId
    (addressName, supply') = freshName supply
    address = LocalReference (pointer t) addressName
    (supply'', supply''') = splitNameSupply supply'
    LayoutPointer _ _ headerSize fieldLayouts = findMap conId (envConstructors env)
compileInstruction env supply (Iridium.If var (Iridium.PatternCon con@(Iridium.DataTypeConstructor _ conId _)) whenTrue whenFalse)
  = compileIfMatchConstructor env supply var con conLayout whenTrue whenFalse
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
      , function = Right $ toOperand env to
      , arguments = map (\arg -> (toOperand env arg, [])) args
      , functionAttributes = []
      , metadata = []
      }
  ]
compileExpression env supply (Iridium.Eval var) name = compileEval env supply (toOperand env var) (Iridium.variableType var) name
compileExpression env supply (Iridium.Alloc con args) name = compileAllocation env supply con args name
compileExpression env supply (Iridium.Var var) name = cast env (toOperand env var) name t t
  where t = Iridium.variableType var
compileExpression env supply (Iridium.Cast var toType) name = cast env (toOperand env var) name t toType
  where t = Iridium.variableType var

compileEval :: Env -> NameSupply -> Operand -> Iridium.PrimitiveType -> Name -> [Named Instruction]
compileEval env supply operand Iridium.TypeAny name =
  [ toName namePtr := ExtractValue operand [0] []
  , toName nameIsWHNF := ExtractValue operand [1] []
  , name := callEval (LocalReference voidPointer $ toName namePtr) (LocalReference bool $ toName nameIsWHNF)
  ]
  where
    (namePtr, supply') = freshId supply
    (nameIsWHNF, _) = freshId supply'
compileEval env supply operand Iridium.TypeAnyThunk name =
  [ name := callEval operand (ConstantOperand $ Int 1 0)
  ]
compileEval env supply operand primType name =
  cast env operand name primType Iridium.TypeAnyWHNF

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

compileIfMatchConstructor :: Env -> NameSupply -> Iridium.Variable -> Iridium.DataTypeConstructor -> ConstructorLayout -> Id -> Id -> Partial
compileIfMatchConstructor env supply var _ (LayoutInline tag) whenTrue whenFalse
  = Partial instructions terminator []
  where
    instructions :: [Named Instruction]
    instructions =
      [ nameInt := PtrToInt (toOperand env var) (envValueType env) []
      , nameCond := ICmp IntegerPredicate.EQ (LocalReference (envValueType env) nameInt) expected []
      ]
    expected = ConstantOperand $ Int (fromIntegral $ targetPointerSize $ envTarget env) (fromIntegral tag * 2 + 1)
    terminator :: Named Terminator
    terminator = Do $ CondBr (LocalReference bool nameCond) (toName whenTrue) (toName whenFalse) []
    (nameInt, supply') = freshName supply
    (nameCond, supply'') = freshName supply'
compileIfMatchConstructor env supply var (Iridium.DataTypeConstructor _ conId _) (LayoutPointer tag (firstHeaderBit, afterHeaderBit) headerSize fieldLayouts) whenTrue whenFalse
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
      [ nameCond := PtrToInt (toOperand env var) bool [] ]
    terminatorMain :: Named Terminator
    -- Check if the least significant bit of the pointer was a 1. If so, this is an inlined constructor
    -- so they do not match.
    -- If it is a 0, we must read the pointer and check its tag.
    terminatorMain = Do $ CondBr (LocalReference bool nameCond) (toName whenFalse) nameBlockCheck []

    instructionsCheck :: [Named Instruction]
    instructionsCheck =
      [ addressName := AST.BitCast (toOperand env var) (pointer t) [] 
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
