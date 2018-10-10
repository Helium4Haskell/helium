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
compileBlock env supply (Iridium.Block name args instruction) = BasicBlock (toName name) instrs term : blocks
  where
    Partial instrs term blocks = compileInstruction env' supply instruction
    env' = expand env $ Iridium.expandEnvWithArguments args

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
compileInstruction env supply (Iridium.Jump to args) = Partial [] (Do $ Br (toName to) []) []
compileInstruction env supply (Iridium.Return var) = Partial [] (Do $ Ret (Just $ toOperand env var) []) []
-- A Match has undefined behaviour if it does not match, so we do not need to check whether it matches.
compileInstruction env supply (Iridium.Match var (Iridium.PatternLit _) next) = compileInstruction env supply next
compileInstruction env supply (Iridium.Match var (Iridium.PatternCon _ []) next) = compileInstruction env supply next
compileInstruction env supply (Iridium.Match var pat@(Iridium.PatternCon conId args) next)
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
    env' = expand env $ Iridium.expandEnvWithMatch pat
compileInstruction env supply (Iridium.IfMatch varId (Iridium.PatternCon conId args) to toArgs next)
  = compileIfMatchConstructor env supply1 varId conId conLayout [] to $ compileInstruction env supply2 next
  where
    (supply1, supply2) = splitNameSupply supply
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
compileExpression env supply (Iridium.Eval thunk) name = case Iridium.typeOf (envTypeEnv env) thunk of
  Iridium.TypeAny ->
    [ toName namePtr := ExtractValue operand [0] []
    , toName nameIsWHNF := ExtractValue operand [1] []
    , name := callEval (LocalReference voidPointer $ toName namePtr) (LocalReference bool $ toName nameIsWHNF)
    ]
  Iridium.TypeAnyThunk ->
    [ name := callEval (LocalReference voidPointer $ toName thunk) (ConstantOperand $ Int 1 0)
    ]
  primType ->
    -- Already in WHNF, insert a cast to TypeAnyWHNF (voidPointer in LLVM)
    cast env (toName thunk) name primType Iridium.TypeAnyWHNF
  where
    operand = toOperand env thunk
    (namePtr, supply') = freshId supply
    (nameIsWHNF, _) = freshId supply'
compileExpression env supply (Iridium.Alloc conId args) name = compileAllocation env supply conId args name
compileExpression env supply (Iridium.Var varId) name = cast env (toName varId) name t t
  where t = Iridium.typeOf (envTypeEnv env) varId
compileExpression env supply (Iridium.Cast varId toType) name = cast env (toName varId) name t toType
  where t = Iridium.typeOf (envTypeEnv env) varId

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

compileIfMatchConstructor :: Env -> NameSupply -> Id -> Id -> ConstructorLayout -> [Id] -> Id -> Partial -> Partial
compileIfMatchConstructor env supply varId conId (LayoutInline tag) [] branchId (Partial nextInstructions nextTerminator blocks)
  = Partial instructions terminator blocks'
  where
    instructions :: [Named Instruction]
    instructions =
      [ nameInt := PtrToInt (LocalReference voidPointer (toName varId)) (envValueType env) []
      , nameCond := ICmp IntegerPredicate.EQ (LocalReference (envValueType env) nameInt) expected []
      ]
    expected = ConstantOperand $ Int (fromIntegral $ targetPointerSize $ envTarget env) (fromIntegral tag * 2 + 1)
    terminator :: Named Terminator
    terminator = Do $ CondBr (LocalReference bool nameCond) (toName branchId) nameBlockFalse []
    (nameInt, supply') = freshName supply
    (nameCond, supply'') = freshName supply'
    (nameBlockFalse, supply''') = freshName supply''
    blocks' = BasicBlock nameBlockFalse nextInstructions nextTerminator : blocks
compileIfMatchConstructor env supply varId conId (LayoutPointer tag (firstHeaderBit, afterHeaderBit) headerSize fieldLayouts) args branchId (Partial nextInstructions nextTerminator blocks)
  = Partial instructionsMain terminatorMain blocks'
  where
    (nameCond, supply1) = freshName supply
    (addressName, supply2) = freshName supply1
    (headerPtrName, supply3) = freshName supply2
    (headerName, supply4) = freshName supply3
    (shiftedLeft, supply5) = freshName supply4
    (shifted, supply6) = freshName supply5
    (tagCheck, supply7) = freshName supply6
    (nameBlockCheck, supply8) = freshName supply7
    (nameBlockTrue, supply9) = freshName supply8
    (nameBlockFalse, supply10) = freshName supply9

    instructionsMain :: [Named Instruction]
    instructionsMain =
      -- Convert pointer to int & truncate to a single bit
      [ nameCond := PtrToInt (LocalReference voidPointer (toName varId)) bool [] ]
    terminatorMain :: Named Terminator
    -- Check if the least significant bit of the pointer was a 1. If so, this is an inlined constructor
    -- so they do not match.
    -- If it is a 0, we must read the pointer and check its tag.
    terminatorMain = Do $ CondBr (LocalReference bool nameCond) nameBlockFalse nameBlockCheck []

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
    terminatorCheck = Do $ CondBr (LocalReference bool tagCheck) nameBlockTrue nameBlockFalse []

    instructionsTrue :: [Named Instruction]
    instructionsTrue = compileExtractFields env supply10 address (fromIntegral $ headerSize * targetPointerSize (envTarget env)) fieldLayouts args
    terminatorTrue :: Named Terminator
    terminatorTrue = Do $ Br (toName branchId) []

    address = LocalReference (pointer t) addressName
    t = NamedTypeReference $ toName conId

    headerBits :: Word32
    headerBits = fromIntegral $ headerSize * targetPointerSize (envTarget env)
    headerType = IntegerType headerBits
    header = LocalReference headerType headerName

    blocks'
      = BasicBlock nameBlockCheck instructionsCheck terminatorCheck : 
        BasicBlock nameBlockTrue instructionsTrue terminatorTrue : 
        BasicBlock nameBlockFalse nextInstructions nextTerminator : blocks
