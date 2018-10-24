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
import Helium.CodeGeneration.LLVM.CompileBind
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.CompileConstructor(compileExtractFields)
import Helium.CodeGeneration.LLVM.CompileStruct
import qualified Helium.CodeGeneration.LLVM.Builtins as Builtins

import Lvm.Common.Id(Id, NameSupply, splitNameSupply, mapWithSupply)
import Lvm.Common.IdMap(findMap)

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.CodeGeneration.Iridium.TypeEnvironment as Iridium
import LLVM.AST as AST
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage
import LLVM.AST.Constant (Constant(Int, Vector))
import qualified LLVM.AST.IntegerPredicate as IntegerPredicate

data Partial = Partial [Named Instruction] (Named Terminator) [BasicBlock]

infixr 3 +>
(+>) :: [Named Instruction] -> Partial -> Partial
instrs1 +> (Partial instrs2 terminator blocks) = Partial (instrs1 ++ instrs2) terminator blocks

compileBlock :: Env -> NameSupply -> Iridium.Block -> [BasicBlock]
compileBlock env supply (Iridium.Block name instruction) = BasicBlock (toName name) instrs term : blocks
  where
    Partial instrs term blocks = compileInstruction env supply instruction

compileInstruction :: Env -> NameSupply -> Iridium.Instruction -> Partial
compileInstruction env supply (Iridium.Let name expr next) = compileExpression env supply1 expr (toName name) +> compileInstruction env supply2 next
  where
    (supply1, supply2) = splitNameSupply supply
compileInstruction env supply (Iridium.LetAlloc binds next) =
  compileBinds env supply1 binds
  +> compileInstruction env supply2 next
  where
    (supply1, supply2) = splitNameSupply supply
compileInstruction env supply (Iridium.Jump to) = Partial [] (Do $ Br (toName to) []) []
compileInstruction env supply (Iridium.Return var) = Partial [] (Do $ Ret (Just $ toOperand env var) []) []
-- A Match has undefined behaviour if it does not match, so we do not need to check whether it actually matches.
compileInstruction env supply (Iridium.Match var _ [] next) = compileInstruction env supply next
compileInstruction env supply (Iridium.Match var (Iridium.DataTypeConstructor _ conId _) args next)
  = [ addressName := AST.BitCast (toOperand env var) (pointer t) []
    ]
    +> compileExtractFields env supply'' address struct args
    +> compileInstruction env supply''' next
  where
    t = NamedTypeReference $ toName conId
    (addressName, supply') = freshName supply
    address = LocalReference (pointer t) addressName
    (supply'', supply''') = splitNameSupply supply'
    LayoutPointer struct = findMap conId (envConstructors env)
compileInstruction env supply (Iridium.If var (Iridium.PatternCon con@(Iridium.DataTypeConstructor _ conId _)) whenTrue whenFalse)
  = compileIfMatchConstructor env supply var con conLayout whenTrue whenFalse
  where
    conLayout = findMap conId (envConstructors env)

compileExpression :: Env -> NameSupply -> Iridium.Expr -> Name -> [Named Instruction]
compileExpression env supply (Iridium.Literal (Iridium.LitInt value)) name = [name := ZExt (ConstantOperand constant) (envValueType env) []]
  where
    constant :: Constant
    constant = Int (fromIntegral $ targetWordSize $ envTarget $ env) (fromIntegral $ value)
compileExpression env supply (Iridium.Literal (Iridium.LitString value)) name =
  [ namePtr := Alloca vectorType Nothing 0 []
  , Do $ Store False (LocalReference (pointer vectorType) namePtr) (ConstantOperand vector) Nothing 0 []
  , name := Call
    { tailCallKind = Nothing
    , callingConvention = Fast
    , returnAttributes = []
    , function = Right $ Builtins.unpackString
    , arguments =
      [ (ConstantOperand $ Int 32 $ fromIntegral $ length value, [])
      , (LocalReference (pointer vectorType) namePtr, [])
      ]
    , functionAttributes = []
    , metadata = []
    }
  ]
  where
    (namePtr, _) = freshName supply
    vectorType = VectorType (fromIntegral $ length value) (IntegerType 32)
    vector = Vector $ map (\c -> Int 32 $ fromIntegral $ fromEnum c) value
-- TODO: Float literals
compileExpression env supply (Iridium.Call to args) name =
  [ name := Call
      { tailCallKind = Nothing
      , callingConvention = Fast
      , returnAttributes = []
      , function = Right $ toOperand env (Iridium.VarGlobal to)
      , arguments = map (\arg -> (toOperand env arg, [])) args
      , functionAttributes = []
      , metadata = []
      }
  ]
compileExpression env supply (Iridium.Eval var) name = compileEval env supply (toOperand env var) (Iridium.variableType var) name
compileExpression env supply (Iridium.Var var) name = cast env (toOperand env var) name t t
  where t = Iridium.variableType var
compileExpression env supply (Iridium.Cast var toType) name = cast env (toOperand env var) name t toType
  where t = Iridium.variableType var
compileExpression env supply expr@(Iridium.Phi branches) name = [name := Phi (compileType env t) (map compileBranch branches) []]
  where
    t = Iridium.typeOfExpr expr
    compileBranch :: Iridium.PhiBranch -> (Operand, Name)
    compileBranch (Iridium.PhiBranch blockId var) = (toOperand env var, toName blockId)

compileEval :: Env -> NameSupply -> Operand -> Iridium.PrimitiveType -> Name -> [Named Instruction]
compileEval env supply operand Iridium.TypeAny name =
  [ namePtr := ExtractValue operand [0] []
  , nameIsWHNF := ExtractValue operand [1] []
  , name := callEval (LocalReference voidPointer $ namePtr) (LocalReference bool $ nameIsWHNF)
  ]
  where
    (namePtr, supply') = freshName supply
    (nameIsWHNF, _) = freshName supply'
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
    expected = ConstantOperand $ Int (fromIntegral $ targetWordSize $ envTarget env) (fromIntegral tag * 2 + 1)
    terminator :: Named Terminator
    terminator = Do $ CondBr (LocalReference bool nameCond) (toName whenTrue) (toName whenFalse) []
    (nameInt, supply') = freshName supply
    (nameCond, supply'') = freshName supply'
compileIfMatchConstructor env supply var (Iridium.DataTypeConstructor _ conId _) (LayoutPointer struct) whenTrue whenFalse
  = Partial instructionsMain terminatorMain blocks
  where
    (supplyExtractTag, supply1) = splitNameSupply supply
    (nameCasted, supply2) = freshName supply1
    (nameCond, supply3) = freshName supply2
    (nameTagCond, supply4) = freshName supply3
    (nameBlockCheck, _) = freshName supply4

    operand = toOperand env var

    instructionsMain :: [Named Instruction]
    instructionsMain =
      -- Convert pointer to int & truncate to a single bit
      [ nameCond := PtrToInt (toOperand env var) bool [] ]
    terminatorMain :: Named Terminator
    -- Check if the least significant bit of the pointer was a 1. If so, this is an inlined constructor
    -- so they do not match.
    -- If it is a 0, we must read the pointer and check its tag.
    terminatorMain = Do $ CondBr (LocalReference bool nameCond) (toName whenFalse) nameBlockCheck []

    t = pointer $ structType env struct

    instructionsCheck :: [Named Instruction]
    instructionsCheck = [ nameCasted := BitCast operand t [] ]
      ++ checkTag supply env (LocalReference t nameCasted) struct nameTagCond

    terminatorCheck :: Named Terminator
    terminatorCheck = Do $ CondBr (LocalReference bool nameTagCond) (toName whenTrue) (toName whenFalse) []

    blocks = [BasicBlock nameBlockCheck instructionsCheck terminatorCheck]
