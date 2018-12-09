module Helium.CodeGeneration.LLVM.CompileBind (compileBinds, toStruct, thunkStruct) where

import Data.Bits(shiftL, (.|.), (.&.))
import Data.Word(Word32)

import Lvm.Common.Id(idFromString, Id, NameSupply, mapWithSupply, splitNameSupply)
import Lvm.Common.IdMap(findMap)
import Lvm.Core.Module(Arity)
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

idThunk :: Id
idThunk = idFromString "$alloc_thunk"

idCon :: Id
idCon = idFromString "$alloc_con"

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
  , initialize supplyInit env (LocalReference (pointer t) nameStruct) struct $ additionalArg ++ argOperands
  )
  where
    t = structType env struct
    additionalArg = bindArguments env target
    (splitInstructions, argOperands) = unzip $ mapWithSupply (splitValueFlag env) supplyArgs (zip args $ map fieldType $ drop (length additionalArg) $ fields struct)
    (supplyArgs, supply1) = splitNameSupply supply
    (supplyInit, supply2) = splitNameSupply supply1
    (nameVoid, supply3) = freshName supply2
    (nameStruct, _) = freshNameFromId (nameSuggestion target) supply3

nameSuggestion :: Iridium.BindTarget -> Id
nameSuggestion (Iridium.BindTargetConstructor _) = idCon
nameSuggestion _ = idThunk

toStruct :: Env -> Iridium.BindTarget -> Int -> Either Int Struct
toStruct env (Iridium.BindTargetConstructor (Iridium.DataTypeConstructor _ conId _)) arity = case findMap conId (envConstructors env) of
  LayoutInline value -> Left value
  LayoutPointer struct -> Right struct
toStruct env (Iridium.BindTargetTuple arity) _ = Right $ tupleStruct arity
toStruct env target arity = Right $ Struct Nothing 32 tag fields
  where
    var = case target of
      Iridium.BindTargetFunction v -> v
      Iridium.BindTargetThunk v -> v
    tag = arity .|. (remaining `shiftL` 16)
    remaining = case var of
      Iridium.VarGlobal (Iridium.GlobalFunction _ (Iridium.FunctionType args _)) -> length args - arity
      _ -> (1 `shiftL` 16) - 1 -- All 16 bits to 1
    targetType = case var of
      Iridium.VarGlobal (Iridium.GlobalFunction _ _) -> Iridium.TypeGlobalFunction $ Iridium.FunctionType [Iridium.TypeUnsafePtr] Iridium.TypeAnyWHNF
      _ -> Iridium.TypeAnyWHNF
    fields = StructField targetType Nothing : map (\i -> StructField Iridium.TypeAny (Just i)) [0..arity - 1] 

toTrampolineOperand :: Env -> Iridium.Variable -> Operand
toTrampolineOperand _ (Iridium.VarGlobal (Iridium.GlobalFunction fn _)) = ConstantOperand $ Constant.GlobalReference trampolineType $ toNamePrefixed "trampoline$" fn
toTrampolineOperand env local = toOperand env local

-- A thunk has an additional argument, namely the function. We add that argument here
bindArguments :: Env -> Iridium.BindTarget -> [(Operand, Operand)]
bindArguments env (Iridium.BindTargetFunction var) = return (toTrampolineOperand env var, ConstantOperand $ Constant.Int 1 1)
bindArguments env (Iridium.BindTargetThunk var) = return (toOperand env var, ConstantOperand $ Constant.Int 1 1)
bindArguments env _ = []

expectedType :: Iridium.BindTarget -> Type
expectedType (Iridium.BindTargetConstructor (Iridium.DataTypeConstructor dataId _ _)) = NamedTypeReference $ toNamePrefixed "$data_" dataId
expectedType _ = voidPointer

-- Gives a struct given an arity. Does not specify a tag, this is intended for purposes when the tag is not known / needed.
thunkStruct :: Arity -> Struct
thunkStruct arity = Struct Nothing 32 0 fields
  where
    -- Function pointer & arguments
    fields = StructField Iridium.TypeUnsafePtr Nothing : map (\i -> StructField Iridium.TypeAny (Just i)) [0..arity - 1] 
