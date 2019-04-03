module Helium.CodeGeneration.LLVM.CompileBind (compileBinds, toStruct, thunkStruct) where

import Data.Bits(shiftL, (.|.), (.&.))
import Data.Word(Word32)
import Data.Either

import Lvm.Common.Id(idFromString, Id, NameSupply, mapWithSupply, splitNameSupply)
import Lvm.Common.IdMap(findMap)
import qualified Lvm.Core.Type as Core
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
  = compileBind' env supply b $ toStruct env target $ length $ filter isRight args

compileBind' :: Env -> NameSupply -> Iridium.Bind -> Either Int Struct -> ([Named Instruction], [Named Instruction])
compileBind' env supply (Iridium.Bind varId target _) (Left tag) = 
  ( [toName varId := AST.IntToPtr (ConstantOperand $ Constant.Int (fromIntegral $ targetWordSize $ envTarget env) value) voidPointer []]
  , [])
  where
    -- Put a '1' in the least significant bit to distinguish it from a pointer.
    value :: Integer
    value = fromIntegral tag * 2 + 1
compileBind' env supply bind@(Iridium.Bind varId target args) (Right struct) =
  ( concat splitInstructions
    ++ allocate env nameVoid nameStruct t struct
    ++ castBind
  , concat additionalArgInstructions
    ++ initialize supplyInit env (LocalReference (pointer t) nameStruct) struct (additionalArg ++ argOperands)
  )
  where
    t = structType env struct
    (additionalArgInstructions, additionalArg) = unzip $ bindArguments env supplyAdditionalArgs target
    args' = [arg | Right arg <- args]
    (splitInstructions, argOperands) = unzip $ mapWithSupply (splitValueFlag env) supplyArgs (zip args' $ map fieldType $ drop (length additionalArg) $ fields struct)
    (supplyArgs, supply1) = splitNameSupply supply
    (supplyInit, supply2) = splitNameSupply supply1
    (supplyAdditionalArgs, supply3) = splitNameSupply supply2
    (nameVoid, supply4) = freshName supply3
    (nameStruct, _) = freshNameFromId (nameSuggestion target) supply3
    whnf = Iridium.typeIsStrict $ Iridium.bindType (envTypeEnv env) bind
    castBind
      | whnf = [toName varId := BitCast (LocalReference voidPointer nameVoid) voidPointer []]
      | otherwise =
        [toName varId := InsertValue
          (ConstantOperand $ Constant.Struct Nothing True [Constant.Undef voidPointer, Constant.Int 1 0])
          (LocalReference voidPointer nameVoid)
          [0]
          []
        ]

nameSuggestion :: Iridium.BindTarget -> Id
nameSuggestion (Iridium.BindTargetConstructor _) = idCon
nameSuggestion _ = idThunk

toStruct :: Env -> Iridium.BindTarget -> Int -> Either Int Struct
toStruct env (Iridium.BindTargetConstructor (Iridium.DataTypeConstructor conId _)) arity = case findMap conId (envConstructors env) of
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
      Iridium.VarGlobal (Iridium.GlobalFunction _ fnArity _) -> fnArity - arity
      _ -> (1 `shiftL` 16) - 1 -- All 16 bits to 1
    targetType = case var of
      Iridium.VarGlobal (Iridium.GlobalFunction _ _ _) -> Core.TStrict $ Core.TCon $ Core.TConDataType $ idFromString "$Trampoline"
      _ -> Core.TVar (-1)
    fields = StructField targetType Nothing : map (\i -> StructField (Core.TVar i) (Just i)) [0..arity - 1] 

toTrampolineOperand :: Env -> Iridium.Variable -> Operand
toTrampolineOperand _ (Iridium.VarGlobal (Iridium.GlobalFunction fn _ _)) = ConstantOperand $ Constant.GlobalReference trampolineType $ toNamePrefixed "trampoline$" fn
toTrampolineOperand env local = toOperand env local

-- A thunk has an additional argument, namely the function. We add that argument here
bindArguments :: Env -> NameSupply -> Iridium.BindTarget -> [([Named Instruction], (Operand, Operand))]
bindArguments env _ (Iridium.BindTargetFunction var) = return ([], (toTrampolineOperand env var, ConstantOperand $ Constant.Int 1 1))
bindArguments env supply (Iridium.BindTargetThunk var)
  | Iridium.typeIsStrict (Iridium.variableType var) = return ([], (toOperand env var, ConstantOperand $ Constant.Int 1 1))
  | otherwise = return
    ( [ name := ExtractValue (toOperand env var) [0] [] ]
    , ( (LocalReference voidPointer name)
      , ConstantOperand $ Constant.Int 1 1
      )
    )
    where
      (name, _) = freshName supply
bindArguments env _ _ = []

-- Gives a struct given an arity. Does not specify a tag, this is intended for purposes when the tag is not known / needed.
thunkStruct :: Int -> Struct
thunkStruct arity = Struct Nothing 32 0 fields
  where
    -- Function pointer & arguments
    fields = StructField (Core.TStrict $ Core.TCon $ Core.TConDataType $ idFromString "$UnsafePtr") Nothing : map (\i -> StructField Iridium.typeUnsafePtr (Just i)) [0..arity - 1] 
