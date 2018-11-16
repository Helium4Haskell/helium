{-| Module      :  CompileMethod
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.LLVM.CompileMethod (compileMethod, compileAbstractMethod) where

import Data.String(fromString)

import Helium.CodeGeneration.LLVM.Env
import Helium.CodeGeneration.LLVM.Utils
import Helium.CodeGeneration.LLVM.CompileType(compileType, compileCallingConvention, voidPointer, toOperand, pointer, taggedThunkPointer)
import Helium.CodeGeneration.LLVM.CompileBlock(compileBlock)
import Helium.CodeGeneration.LLVM.Struct(Struct(..), StructField(..))
import Helium.CodeGeneration.LLVM.CompileBind(thunkStruct)
import Helium.CodeGeneration.LLVM.CompileStruct(structType, extractField)

import Lvm.Common.Id(Id, NameSupply, freshId, splitNameSupply, mapWithSupply, idFromString)

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import LLVM.AST
import qualified LLVM.AST.Global as Global
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage

-- llvm-hs-pure requires to set a name on the argument of a declared (abstract) function. However, when pretty printing / exporting the
-- IR this is not used. We thus can use a non-unique name.
unusedArgumentName :: Id
unusedArgumentName = idFromString "_argument"

compileAbstractMethod :: Env -> NameSupply -> Iridium.Declaration Iridium.AbstractMethod -> [Definition]
compileAbstractMethod env supply (Iridium.Declaration name _ _ (Iridium.AbstractMethod (Iridium.FunctionType argTypes retType) annotations)) = toFunction env supply name annotations args retType []
  where
    args = map (Iridium.Local unusedArgumentName) argTypes

compileMethod :: Env -> NameSupply -> Iridium.Declaration Iridium.Method -> [Definition]
compileMethod env supply (Iridium.Declaration name _ _ (Iridium.Method args retType annotations entry blocks)) = toFunction env supply2 name annotations args retType basicBlocks
  where
    parameters :: [Parameter]
    parameters = map (\(Iridium.Local name t) -> Parameter (compileType env t) (toName name) []) args
    basicBlocks :: [BasicBlock]
    basicBlocks = concat $ mapWithSupply (compileBlock env) supply1 (entry : blocks)
    (supply1, supply2) = splitNameSupply supply

toFunction :: Env -> NameSupply -> Id -> [Iridium.Annotation] -> [Iridium.Local] -> Iridium.PrimitiveType -> [BasicBlock] -> [Definition]
toFunction env supply name annotations args retType basicBlocks = trampoline ++ [def]
  where
    def = GlobalDefinition $ Function
      -- TODO: set Linkage to Private if possible
      -- TODO: set Visibility to Hidden or Protected, if that does not give issues with function pointers
      -- TODO: check whether setting [ParameterAttribute] on arguments and return type can improve performance
      { Global.linkage = External
      , Global.visibility = Default
      , Global.dllStorageClass = Nothing
      , Global.callingConvention = callConv
      , Global.returnAttributes = []
      , Global.returnType = compileType env retType
      , Global.name = toName name
      , Global.parameters = (parameters, {- varargs: -} False)
      , Global.functionAttributes = []
      , Global.section = Nothing
      , Global.comdat = Nothing
      , Global.alignment = 0
      , Global.garbageCollectorName = Nothing
      , Global.prefix = Nothing
      , Global.basicBlocks = basicBlocks
      , Global.personalityFunction = Nothing
      , Global.metadata = []
      }
    parameters :: [Parameter]
    parameters = map (\(Iridium.Local name t) -> Parameter (compileType env t) (toName name) []) args

    callConv = compileCallingConvention $ Iridium.callingConvention annotations

    trampoline :: [Definition]
    trampoline
      | Iridium.AnnotateTrampoline `notElem` annotations = []
      | otherwise = return $ GlobalDefinition $ Function
        { Global.linkage = External
        , Global.visibility = Default
        , Global.dllStorageClass = Nothing
        , Global.callingConvention = callConv
        , Global.returnAttributes = []
        , Global.returnType = voidPointer
        , Global.name = toNamePrefixed "trampoline$" name
        , Global.parameters = ([Parameter voidPointer (mkName "$_thunk_void") []], {- varargs: -} False)
        , Global.functionAttributes = []
        , Global.section = Nothing
        , Global.comdat = Nothing
        , Global.alignment = 0
        , Global.garbageCollectorName = Nothing
        , Global.prefix = Nothing
        , Global.basicBlocks = if null basicBlocks then [] else [trampolineBlock supply env name callConv args]
        , Global.personalityFunction = Nothing
        , Global.metadata = []
        }

-- extractField :: NameSupply -> Env -> Operand -> Struct -> Int -> StructField -> Name -> [Named Instruction]
trampolineBlock :: NameSupply -> Env -> Id -> CallingConvention -> [Iridium.Local] -> BasicBlock
trampolineBlock supply env fn callConv args = BasicBlock (mkName "trampoline_entry") instructions ret
  where
    instructions :: [Named Instruction]
    instructions =
      [ nameThunk := BitCast (LocalReference voidPointer $ mkName "$_thunk_void") (pointer t) []
      ]
      ++ concat (
        mapWithSupply
          (\s index -> extractField s env (LocalReference (pointer t) nameThunk) struct (index + 1) (StructField Iridium.TypeAny (Just index)) $ mkName $ "$_arg" ++ show index)
          supply
          [0..arity - 1]
        )
      ++
        [ nameResult :=
          Call
            { tailCallKind = Nothing
            , callingConvention = callConv
            , returnAttributes = []
            , function = Right $ toOperand env (Iridium.VarGlobal $ Iridium.Global fn $ Iridium.FunctionType (map Iridium.localType args) Iridium.TypeAnyWHNF)
            , arguments = map (\index -> (LocalReference taggedThunkPointer $ mkName $ "$_arg" ++ show index, [])) [0..arity - 1]
            , functionAttributes = []
            , metadata = []
            }
        ]
    ret :: Named Terminator
    ret = Do $ Ret (Just $ LocalReference voidPointer nameResult) []
    nameThunk = mkName "$_thunk"
    nameResult = mkName "$_result"

    arity = length args

    -- Struct representing a thunk for this function
    -- Note that we ignore the value for the tag and the type for the function pointer, as we don't need those
    struct = thunkStruct arity
    t = structType env struct
