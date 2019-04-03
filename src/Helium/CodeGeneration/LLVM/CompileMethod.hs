{-| Module      :  CompileMethod
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.LLVM.CompileMethod (compileMethod, compileAbstractMethod) where

import Data.String(fromString)
import Data.Either

import Helium.CodeGeneration.LLVM.Env
import Helium.CodeGeneration.LLVM.Utils
import Helium.CodeGeneration.LLVM.CompileType(compileType, compileCallingConvention, voidPointer, toOperand, pointer, taggedThunkPointer, trampolineType, emptyThunkType)
import Helium.CodeGeneration.LLVM.CompileBlock(compileBlock)
import Helium.CodeGeneration.LLVM.Struct(Struct(..), StructField(..))
import Helium.CodeGeneration.LLVM.CompileBind(thunkStruct)
import Helium.CodeGeneration.LLVM.CompileStruct(structType, extractField)

import Lvm.Common.Id(Id, NameSupply, freshId, freshIdFromId, splitNameSupply, mapWithSupply, idFromString)
import qualified Lvm.Core.Type as Core

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import LLVM.AST
import qualified LLVM.AST.Global as Global
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage
import LLVM.AST.AddrSpace
import qualified LLVM.AST.Constant as Constant

-- llvm-hs-pure requires to set a name on the argument of a declared (abstract) function. However, when pretty printing / exporting the
-- IR this is not used. We thus can use a non-unique name.
unusedArgumentName :: Id
unusedArgumentName = idFromString "_argument"

compileAbstractMethod :: Env -> NameSupply -> Iridium.Declaration Iridium.AbstractMethod -> [Definition]
compileAbstractMethod env supply (Iridium.Declaration name visible _ _ method@(Iridium.AbstractMethod arity fnType annotations)) = toFunction env supply name visible annotations args fnType retType []
  where
    Iridium.FunctionType argTypes' retType = Iridium.abstractFunctionType (envTypeEnv env) method
    argTypes = [tp | Right tp <- argTypes']
    args = map (Iridium.Local unusedArgumentName) argTypes

compileMethod :: Env -> NameSupply -> Iridium.Declaration Iridium.Method -> [Definition]
compileMethod env supply (Iridium.Declaration name visible _ _ method@(Iridium.Method _ args retType annotations entry blocks)) = toFunction env supply2 name visible annotations args' fnType retType basicBlocks
  where
    fnType = Iridium.methodType method
    parameters :: [Parameter]
    parameters = [Parameter (compileType env t) (toName name) [] | Right (Iridium.Local name t) <- args]
    args' = [arg | Right arg <- args]
    basicBlocks :: [BasicBlock]
    basicBlocks = concat $ mapWithSupply (compileBlock env) supply1 (entry : blocks)
    (supply1, supply2) = splitNameSupply supply

toFunction :: Env -> NameSupply -> Id -> Iridium.Visibility -> [Iridium.Annotation] -> [Iridium.Local] -> Core.Type -> Core.Type -> [BasicBlock] -> [Definition]
toFunction env supply name visible annotations args fnType retType basicBlocks = trampoline ++ thunk ++ [def]
  where
    def = GlobalDefinition $ Function
      -- TODO: set Linkage to Private if possible
      -- TODO: set Visibility to Hidden or Protected, if that does not give issues with function pointers
      -- TODO: check whether setting [ParameterAttribute] on arguments and return type can improve performance
      { Global.linkage = linkage
      , Global.visibility = Default
      , Global.dllStorageClass = Nothing
      , Global.callingConvention = callConv
      , Global.returnAttributes = []
      , Global.returnType = compileType env (Core.typeToStrict $ if fake_io then Iridium.typeInt else retType)
      , Global.name = toName name
      , Global.parameters = (if fake_io then init parameters else parameters, {- varargs: -} False)
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

    linkage = case visible of
      Iridium.Private
        | not (null basicBlocks) && name /= idFromString "main" -> Private
      _ -> External

    parameters :: [Parameter]
    parameters = map (\(Iridium.Local name t) -> Parameter (compileType env t) (toName name) []) args

    callConv = compileCallingConvention $ Iridium.callingConvention annotations

    (supplyTrampoline1, supplyTrampoline2) = splitNameSupply supply

    arity = length args

    fake_io = Iridium.AnnotateFakeIO `elem` annotations

    trampoline :: [Definition]
    trampoline
      | Iridium.AnnotateTrampoline `notElem` annotations = []
      | otherwise = return $ GlobalDefinition $ Function
        { Global.linkage = linkage
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
        , Global.basicBlocks = if null basicBlocks then [] else --[trampolineBlock supply env name callConv args]
          [ BasicBlock
              (mkName "entry")
              (
                [ nameThunk := BitCast (LocalReference voidPointer $ mkName "$_thunk_void") (pointer structTy) [] ]
                ++ concat (
                  mapWithSupply
                    (\s (Iridium.Local arg _, index) -> extractField s env (LocalReference (pointer structTy) nameThunk) struct (index + 1) (StructField (Iridium.typeNotStrict Iridium.typeUnsafePtr) (Just index)) $ toName arg)
                    supplyTrampoline1
                    $ zip args [0..arity - 1]
                  )
                ++ trampolineInstructions
              )
              trampolineTerminator
          ]
        , Global.personalityFunction = Nothing
        , Global.metadata = []
        }
    [BasicBlock _ trampolineInstructions trampolineTerminator] = compileBlock env supplyTrampoline1 $ Iridium.Block (idFromString "entry") $ trampolineBody supplyTrampoline2 name args fnType $ Core.typeToStrict retType
    struct = thunkStruct arity
    structTy = structType env struct
    nameThunk = mkName "$_thunk"

    thunk :: [Definition]
    thunk
      | not (null args) || Iridium.AnnotateTrampoline `notElem` annotations = []
      | otherwise = return $ GlobalDefinition $ GlobalVariable
        { Global.name = toNamePrefixed "thunk$" name
        , Global.linkage = linkage
        , Global.visibility = Default
        , Global.dllStorageClass = Nothing
        , Global.threadLocalMode = Nothing
        , Global.unnamedAddr = Nothing
        , Global.isConstant = False
        , Global.type' = emptyThunkType
        , Global.addrSpace = AddrSpace 0
        , Global.initializer =
          if null basicBlocks then Nothing else
            Just $ Constant.Struct Nothing False
                [ Constant.Int 64 0 -- GC bits
                , Constant.Int 64 0 -- Given & remaining argument count
                , Constant.GlobalReference trampolineType $ toNamePrefixed "trampoline$" name
                ]
        , Global.section = Nothing
        , Global.comdat = Nothing
        , Global.alignment = 0
        , Global.metadata = []
        }

trampolineBody :: NameSupply -> Id -> [Iridium.Local] -> Core.Type -> Core.Type -> Iridium.Instruction
trampolineBody supply fn params fnType retType = foldr id call instrs
  where
    res = idFromString "$_result"
    res' = idFromString "$_result_any"
    (args, instrs) = unzip $ mapWithSupply trampolineCastArgument supply params
    retType' = Core.typeToStrict $ Core.TVar 0 -- Return type must be a pointer in LLVM
    call = Iridium.Let res (Iridium.Call (Iridium.GlobalFunction fn (length params) fnType) $ map (Right . Iridium.VarLocal) args)
      $ Iridium.Let res' (Iridium.Cast (Iridium.VarLocal $ Iridium.Local res retType) retType')
      $ Iridium.Return $ Iridium.VarLocal $ Iridium.Local res' retType'

trampolineCastArgument :: NameSupply -> Iridium.Local -> (Iridium.Local, Iridium.Instruction -> Iridium.Instruction)
trampolineCastArgument supply local@(Iridium.Local name tp)
  | Core.typeIsStrict tp =
    let (nameWhnf, _) = freshIdFromId name supply
    in
      ( Iridium.Local nameWhnf tp
      , Iridium.Let nameWhnf (Iridium.Eval $ Iridium.VarLocal $ Iridium.Local name $ Core.typeNotStrict tp)
      )
  | otherwise = (local, id)
trampolineBlock :: NameSupply -> Env -> Id -> Core.Type -> Iridium.FunctionType -> CallingConvention -> [Iridium.Local] -> BasicBlock
trampolineBlock supply env fn tp (Iridium.FunctionType argTypes _) callConv args = BasicBlock (mkName "trampoline_entry") instructions ret
  where
    instructions :: [Named Instruction]
    instructions =
      [ nameThunk := BitCast (LocalReference voidPointer $ mkName "$_thunk_void") (pointer t) []
      ]
      ++ concat (
        mapWithSupply
          (\s (index, argType) -> extractField s env (LocalReference (pointer t) nameThunk) struct (index + 1) (StructField argType (Just index)) $ mkName $ "$_arg" ++ show index)
          supply
          $ zip [0..] [t | Right t <- argTypes]
        )
      ++
        [ nameResult :=
          Call
            { tailCallKind = Nothing
            , callingConvention = callConv
            , returnAttributes = []
            , function = Right $ toOperand env (Iridium.VarGlobal $ Iridium.GlobalFunction fn arity tp)
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
