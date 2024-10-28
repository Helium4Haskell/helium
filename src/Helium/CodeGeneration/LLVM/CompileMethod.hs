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
import Helium.CodeGeneration.LLVM.CompileType(compileType, compileCallingConvention, toOperand)
import Helium.CodeGeneration.LLVM.CompileBlock(compileBlock)
import Helium.CodeGeneration.LLVM.Struct(Struct(..), StructField(..))
import Helium.CodeGeneration.LLVM.CompileStruct(structType, extractField)

import Helium.Lvm.Common.Id(Id, NameSupply, freshId, freshIdFromId, splitNameSupply, mapWithSupply, idFromString, stringFromId)
import qualified Helium.Lvm.Core.Type as Core

import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import LLVM.AST
import qualified LLVM.AST.Global as Global
import LLVM.AST.Visibility
import LLVM.AST.CallingConvention
import LLVM.AST.Linkage
import LLVM.AST.AddrSpace
import qualified LLVM.AST.Constant as Constant
import qualified LLVM.AST.Type as Type
import qualified LLVM.AST.IntegerPredicate as IntegerPredicate

import Data.Char

-- llvm-hs-pure requires to set a name on the argument of a declared (abstract) function. However, when pretty printing / exporting the
-- IR this is not used. We thus can use a non-unique name.
unusedArgumentName :: Id
unusedArgumentName = idFromString "_argument"

compileAbstractMethod :: Env -> NameSupply -> Iridium.Declaration Iridium.AbstractMethod -> [Definition]
compileAbstractMethod env supply (Iridium.Declaration name visible _ _ method@(Iridium.AbstractMethod _ fnType annotations)) = toFunction env supply name visible annotations args (Iridium.typeFromFunctionType fnType) retType []
  where
    Iridium.FunctionType argTypes' retType = fnType
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

packId :: Id -> Constant.Constant
packId name = Constant.Array Type.i8 $ map (Constant.Int 8) (0 : list)
  where
    list = reverse $ map (fromIntegral . ord) $ stringFromId name

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
      , Global.returnType = compileType env (Core.typeToStrict $ if implicitIO then Iridium.typeInt else retType)
      , Global.name = toName name
      , Global.parameters = (if implicitIO then init parameters else parameters, {- varargs: -} False)
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

    implicitIO = Iridium.AnnotateImplicitIO `elem` annotations

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
        , Global.parameters =
          (
            [ Parameter thunkType (mkName "thunk") []
            , Parameter (pointer taggedThunkPointer) (mkName $ "ptr_" ++ show (arity - 1)) []
            , Parameter (IntegerType 16) (mkName $ "remaining_" ++ show (arity - 1)) []
            ]
          , {- varargs: -} False
          )
        , Global.functionAttributes = []
        , Global.section = Nothing
        , Global.comdat = Nothing
        , Global.alignment = 0
        , Global.garbageCollectorName = Nothing
        , Global.prefix = Just $ packId name
        , Global.basicBlocks = if null basicBlocks then [] else
          [ BasicBlock
              (mkName "entry")
              (
                [ mkName "next_thunk_ptr" := getElementPtr (LocalReference thunkType $ mkName "thunk") [0, 1]
                , mkName ("next_thunk_" ++ show (arity - 1)) := Load False (LocalReference (pointer thunkType) $ mkName "next_thunk_ptr") Nothing 0 []
                ]
                ++ (if arity /= 0 then trampolineExtractArguments (arity - 1) else [])
                ++ trampolineInstructions
              )
              trampolineTerminator
          ]
        , Global.personalityFunction = Nothing
        , Global.metadata = []
        }
    [BasicBlock _ trampolineInstructions trampolineTerminator] = compileBlock env supplyTrampoline1 $ Iridium.Block (idFromString "entry") $ trampolineBody supplyTrampoline2 name args fnType $ Core.typeToStrict retType

    thunk :: [Definition]
    thunk
      | Iridium.AnnotateTrampoline `notElem` annotations = []
      | otherwise = return $ GlobalDefinition $ GlobalVariable
        { Global.name = toNamePrefixed "thunk$" name
        , Global.linkage = linkage
        , Global.visibility = Default
        , Global.dllStorageClass = Nothing
        , Global.threadLocalMode = Nothing
        , Global.unnamedAddr = Nothing
        , Global.isConstant = False
        , Global.type' = thunkStructType
        , Global.addrSpace = AddrSpace 0
        , Global.initializer =
          if null basicBlocks then Nothing else
            Just $ Constant.Struct Nothing False
                [ Constant.Int 64 0 -- Header (GC)
                , Constant.GlobalReference thunkType $ toNamePrefixed "thunk$" name -- 'next' points to self
                , Constant.GlobalReference trampolineType $ toNamePrefixed "trampoline$" name -- function pointer
                , Constant.Int 16 $ fromIntegral $ length args -- remaining: (length args) arguments remaining
                , Constant.Int 16 0 -- given: 0 arguments given
                , Constant.Array taggedThunkPointer []
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
    (args, instrs) = unzip $ zipWith trampolineCastArgument [0..] params
    retType' = Core.typeToStrict $ Core.TVar 0 -- Return type must be a pointer in LLVM
    call = Iridium.Let res (Iridium.Call (Iridium.GlobalFunction fn (length params) fnType) $ map (Right . Iridium.VarLocal) args)
      $ Iridium.Let res' (Iridium.Cast (Iridium.VarLocal $ Iridium.Local res retType) retType')
      $ Iridium.Return $ Iridium.VarLocal $ Iridium.Local res' retType'

trampolineCastArgument :: Int -> Iridium.Local -> (Iridium.Local, Iridium.Instruction -> Iridium.Instruction)
trampolineCastArgument index (Iridium.Local _ tp)
  | Core.typeIsStrict tp =
    let nameWhnf = idFromString $ "argument_whnf_" ++ show index
    in
      ( Iridium.Local nameWhnf tp
      , Iridium.Let nameWhnf (Iridium.Eval $ Iridium.VarLocal $ Iridium.Local nameThunk $ Core.typeNotStrict tp)
      )
  | otherwise = (Iridium.Local nameThunk tp, id)
  where
    nameThunk = idFromString $ "argument_" ++ show index

-- Variables:
--
-- Input:
-- i16 %remaining_i - Number of remaining arguments in the current thunk, before extracting argument i
-- <{i8*, i1}>* %ptr_i - Pointer to argument i
-- thunk* %next_thunk_i - Pointer to the next thunk, before extracting argument i
--
-- Output:
-- %remaining_{i-1}, %ptr_{i-1}, %next_thunk_{i-1} - For the next iteration
-- <{i8*, i1}> %{argument}
trampolineExtractArguments :: Int -> [Named Instruction]
trampolineExtractArguments 0 =
  [ mkName "argument_0" := Load False (LocalReference (pointer taggedThunkPointer) $ mkName "ptr_0") Nothing 0 []
  ]
trampolineExtractArguments i =
  -- argument_i = load ptr_i
  [ name "argument" := Load False (LocalReference (pointer taggedThunkPointer) $ name "ptr") Nothing 0 []
  -- Check whether this is the last element of the thunk object
  -- to_next_i = remaining_i == 1
  , name "to_next" := ICmp IntegerPredicate.EQ (LocalReference int16 $ name "remaining") (ConstantOperand $ Constant.Int 16 1) []

  -- Extract 'given' of next thunk
  , name "next_given_ptr" := getElementPtr (LocalReference thunkType $ name "next_thunk") [0, 4]
  , name "next_given" := Load False (LocalReference (pointer int16) $ name "next_given_ptr") Nothing 0 []

  -- Extract 'next' of next thunk
  , name "next_next_thunk_ptr" := getElementPtr (LocalReference thunkType $ name "next_thunk") [0, 1]
  , name "next_next_thunk" := Load False (LocalReference (pointer thunkType) $ name "next_next_thunk_ptr") Nothing 0 []

  -- remaining_{i-1} = to_next_i ? next_given_i : remaining_i - 1
  , name "remaining_decrement" := Sub False False (LocalReference int16 $ name "remaining") (ConstantOperand $ Constant.Int 16 1) []
  , next "remaining" := Select operandToNext
      (LocalReference int16 $ name "next_given")
      (LocalReference int16 $ name "remaining_decrement")
      []
  
  -- ptr_{i-1} = to_next_i ? {pointer to first argument of next_thunk} : &ptr_i[1]
  , name "next_thunk_first_arg" := getElementPtr (LocalReference thunkType $ name "next_thunk") [0, 5, 0]
  , name "ptr_increment" := getElementPtr (LocalReference (pointer taggedThunkPointer) $ name "ptr") [1]
  , next "ptr" := Select operandToNext
      (LocalReference (pointer taggedThunkPointer) $ name "next_thunk_first_arg")
      (LocalReference (pointer taggedThunkPointer) $ name "ptr_increment")
      []

  -- next_thunk_{i-1} = to_next_i ? next_next_thunk[i] : next_thunk[i]
  , next "next_thunk" := Select operandToNext
      (LocalReference thunkType $ name "next_next_thunk")
      (LocalReference thunkType $ name "next_thunk")
      []
  ] ++ trampolineExtractArguments (i - 1)
  where
    operandToNext = LocalReference boolType $ name "to_next"
    name str = mkName (str ++ "_" ++ show i)
    next str = mkName (str ++ "_" ++ show (i - 1))
    int16 = IntegerType 16
