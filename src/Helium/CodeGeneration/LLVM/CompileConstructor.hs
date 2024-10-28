module Helium.CodeGeneration.LLVM.CompileConstructor (dataTypeType, constructorType, compileExtractFields) where

import qualified Data.Bits as Bits
import Data.Word(Word32)

import Helium.Lvm.Common.Id(Id, NameSupply, mapWithSupply, splitNameSupply)
import Helium.Lvm.Common.IdMap(findMap)
import Helium.CodeGeneration.LLVM.Env (Env(..))
import Helium.CodeGeneration.LLVM.ConstructorLayout
import Helium.CodeGeneration.LLVM.Struct
import Helium.CodeGeneration.LLVM.CompileStruct
import Helium.CodeGeneration.LLVM.CompileType
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

dataTypeType :: Env -> Iridium.Declaration Iridium.DataType -> [(Id, ConstructorLayout)] -> Type
dataTypeType env (Iridium.Declaration dataName _ _ _ _) layouts = case pointerLayouts of
  -- TODO: Use integer type for datatypes where all constructors have no arguments
  -- [] -> envValueType env
  [(conId, _)] -> pointer $ NamedTypeReference (toName conId)
  _ -> voidPointer
  where
    pointerLayouts = filter (isPointer . snd) layouts
    isPointer (LayoutPointer _) = True
    isPointer _ = False

constructorType :: Env -> ConstructorLayout -> Type
constructorType env (LayoutInline tag) = envValueType env
constructorType env (LayoutPointer struct) = structTypeNoAlias env struct

compileExtractFields :: Env -> NameSupply -> Operand -> Struct -> [Maybe Id] -> [Named Instruction]
compileExtractFields env supply reference struct vars
  = concat
    $ mapWithSupply (compileExtractField env reference struct) supply
    $ zip3 (fields struct) vars [0..]

compileExtractField :: Env -> Operand -> Struct -> NameSupply -> (StructField, Maybe Id, Int) -> [Named Instruction]
compileExtractField env reference struct supply (field, Just name, index) = extractField supply env reference struct index field $ toName name
compileExtractField _ _ _ _ (_, Nothing, _) = []
