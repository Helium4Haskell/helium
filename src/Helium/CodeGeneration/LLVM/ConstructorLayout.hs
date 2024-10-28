-- The layout of data types is defined per constructor. Different constructors of the same data type
-- can thus have different size in memory.
--
-- # Constructors with arguments
-- Objects from constructors with arguments are allocated and passed by a pointer. The object consists
-- of a header and the fields.
--
-- The header consists of garbage collection information, a tag and flags that denote whether the
-- fields are in WHNF.
--
-- # Constructors without arguments
-- If a constructor has no arguments, we will not allocate objects of that constructor on the heap.
-- Instead, we use a special as the pointer. This value has a 1 in the least significant bit, to
-- distinguish it from actual pointers.

module Helium.CodeGeneration.LLVM.ConstructorLayout(constructorLayout, ConstructorLayout(..)) where

import Data.List(mapAccumL)
import Helium.Lvm.Common.Id(Id, stringFromId)
import qualified Helium.Lvm.Core.Type as Core
import Helium.CodeGeneration.LLVM.Utils
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Struct
import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium

data ConstructorLayout
  = LayoutInline 
    { layoutTagId :: Int
    }
  | LayoutPointer
    { layoutStruct :: Struct
    }

constructorLayout :: Target -> Iridium.DataType -> Int -> Iridium.DataTypeConstructor -> ConstructorLayout
constructorLayout target (Iridium.DataType constructors) index (Iridium.DataTypeConstructor conId tp)
  | fields == [] = LayoutInline index
  | otherwise = LayoutPointer struct
  where
    Iridium.FunctionType typeArgs typeReturn = Iridium.extractFunctionTypeNoSynonyms tp
    fields = [field | Right field <- typeArgs]

    tagBits = ceiling $ logBase 2.0 $ fromIntegral $ length constructors

    struct :: Struct
    struct = Struct (Just $ toName conId) tagBits index structFields

    structFields :: [StructField]
    (_, structFields) = mapAccumL toField 0 fields
    
    toField nextIndex fieldType
      | Core.typeIsStrict fieldType = (nextIndex, StructField fieldType Nothing) -- Do not use a bit in the header
      | otherwise = (nextIndex + 1, StructField fieldType $ Just nextIndex) -- Use a bit in the header
