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

import Lvm.Common.Id(Id, stringFromId)
import Helium.CodeGeneration.LLVM.Utils
import Helium.CodeGeneration.LLVM.Target
import Helium.CodeGeneration.LLVM.Struct
import qualified Helium.CodeGeneration.Iridium.Data as Iridium
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.CodeGeneration.Iridium.TypeEnvironment as TypeEnv

data ConstructorLayout
  = LayoutInline 
    { layoutTagId :: Int
    }
  | LayoutPointer
    { layoutStruct :: Struct
    }

constructorLayout :: TypeEnv.TypeEnv -> Target -> Iridium.DataType -> Int -> Iridium.DataTypeConstructor -> ConstructorLayout
constructorLayout env target (Iridium.DataType constructors) index (Iridium.DataTypeConstructor _ conId fields)
  | fields == [] = LayoutInline index
  | otherwise = LayoutPointer struct
  where
    tagBits = ceiling $ logBase 2.0 $ fromIntegral $ length constructors

    struct :: Struct
    struct = Struct (Just $ toName conId) tagBits index structFields

    structFields :: [StructField]
    structFields = zipWith (\fieldType fieldIndex -> StructField fieldType (Just fieldIndex)) fields [0..]
