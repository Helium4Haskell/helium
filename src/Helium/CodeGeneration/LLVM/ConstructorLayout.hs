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

module Helium.CodeGeneration.LLVM.ConstructorLayout(gcBits, constructorLayout, ConstructorLayout(..), ConstructorFieldLayout(..), constructorSize) where

import Lvm.Common.Id(Id, stringFromId)
import Helium.CodeGeneration.LLVM.Utils
import Helium.CodeGeneration.LLVM.Target
import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import qualified Helium.CodeGeneration.Iridium.TypeEnvironment as TypeEnv
import LLVM.AST.Type as Type
import LLVM.AST.AddrSpace
import LLVM.AST.Operand
import LLVM.AST.Constant

gcBits :: Int
gcBits = 48

data ConstructorLayout
  = LayoutInline 
    { layoutTagId :: Int
    }
  | LayoutPointer
    { layoutTagId :: Int -- Identifies the constructor of the data type.
    , layoutTagBits :: (Int, Int)
    , layoutHeaderSize :: Int -- Number of pointer-sized fields that we need for the tag & flags.
    , layoutFields :: [ConstructorFieldLayout]
    }

data ConstructorFieldLayout
  = ConstructorFieldLayout
    { layoutFieldType :: Iridium.PrimitiveType
    , layoutFieldIndex :: Int
    -- * The index of bit in the tag of the constructor, which says whether this field is in WHNF
    , layoutFieldFlag :: Maybe Int
    }

constructorLayout :: TypeEnv.TypeEnv -> Target -> Iridium.DataType -> Int -> Iridium.DataTypeConstructor -> ConstructorLayout
constructorLayout env target (Iridium.DataType _ constructors) index (Iridium.DataTypeConstructor _ fields)
  | headerBits <= pointerSize - 1 && fields == [] = LayoutInline index
  | otherwise = LayoutPointer index (gcBits, gcBits + tagBits) headerSize fieldLayouts
  where
    tagBits = ceiling $ logBase 2.0 $ fromIntegral $ length constructors
    flagBits = length fields -- TODO: When adding strict fields, only count the fields that are not strict
    pointerSize = targetPointerSize target

    -- Number of bits that we need for the tag, flags that denote whether a field is evaluated and data for garbage collector.
    headerBits = tagBits + flagBits + gcBits -- Reserve `gcBits` bits for the garbage collector
    headerSize = (headerBits + pointerSize - 1) `div` pointerSize -- ceiling of headerBits / pointerSize

    fieldLayouts :: [ConstructorFieldLayout]
    -- TODO: When adding strict fields, change the types of the members and set layoutFieldFlag to Nothing
    -- for strict fields. Furthermore reordering the fields might help, for better alignment of data.
    -- That would help with small sized fields (like chars or bools).
    fieldLayouts = zipWith (\fieldType index -> ConstructorFieldLayout fieldType index (Just $ tagBits + gcBits + index)) fields [1..]

-- Number of bytes that we need for an allocation of this constructor
constructorSize :: Target -> ConstructorLayout -> Int
constructorSize target (LayoutInline _) = 0
constructorSize target (LayoutPointer _ _ headerSize fields) = bits `div` 8
  where
    bits = (headerSize + length fields) * (targetPointerSize target)
