module Helium.CodeGeneration.LLVM.Struct where

import qualified Helium.CodeGeneration.Iridium.Type as Iridium
import Helium.CodeGeneration.Iridium.Show()
import LLVM.AST (Name)

data Struct = Struct
  { typeName :: Maybe Name
  , tagSize :: Int
  , tagValue :: Int
  , fields :: [StructField]
  }
  deriving (Eq, Ord, Show)

data StructField = StructField
  { fieldType :: Iridium.PrimitiveType
  , fieldFlagIndex :: Maybe Int
  }
  deriving (Eq, Ord, Show)

tupleStruct :: Int -> Struct
tupleStruct arity = Struct Nothing 0 0 $ map field [0 .. arity - 1]
  where
    field index = StructField Iridium.TypeAny (Just index)