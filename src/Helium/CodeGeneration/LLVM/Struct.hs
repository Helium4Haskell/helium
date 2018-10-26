module Helium.CodeGeneration.LLVM.Struct where

import qualified Helium.CodeGeneration.Iridium.Type as Iridium
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
