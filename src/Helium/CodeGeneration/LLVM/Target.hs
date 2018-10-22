module Helium.CodeGeneration.LLVM.Target where

data Target = Target
  { targetWordSize :: Int
  , targetGarbageCollectorBits :: Int
  }
