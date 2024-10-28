module Helium.CodeGeneration.Iridium.Utils where

import Helium.CodeGeneration.Iridium.Data
import Helium.Lvm.Common.Id (NameSupply, mapWithSupply, splitNameSupply, idFromString)

mapMethodsWithSupply :: (NameSupply -> Declaration Method -> Declaration Method) -> NameSupply -> Module -> Module
mapMethodsWithSupply fn supply (Module name dependencies customs datas types abstracts methods) = Module name dependencies customs datas types abstracts methods'
  where
    methods' = mapWithSupply fn supply methods

mapBlocks :: (Instruction -> Instruction) -> Module -> Module
mapBlocks fn (Module name dependencies customs datas types abstracts methods) = Module name dependencies customs datas types abstracts $ map (fmap fnMethod) methods
  where
    fnMethod :: Method -> Method
    fnMethod (Method tp args rettype annotations entry blocks) = Method tp args rettype annotations (fnBlock entry) $ map fnBlock blocks
    fnBlock :: Block -> Block
    fnBlock (Block name instr) = Block name $ fn instr

mapBlocksWithSupply :: (NameSupply -> Instruction -> Instruction) -> NameSupply -> Module -> Module
mapBlocksWithSupply fn supply (Module name dependencies customs datas types abstracts methods) = Module name dependencies customs datas types abstracts $ mapWithSupply (\s -> fmap (fnMethod s)) supply methods
  where
    fnMethod :: NameSupply -> Method -> Method
    fnMethod s (Method tp args rettype annotations entry blocks) = Method tp args rettype annotations (fnBlock supply1 entry) $ mapWithSupply fnBlock supply2 blocks
      where
        (supply1, supply2) = splitNameSupply s
    fnBlock :: NameSupply -> Block -> Block
    fnBlock s (Block name instr) = Block name $ fn s instr

-- Takes a specified number of value arguments (Right).
-- Type arguments (Left) are preserved, but not counted.
paramsTakeValues :: Int -> [Either a b] -> ([Either a b], [Either a b])
paramsTakeValues n (Left tp : params) = (Left tp : taken, remaining)
  where
    (taken, remaining) = paramsTakeValues n params
paramsTakeValues 0 remaining = ([], remaining)
paramsTakeValues n (Right local : params) = (Right local : taken, remaining)
  where
    (taken, remaining) = paramsTakeValues (n - 1) params
paramsTakeValues _ _ = ([], [])
