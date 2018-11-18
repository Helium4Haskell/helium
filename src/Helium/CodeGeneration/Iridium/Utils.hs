module Helium.CodeGeneration.Iridium.Utils where

import Helium.CodeGeneration.Iridium.Data
import Lvm.Common.Id (NameSupply, mapWithSupply, splitNameSupply, idFromString)

mapBlocks :: (Instruction -> Instruction) -> Module -> Module
mapBlocks fn (Module name dependencies customs datas abstracts methods) = Module name dependencies customs datas abstracts $ map (fmap fnMethod) methods
  where
    fnMethod :: Method -> Method
    fnMethod (Method args rettype annotations entry blocks) = Method args rettype annotations (fnBlock entry) $ map fnBlock blocks
    fnBlock :: Block -> Block
    fnBlock (Block name instr) = Block name $ fn instr


mapBlocksWithSupply :: (NameSupply -> Instruction -> Instruction) -> NameSupply -> Module -> Module
mapBlocksWithSupply fn supply (Module name dependencies customs datas abstracts methods) = Module name dependencies customs datas abstracts $ mapWithSupply (\s -> fmap (fnMethod s)) supply methods
  where
    fnMethod :: NameSupply -> Method -> Method
    fnMethod s (Method args rettype annotations entry blocks) = Method args rettype annotations (fnBlock supply1 entry) $ mapWithSupply fnBlock supply2 blocks
      where
        (supply1, supply2) = splitNameSupply s
    fnBlock :: NameSupply -> Block -> Block
    fnBlock s (Block name instr) = Block name $ fn s instr
