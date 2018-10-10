{-| Module      :  Utils
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.LLVM.Utils where

import LLVM.AST as AST
import LLVM.AST.Constant
import Lvm.Common.Id(Id, stringFromId, freshId, NameSupply)

toName :: Id -> Name
toName = mkName . stringFromId

freshName :: NameSupply -> (Name, NameSupply)
freshName supply = (toName newId, supply')
  where
    (newId, supply') = freshId supply

getElementPtr :: Operand -> [Int] -> Instruction
getElementPtr address indices = AST.GetElementPtr False address operands []
  where
    operands = map (ConstantOperand . Int 32 . fromIntegral) indices
