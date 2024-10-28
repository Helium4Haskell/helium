{-| Module      :  Utils
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.CodeGeneration.LLVM.Utils where

import LLVM.AST as AST
import LLVM.AST.Constant
import LLVM.AST.AddrSpace
import Helium.Lvm.Common.Id(Id, idFromString, stringFromId, freshId, NameSupply, freshIdFromId)

toName :: Id -> Name
toName = mkName . stringFromId

toNamePrefixed :: String -> Id -> Name
toNamePrefixed prefix = mkName . (prefix ++) . stringFromId

-- Prevent collisions with previously generated identifiers
name_ :: Id
name_ = idFromString "$"

freshName :: NameSupply -> (Name, NameSupply)
freshName = freshNameFromId name_

freshNameFromId :: Id -> NameSupply -> (Name, NameSupply)
freshNameFromId oldId supply = (toName newId, supply')
  where
    (newId, supply') = freshIdFromId oldId supply

getElementPtr :: Operand -> [Int] -> Instruction
getElementPtr address indices = AST.GetElementPtr False address operands []
  where
    operands = map (ConstantOperand . Int 32 . fromIntegral) indices

trampolineType :: Type
trampolineType = pointer $ FunctionType voidPointer [thunkType, pointer taggedThunkPointer, IntegerType 16] False

thunkType :: Type
thunkType = pointer $ NamedTypeReference $ mkName "thunk"

thunkStructType :: Type
thunkStructType = NamedTypeReference $ mkName "thunk"

boolType :: Type
boolType = IntegerType 1

-- Bool denotes whether the value is in WHNF
taggedThunkPointer :: Type
taggedThunkPointer = StructureType True [voidPointer, boolType]

pointer :: Type -> Type
pointer t = AST.PointerType t (AddrSpace 0)

voidPointer :: Type
voidPointer = pointer (IntegerType 8)
