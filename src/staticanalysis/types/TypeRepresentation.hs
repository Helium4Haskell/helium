-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypeRepresentation.hs : The data type that represents types and
--    type schemes.
--
-------------------------------------------------------------------------------

module TypeRepresentation where

----------------------------------------------------------------------
-- data type and type synonym definitions

data TpScheme = Scheme [Int] [(Int,String)] Tp
type Tps      = [Tp]
data Tp       = TVar Int
              | TCon String
              | TApp Tp Tp
  deriving Eq
  
----------------------------------------------------------------------  
-- common types

intType, charType, floatType, boolType, stringType, voidType :: Tp
intType    = TCon "Int"
charType   = TCon "Char"
floatType  = TCon "Float"
boolType   = TCon "Bool"
stringType = TCon "String"
voidType   = tupleType []

infixr 5 .->.
(.->.) :: Tp -> Tp -> Tp
t1 .->. t2 = TApp (TApp (TCon "->") t1) t2

listType :: Tp -> Tp
listType t1 = TApp (TCon "[]") t1

ioType :: Tp -> Tp
ioType t1 = TApp (TCon "IO") t1

tupleType :: Tps -> Tp
tupleType tps = let name | null tps  = "()"
                         | otherwise = "("++replicate (length tps-1) ','++")"
                in foldl TApp (TCon name) tps

isTupleConstructor :: String -> Bool                        
isTupleConstructor ('(':[]) = False
isTupleConstructor ('(':cs) = all (','==) (init cs) && last cs == ')'
isTupleConstructor _        = False

isIOType :: Tp -> Bool
isIOType (TApp (TCon "IO") _) = True
isIOType _                    = False
