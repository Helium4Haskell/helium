-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypeBasics.hs : The data type that represents types (and basic functionality)
--
-------------------------------------------------------------------------------

module TypeBasics where

import List ( union )
import Char ( isDigit )

----------------------------------------------------------------------
-- data type and type synonym definitions

type Tps      = [Tp]
data Tp       = TVar Int
              | TCon String
              | TApp Tp Tp
  deriving Eq

----------------------------------------------------------------------
--  basic functionality for types

arityOfTp :: Tp -> Int
arityOfTp = length . fst . functionSpine

leftSpine :: Tp -> (Tp,Tps)
leftSpine = rec [] where
   rec tps (TApp t1 t2) = rec (t2:tps) t1
   rec tps tp           = (tp,tps)
   
functionSpine :: Tp -> (Tps,Tp)
functionSpine = rec [] where
   rec tps (TApp (TApp (TCon "->") t1) t2) = rec (t1:tps) t2
   rec tps tp                              = (reverse tps,tp)

functionSpineOfLength :: Int -> Tp -> (Tps, Tp)
functionSpineOfLength i tp = 
   let (as, a ) = functionSpine tp
       (bs, cs) = splitAt i as
   in (bs, foldr (.->.) a cs)
   
constantsInType :: Tp -> [String]
constantsInType (TVar _)     = []
constantsInType (TCon s)     = [s]
constantsInType (TApp t1 t2) = constantsInType t1 `union` constantsInType t2

priorityOfType :: Tp -> Int
priorityOfType tp = case leftSpine tp of 
       (TCon "->",[_,_]  ) -> 0
       (_        ,[]     ) -> 2
       (TCon "[]",[_]    ) -> 2
       (TCon s   ,_      ) | isTupleConstructor s -> 2
       _                   -> 1

freezeVariablesInType :: Tp -> Tp
freezeVariablesInType tp = 
   case tp of 
      TVar i   -> TCon ('_':show i)
      TCon s   -> TCon s
      TApp l r -> TApp (freezeVariablesInType l) (freezeVariablesInType r)

unfreezeVariablesInType :: Tp -> Tp
unfreezeVariablesInType tp = 
   case tp of 
      TVar i     -> TVar i
      TCon ('_':s) | all isDigit s && not (null s)
                 -> TVar (read s)
      TCon s     -> TCon s
      TApp l r   -> TApp (unfreezeVariablesInType l) (unfreezeVariablesInType r)

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

----------------------------------------------------------------------  
-- tests on types

isTVar :: Tp -> Bool
isTVar (TVar _) = True
isTVar _        = False

isTCon :: Tp -> Bool
isTCon (TCon _) = True
isTCon _        = False   

isTApp :: Tp -> Bool
isTApp (TApp _ _) = True
isTApp _          = False

isTupleConstructor :: String -> Bool                        
isTupleConstructor ('(':[]) = False
isTupleConstructor ('(':cs) = all (','==) (init cs) && last cs == ')'
isTupleConstructor _        = False

isIOType :: Tp -> Bool
isIOType (TApp (TCon "IO") _) = True
isIOType _                    = False

----------------------------------------------------------------------
-- show functions for types and type schemes

instance Show Tp where
   show tp = case leftSpine tp of 
       (TCon "->",[t1,t2]) -> rec (<1) t1 ++ " -> " ++ rec (const False) t2
       (TVar i   ,[]     ) -> 'v' : show i
       (TCon s   ,[]     ) -> s
       (TCon "[]",[t1]   ) -> "[" ++ rec (const False) t1 ++ "]"
       (TCon s   ,ts     ) | isTupleConstructor s -> let ts'  = map (rec (const False)) ts
                                                         f [] = ""
                                                         f xs = foldr1 (\x y -> x++", "++y) xs
                                                     in "(" ++ f ts' ++ ")"
       (t,ts) -> unwords (map (rec (<2)) (t:ts))

       where rec p t       = parIf (p (priorityOfType t)) (show t) 
             parIf True  s = "("++s++")"
             parIf False s = s
