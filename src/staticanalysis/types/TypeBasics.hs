-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypeBasics.hs : Basic functionality on types.
--
-------------------------------------------------------------------------------

module TypeBasics where

import List                 ( (\\), union )
import TypeRepresentation
import TypeSubstitution

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

instance Show TpScheme where
  show (Scheme qs nm tp) = 
     let unknownNames = filter (`notElem` (map fst nm)) qs 
         sub = listToSubstitution $ [ (i,TCon s) | (i,s) <- nm, i `elem` qs ]
                                 ++ zip unknownNames (map (\c -> TCon [c] ) ['a'..])         
     in show (sub |-> tp)

----------------------------------------------------------------------
--  basic functionality for types and type schemes

generalize :: [Int] -> Tp -> TpScheme
generalize monos tp = Scheme (ftv tp \\ monos) [] tp

generalizeAll :: Tp -> TpScheme
generalizeAll = generalize [] 

instantiate :: Int -> TpScheme -> (Int,Tp)
instantiate unique (Scheme as nameMap tp) = 
   let sub = listToSubstitution (zip as (map TVar [unique..]))
   in (unique + length as,sub |-> tp)
   
instantiateWithNameMap :: Int -> TpScheme -> (Int, Tp)
instantiateWithNameMap unique (Scheme qs nm tp) = 
   let sub = listToSubstitution [ (i,TCon s) | (i,s) <- nm, i `elem` qs ]
   in instantiate unique (Scheme (qs \\ (map fst nm)) [] (sub |-> tp))

unsafeInstantiate :: TpScheme -> Tp
unsafeInstantiate = snd . instantiate magicNumber
   where magicNumber = 123456789

arityOfTpScheme :: TpScheme -> Int
arityOfTpScheme (Scheme as nameMap tp) = arityOfTp tp

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
   
constantsInType :: Tp -> [String]
constantsInType (TVar i)     = []
constantsInType (TCon s)     = [s]
constantsInType (TApp t1 t2) = constantsInType t1 `union` constantsInType t2

priorityOfType :: Tp -> Int
priorityOfType tp = case leftSpine tp of 
       (TCon "->",[t1,t2]) -> 0
       (_        ,[]     ) -> 2
       (TCon "[]",[t1]   ) -> 2
       (TCon s   ,_      ) | isTupleConstructor s -> 2
       _                   -> 1
