module TypeSchemeBasics where

import TypeBasics
import TypeClasses
import TypeSubstitution
import TypeSynonyms
import TypeUnification
import List ( (\\), nub )

data TpScheme = TpScheme 
                { getQuantifiers      :: [Int]             
                , getTypeClassContext :: ClassPredicates
                , getNameMap          :: [(Int,String)]
                , getSimpleType       :: Tp
                }
               
instance Show TpScheme where
  show scheme@(TpScheme qs ps nm tp) = 
     let sub1        = filter ((`elem` qs) . fst) nm
         unknownInts = filter (`notElem` map fst sub1) qs
         sub2        = zip unknownInts [ [c] | c <- ['a'..], [c] `notElem` map snd sub1 ]
         subTotal    = listToSubstitution [ (i, TCon s) | (i, s) <- sub1 ++ sub2 ]
         predicates  = [ (s,subTotal |-> tps) | (s,tps) <- ps ]
     in showClassPredicates predicates ++ show (subTotal |-> tp)

instance Substitutable TpScheme where    
   sub |-> (TpScheme monos ps nm tp) = let sub' = removeDom monos sub
                                           ps'  = [ (s,sub' |-> tps) | (s,tps) <- ps ]
                                       in TpScheme monos ps' nm (sub' |-> tp)
   ftv     (TpScheme monos ps _  tp) = nub (ftv tp) \\ monos

----------------------------------------------------------------------
--  basic functionality for types and type schemes

generalize :: [Int] -> Tp -> TpScheme
generalize monos tp = TpScheme (ftv tp \\ monos) [] [] tp

generalizeAll :: Tp -> TpScheme
generalizeAll = generalize [] 

gen' :: [Int] -> ClassPredicates -> Tp -> TpScheme
gen' monos preds tp = 
   let ftvTP      = ftv tp 
       p          = any (`elem` ftvTP) . ftv . snd
   in TpScheme (ftv tp \\ monos) (filter p preds) [] tp

instantiate :: Int -> TpScheme -> (Int,Tp)
instantiate unique (TpScheme qs tcc nm tp) = 
   let sub = listToSubstitution (zip qs (map TVar [unique..]))
   in (unique + length qs,sub |-> tp)
   
instantiateWithNameMap :: Int -> TpScheme -> (Int, Tp) -- ??
instantiateWithNameMap unique (TpScheme qs tcc nm tp) = 
   let sub = listToSubstitution [ (i,TCon s) | (i,s) <- nm, i `elem` qs ]
   in instantiate unique (TpScheme (qs \\ (map fst nm)) tcc [] (sub |-> tp))

unsafeInstantiate :: TpScheme -> Tp
unsafeInstantiate = snd . instantiate magicNumber
   where magicNumber = 123456789

inst' :: Int -> TpScheme -> (Int, ClassPredicates, Tp)
inst' unique (TpScheme qs ps _ tp) = 
   let sub = listToSubstitution (zip qs (map TVar [unique..]))
   in (unique + length qs, [ (s,sub |-> tps) | (s,tps) <- ps ], sub |-> tp)

-------------------------------------------------------------

arityOfTpScheme :: TpScheme -> Int
arityOfTpScheme (TpScheme _ _ _ tp) = arityOfTp tp     

------------- unification 
freezeMonosInTypeSchemes :: [TpScheme] -> [TpScheme]
freezeMonosInTypeSchemes xs = 
   let sub = listToSubstitution (zip (ftv xs) [ TCon ('_':show i) | i <- [1..]] )
   in sub |-> xs
                           
unifiableTypeSchemes :: OrderedTypeSynonyms -> TpScheme -> TpScheme -> Bool
unifiableTypeSchemes typesynonyms s1 s2 =
   let i       = maximum (0 : ftv s1 ++ ftv s2) + 1
       (i',t1) = instantiate i  s1
       (_ ,t2) = instantiate i' s2
   in unifiable typesynonyms t1 t2

genericInstanceOf :: OrderedTypeSynonyms -> TpScheme -> TpScheme -> Bool
genericInstanceOf typesynonyms scheme1@(TpScheme qs1 tcc1 nm1 t1) scheme2@(TpScheme qs2 tcc2 nm2 t2) =
      let [TpScheme qs1 tcc1 _ tp1,scheme2'] = freezeMonosInTypeSchemes [scheme1,scheme2]
          sub    = listToSubstitution (zip (ftv [scheme1,scheme2]) [ TCon ('_':show i) | i <- [0..]])
          sub'   = listToSubstitution (zip qs1 [ TCon ('+':show i) | i <- [0..]])
          t1'    = sub' |-> tp1
          t2'    = unsafeInstantiate scheme2'
      in unifiable typesynonyms t1' t2'
