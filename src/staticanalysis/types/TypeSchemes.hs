-----------------------------------------------------------------------------
-- The Helium Compiler : Static Analysis : a library for types
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- A representation of type schemes. A type scheme is a (qualified) type
-- with a number of quantifiers (foralls) in front of it. A partial mapping 
-- from type variable (Int) to their name (String) is preserved.
--
-----------------------------------------------------------------------------

module TypeSchemes where

import TypeBasics
import QualifiedTypes
import TypeSubstitution
import TypeSynonyms
import TypeUnification
import TypeClasses
import List ( (\\), nub )

data TpScheme = TpScheme 
                { getQuantifiers     :: [Int]             
                , getNameMap         :: [(Int,String)]
                , getQualifiedType   :: QType
                }

instance Show TpScheme where
   show (TpScheme quantifiers namemap qtype) = 
      let sub1     = filter ((`elem` quantifiers) . fst) namemap 
          unknown  = quantifiers \\ map fst sub1
          sub2     = zip unknown [ [c] | c <- ['a'..], [c] `notElem` map snd sub1 ]
          subTotal = listToSubstitution [ (i, TCon s) | (i, s) <- sub1 ++ sub2 ]
      in show (subTotal |-> qtype)

instance Substitutable TpScheme where
   sub |-> (TpScheme quantifiers namemap qtype) = TpScheme quantifiers namemap (removeDom quantifiers sub |-> qtype)
   ftv     (TpScheme quantifiers namemap qtype) = ftv qtype \\ quantifiers

----------------------------------------------------------------------
--  basic functionality for types and type schemes

generalize :: [Int] -> Predicates -> Tp -> TpScheme
generalize monos preds tp = 
   let ftvTP              = ftv tp 
       p (Predicate _ tp) = any (`elem` ftvTP) (ftv tp)
   in TpScheme (ftv tp \\ monos) [] (filter p preds :=> tp)
                        
generalizeAll :: Tp -> TpScheme
generalizeAll = generalize [] []

instantiate :: Int -> TpScheme -> (Int, Predicates, Tp)
instantiate unique (TpScheme qs _ (ps :=> tp)) = 
   let sub = listToSubstitution (zip qs (map TVar [unique..]))
   in (unique + length qs, sub |-> ps, sub |-> tp)  
   
instantiateWithNameMap :: Int -> TpScheme -> (Int, Predicates, Tp) -- weg
instantiateWithNameMap unique (TpScheme qs nm qtp) = 
   let sub = listToSubstitution [ (i,TCon s) | (i,s) <- nm, i `elem` qs ]
   in instantiate unique (TpScheme (qs \\ (map fst nm)) [] (sub |-> qtp))

unsafeInstantiate :: TpScheme -> Tp
unsafeInstantiate scheme = tp
   where magicNumber = 123456789
         (_, _, tp)  = instantiate magicNumber scheme
   
arityOfTpScheme :: TpScheme -> Int
arityOfTpScheme (TpScheme _ _ (_ :=> tp)) = arityOfTp tp

isOverloaded :: TpScheme -> Bool
isOverloaded (TpScheme _ _ (xs :=> tp)) = not (null xs)

freezeFreeTypeVariables :: TpScheme -> TpScheme
freezeFreeTypeVariables scheme = 
   let sub = listToSubstitution (map f (ftv scheme))
       f i = (i, TCon ('_' : show i))
   in sub |-> scheme

{- unifiableTypeSchemes :: OrderedTypeSynonyms -> TpScheme -> TpScheme -> Bool
unifiableTypeSchemes typesynonyms s1 s2 =
   let i       = maximum (0 : ftv s1 ++ ftv s2) + 1
       (i',_,t1) = instantiate i  s1
       (_ ,_,t2) = instantiate i' s2
   in unifiable typesynonyms t1 t2 -}

genericInstanceOf :: OrderedTypeSynonyms -> ClassEnvironment -> TpScheme -> TpScheme -> Bool
genericInstanceOf synonyms classes scheme1 scheme2 =
   let -- monomorphic type variables are treated as constants
       s1 = freezeFreeTypeVariables scheme1
       s2 = freezeFreeTypeVariables scheme2
       -- substitution to fix the type variables in the first type scheme
       sub         = listToSubstitution (zip (getQuantifiers s1) [ TCon ('+':show i) | i <- [0..]])
       ps1 :=> tp1 = sub |-> getQualifiedType s1
       (_,ps2,tp2) = instantiate 123456789 s2
   in case mguWithTypeSynonyms synonyms tp1 tp2 of
         Left _         -> False
         Right (_,sub2) -> entailList synonyms classes ps1 (sub2 |-> ps2)
