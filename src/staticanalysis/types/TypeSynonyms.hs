-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypeSynonyms.hs : Type definition of type synonyms that are ordered in
--    a list.
--
-------------------------------------------------------------------------------

module TypeSynonyms where

import TypeBasics
import TypeRepresentation
import Utils                 ( internalError )

----------------------------------------------------------------------
-- type synonyms

-- The type synonyms are ordered such that if type synonym A has a type 
-- constant B in its right-hand-side which is also a type synonym, then 
-- A is positioned before B in the list. Used for solving constraints.
type OrderedTypeSynonyms = [(String,Int,Tps -> Tp)]


expandType :: OrderedTypeSynonyms -> Tp -> Tp
expandType synonyms tp = 
   let (x,xs) = leftSpine (expandTypeConstructor synonyms tp)
   in foldl TApp x (map (expandType synonyms) xs)
                           
expandTypeConstructor :: OrderedTypeSynonyms -> Tp -> Tp
expandTypeConstructor synonyms tp = 
   case expandTypeConstructorOneStep synonyms tp of 
      Just tp' -> expandTypeConstructor synonyms tp'
      Nothing  -> tp

expandTypeConstructorsOneStep :: OrderedTypeSynonyms -> Tps -> Maybe Tps
expandTypeConstructorsOneStep synonyms tps = rec synonyms
   where constants = [ s | TCon s <- map (fst . leftSpine) tps ]
         rec [] = Nothing
         rec ((n,i,f):rest)
            |  n `elem` constants = Just (map replace tps)
            | otherwise           = rec rest
             
           where replace tp = case leftSpine tp of 
                                (TCon s,tps) | s == n
                                   -> if length tps == i 
                                        then f tps
                                        else internalError "SATypes.hs" "expandTypeConstructorsOneStep" "arity mismatch"
                                _  -> tp
   
expandTypeConstructorOneStep :: OrderedTypeSynonyms -> Tp -> Maybe Tp
expandTypeConstructorOneStep synonyms tp = 
   case expandTypeConstructorsOneStep synonyms [tp] of
      Just [tp'] -> Just tp'
      Nothing    -> Nothing
