----------------------------------------------------------------------------
-- The Helium Compiler : Static Analysis : a library for types
-- |
-- Maintainer  :  bastiaan@cs.uu.nl
-- Stability   :  experimental
-- Portability :  unknown
--
-- A qualified type is a plain type together with a list of predicates.
--
-----------------------------------------------------------------------------

module QualifiedTypes where

import TypeBasics
import TypeSubstitution
import List (union, (\\), sort )

infix 2 :=>

data QType      = Predicates :=> Tp
type Predicates = [Predicate]
data Predicate  = Predicate String Tp 
   deriving Eq

isAmbiguous :: QType -> Bool
isAmbiguous (ps :=> tp) = 
   not (null (ftv ps \\ ftv tp))

isGround :: Predicate -> Bool
isGround (Predicate s tp) = null (ftv tp)

hasPredicates :: QType -> Bool
hasPredicates (ps :=> tp) = not (null ps)

instance Show QType where
   show (ps :=> tp) = case ps of 
                         []  -> show tp
                         [p] -> show p ++ " => " ++ show tp
                         _   -> let list = foldr1 (\x y -> x++", "++y) (sort (map show ps))
                                in "(" ++ list ++ ") => " ++ show tp
   
instance Show Predicate where
   show (Predicate s tp) = if priorityOfType tp == 2 
                             then s ++ " " ++ show tp
                             else s ++ " (" ++ show tp ++ ")"
                        
instance Substitutable QType where
   sub |-> (ps :=> tp) = (sub |-> ps :=> sub |-> tp)
   ftv     (ps :=> tp) = ftv ps `union` ftv tp

instance Substitutable Predicate where
   sub |-> (Predicate s tp) = Predicate s (sub |-> tp)
   ftv     (Predicate s tp) = ftv tp
   
