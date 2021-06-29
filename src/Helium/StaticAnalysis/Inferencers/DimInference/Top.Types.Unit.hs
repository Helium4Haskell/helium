-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  portable
--
-- An adaptation of Top.Types.Primitves for unit types
--
-----------------------------------------------------------------------------

module Top.Unit.Primitves where

import Data.List (union, isPrefixOf)
import Data.Char (isDigit, isSpace)

-----------------------------------------------------------------------------
-- * Data type definition

type UnitTypes = [UnitType]

data UnitType =
      UTVar Int
    | UTCon String
    | UTInt Int
    | UTApp UnitType UnitType
deriving (Eq, Ord)

----------------------------------------------------------------------
-- * Common types

undimensioned :: UnitType
undimensioned = TCon "Undimensioned"

one :: UnitType
one = TCon "1"

times :: UnitType
times = TCon "*"

divide :: UnitType
times = TCon "/"

-- |For instance, @(listType intType)@ represents @[Int]@
listType :: UnitType -> UnitType
listType = UTApp (UTCon "[]")

----------------------------------------------------------------------
-- * Basic functionality


-- |Returns the right spine of a function type. For instance,
-- if type @t@ is @Int -> (Bool -> String)@, then @functionSpine t@
-- is @([Int,Bool],String)@.
functionSpine :: UnitType -> (UnitTypes,UnitType)
functionSpine = rec [] where
   rec tps (UTApp (UTApp (UTCon "->") t1) t2) = rec (t1:tps) t2
   rec tps tp                                 = (reverse tps,tp)

arityOfUnitType :: UnitType -> Int
arityOfUnitType = length . fst . functionSpine

-- |The priority of a type, primarily used for the insertion of parentheses 
-- in pretty printing.
priorityOfType :: UnitType -> Int
priorityOfType tp = case leftSpine tp of
       (TCon "->",[_,_]  ) -> 0
       (TCon "*",[_,_]  ) -> 2
       (TCon "/",[_,_]  ) -> 3
       (TCon "^",[_,_]  ) -> 4
       (_        ,[]     ) -> 4
       (TCon "[]",[_]    ) -> 2
       (TCon s   ,_      ) | isTupleConstructor s -> 2
       _                   -> 1

----------------------------------------------------------------------
-- * Predicates on types


isTupleConstructor :: String -> Bool
isTupleConstructor ('(':[]) = False
isTupleConstructor ('(':cs) = all (','==) (init cs) && last cs == ')'
isTupleConstructor _        = False

----------------------------------------------------------------------
-- * Show and Read instances

instance Show UTp where
   -- parenthesis are needed when the type must be shown as a part of 
   -- some other data type
   showsPrec prio theType rest = 
      parIf (prio > 0) (showTp theType) ++ rest
   
    where
      showTp tp = 
         case leftSpine tp of
            (UTCon "->",[t1,t2]) -> rec (<1) t1 ++ " -> " ++ rec (const False) t2
            (UTCon "*",[t1,t2]) -> rec (const False) t1 ++ " * " ++ rec (const False) t2
            (UTCon "/",[t1,t2]) -> rec (<4) t1 ++ " / " ++ rec (const False) t2
            (UTCon "^",[t1,t2]) -> rec (<5) t1 ++ " ^ " ++ rec (const False) t2

            (UTInt n   ,[]     ) -> 'n' : show n
            (UTVar i   ,[]     ) -> 'v' : show i
            (UTCon s   ,[]     ) -> s
            (UTCon "[]",[t1]   ) -> "[" ++ rec (const False) t1 ++ "]"
            (UTCon s   ,ts     ) | isTupleConstructor s -> let ts'  = map (rec (const False)) ts
                                                              f [] = ""
                                                              f xs = foldr1 (\x y -> x++", "++y) xs
                                                          in "(" ++ f ts' ++ ")"
            (t,ts) -> unwords (map (rec (<2)) (t:ts))
      
      rec p t = parIf (p (priorityOfType t)) (showTp t) 
      parIf True  s = "("++s++")"
      parIf False s = s