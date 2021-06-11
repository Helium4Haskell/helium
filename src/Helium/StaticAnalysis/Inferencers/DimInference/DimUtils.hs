{-| Module      :  DimUtils
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

    Utilities to store unit types, strongly inspired from Top (UTp instead of Tp)
-}

module Helium.StaticAnalysis.Inferencers.DimInference.DimUtils where

data UTp a =
     UTApp (UTp a) (UTp a)
    | UTCon String
    | UTVar Int
    | Base a 
    | Undimensioned

(to) :: UTp -> UTp -> UTp
ut1 to ut2 = UTApp (UTApp (UTCon "->") ut1) ut2

listUType :: UTp a -> UTp A
listUType = UTApp (UTCon "[]")

tupleUType :: [UTp a] -> UTp a 
tupleUType utps = let name | null utps  = "()"
                           | otherwise = "("++replicate (length utps-1) ','++")"
                in foldl TApp (TCon name) tps


----------------------------------------------------------------------
-- * Basic functionality


-- |Returns the right spine of a function type. For instance,
-- if type @t@ is @Int -> (Bool -> String)@, then @functionSpine t@
-- is @([Int,Bool],String)@.
ufunctionSpine :: UTp a -> ([UTp a],UTp a)
ufunctionSpine = rec [] where
   rec utps (UTApp (UTApp (UTCon "->") ut1) ut2) = rec (ut1:tps) ut2
   rec utps utp                                 = (reverse utps,utp)

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

-- A representation of type schemes. 
-- A type scheme is a (qualified) type with a number of quantifiers (foralls) 
-- in front of it. A partial mapping from type variable (Int) to their name (String)
-- is preserved. 
type UTpScheme = Qualification UnitPredicates UTp
    -- list of quantified unit variables, finite map partially
    -- mapping those var to their original id and a qualified type

type NormUnitType = UTp NormUnit
type UnitType = UTp Unit

type UnitConstraints = [(UnitType Unit, UnitType Unit)]


type UnitPredicates = [UnitPredicate]
data UnitPredicate = UnitPredicate String UnitType deriving Eq

type UnitClassEnvironment = M.map String Class
type UnitClass = ([String], UnitInstances)
type UnitInstances = [UnitInstance]
type UnitInstance = (UnitPredicate, UnitPredicates)
