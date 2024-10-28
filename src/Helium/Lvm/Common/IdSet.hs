--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

-- this module is exotic, only used by the core compiler
-- but it works with any IdMap
module Helium.Lvm.Common.IdSet
   ( IdSet, Id
   , emptySet, singleSet, elemSet, filterSet, foldSet
   , insertSet, deleteSet, unionSet, unionSets, intersectionSet, diffSet
   , listFromSet, setFromList, sizeSet, isEmptySet
   ) where

import Data.IntSet (IntSet)
import Data.List (sort)
import Helium.Lvm.Common.Id
import qualified Data.IntSet as IntSet
import Data.Semigroup as Sem

-- | An efficient set of 'Id's
newtype IdSet = IdSet IntSet

instance Show IdSet where
  showsPrec n a = showParen (n >= 11) (showString "IdSet.setFromList " . showsPrec 11 (listFromSet a))

instance Sem.Semigroup IdSet where
  (<>) = unionSet

instance Monoid IdSet where
  mempty  = emptySet
  mappend = (<>)
  mconcat = unionSets

emptySet :: IdSet
emptySet = IdSet IntSet.empty

singleSet :: Id -> IdSet
singleSet = IdSet . IntSet.singleton . intFromId

elemSet :: Id -> IdSet -> Bool
elemSet x (IdSet s) = IntSet.member (intFromId x) s

filterSet :: (Id -> Bool) -> IdSet -> IdSet
filterSet p (IdSet s) = IdSet (IntSet.filter (p . idFromInt) s)

foldSet :: (Id -> a ->  a) -> a -> IdSet -> a
foldSet f a (IdSet s) = IntSet.fold (f . idFromInt) a s

insertSet :: Id -> IdSet -> IdSet
insertSet x (IdSet s) = IdSet (IntSet.insert (intFromId x) s)

deleteSet :: Id -> IdSet -> IdSet
deleteSet x (IdSet s) = IdSet (IntSet.delete (intFromId x) s)

unionSet :: IdSet -> IdSet -> IdSet
unionSet (IdSet s1) (IdSet s2) = IdSet (s1 `IntSet.union` s2)

unionSets :: [IdSet] -> IdSet
unionSets xs = IdSet (IntSet.unions [ s | IdSet s <- xs ])

intersectionSet :: IdSet -> IdSet -> IdSet
intersectionSet (IdSet s1) (IdSet s2) = IdSet (s1 `IntSet.intersection` s2)

diffSet :: IdSet -> IdSet -> IdSet
diffSet (IdSet s1) (IdSet s2) = IdSet (IntSet.difference s1 s2)

-- sort is needed to not rely on an id's index
listFromSet :: IdSet -> [Id]
listFromSet (IdSet s) = sort [ idFromInt n | n <- IntSet.elems s ]

setFromList :: [Id] -> IdSet
setFromList = foldr insertSet emptySet

sizeSet :: IdSet -> Int
sizeSet (IdSet s) = IntSet.size s

isEmptySet :: IdSet -> Bool
isEmptySet (IdSet s) = IntSet.null s
