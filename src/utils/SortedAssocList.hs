-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- SortedAssocList.hs : A sorted association list. Because the pairs are  
--    ordered by their keys, it is easy to determine the intersection of 
--    two association lists.
--
-- Future: should be replaced by a binary search tree.
--
-------------------------------------------------------------------------------

module SortedAssocList where

import List (partition, nub)

newtype Ord key => AssocList key elt = AssocList [(key,elt)]

-- standard functions
empty      :: Ord key => AssocList key elt
single     :: Ord key => key -> elt -> AssocList key elt
combine    :: Ord key => AssocList key elt -> AssocList key elt -> AssocList key elt
add        :: Ord key => key -> elt -> AssocList key elt -> AssocList key elt
remove     :: Ord key => key -> AssocList key elt -> AssocList key elt
removes    :: Ord key => [key] -> AssocList key elt -> AssocList key elt
toList     :: Ord key => AssocList key elt -> [(key,elt)]
fromList   :: Ord key => [(key,elt)] -> AssocList key elt
unsafeFromList :: Ord key => [(key,elt)] -> AssocList key elt
keys       :: Ord key => AssocList key elt -> [key]
elts       :: Ord key => AssocList key elt -> [elt]
mapElt     :: Ord key => (elt -> newelt) -> AssocList key elt -> AssocList key newelt
mapKey     :: (Ord key, Ord newKey) => (key -> newKey) -> AssocList key elt -> AssocList newKey elt
size       :: Ord key => AssocList key elt -> Int
lookupAL   :: Ord key => key -> AssocList key elt -> Maybe elt

-- specific functions
lookups    :: Ord key => key -> AssocList key elt -> ([elt],AssocList key elt)
lookups'   :: Ord key => key -> AssocList key elt -> ([(key,elt)],AssocList key elt)

lookups k (AssocList set) = let (set1,set2) = partition ((k==).fst) set
                            in (map snd set1,AssocList set2)
lookups' k (AssocList set) = let (as,set1) = span ((k/=).fst) set
                                 (bs,set2) = span ((k==).fst) set1
                             in (bs,AssocList (as++set2))





--nubAL      :: Ord key => AssocList key elt -> AssocList key elt
--nubALBy    :: Ord key => (key -> key -> Bool) -> AssocList key elt -> AssocList key elt
{-
nubAL = nubALBy (==)
nubALBy eq l =
    let
        rec []         list = list
        rec (key:keys) list =
            (\(elt:_,newList) -> add key elt (rec keys newList)) $
                lookupsBy eq key list
    in
        rec (nub (keys l)) l
-}
empty = AssocList []
single k e = add k e empty
--combine (AssocList set1) (AssocList set2) = AssocList (set1++set2)
--add k e (AssocList set) = AssocList ((k,e):set)
remove k (AssocList set) = AssocList (filter ((k/=).fst) set)
removes ks (AssocList set) = AssocList (filter ((`notElem` ks).fst) set)

lookupAL k (AssocList set) = lookup k set
toList (AssocList set) = set
fromList = foldr (uncurry add) empty
unsafeFromList = AssocList
keys (AssocList set) = map fst set
elts (AssocList set) = map snd set
mapElt f (AssocList set) = AssocList [ (key, f elt) | (key, elt) <- set ]

mapKey f (AssocList set) = AssocList [ (f key, elt) | (key, elt) <- set ]

add k e (AssocList set) = AssocList (rec set)
   where rec []     = [(k,e)]
         rec (x:xs) | fst x < k = x : rec xs
                    | otherwise = (k,e):x:xs
combine (AssocList set1) (AssocList set2) = AssocList (rec set1 set2)
   where rec [] set = set
         rec set [] = set
         rec (a:as) (b:bs) | fst a < fst b = a : rec as (b:bs)
                           | otherwise     = b : rec (a:as) bs
size (AssocList set) = length set


instance (Ord a,Show a,Show b) => Show (AssocList a b) where
   show (AssocList set1) = show set1
