-----------------------------------------------------------------------------
-- Standard Library: List operations
--
-- Suitable for use with Helium, derived from Hugs 98 Standard Library
-- Modifications:
--   * tuple constructors for zip functions 
--   * 'generic' functions for Integral type class are excluded
--   * list functions from Prelude are not exported by this module
-----------------------------------------------------------------------------

module List ( 
    elemIndex, elemIndices,
    find, findIndex, findIndices,
    nub, nubBy, delete, deleteBy, (\\), deleteFirstsBy,
    union, unionBy, intersect, intersectBy,
    intersperse, transpose, partition, group, groupBy,
    inits, tails, isPrefixOf, isSuffixOf,
    mapAccumL, mapAccumR,
    sort, sortBy, insert, insertBy, maximumBy, minimumBy,
    zip4, zip5, zip6, zip7,
    zipWith4, zipWith5, zipWith6, zipWith7,
    unzip4, unzip5, unzip6, unzip7, unfoldr
    ) where

import Maybe( listToMaybe )

infix 5 \\

elemIndex               :: Eq a => a -> [a] -> Maybe Int
elemIndex x              = findIndex (x ==)
        
elemIndices             :: Eq a => a -> [a] -> [Int]
elemIndices x            = findIndices (x ==)
                
find                    :: (a -> Bool) -> [a] -> Maybe a
find p                   = listToMaybe . filter p

findIndex               :: (a -> Bool) -> [a] -> Maybe Int
findIndex p              = listToMaybe . findIndices p

findIndices             :: (a -> Bool) -> [a] -> [Int]
findIndices p xs         = [ i | (x,i) <- zip xs [0..], p x ]

nub                     :: (Eq a) => [a] -> [a]
nub                      = nubBy (==)

nubBy                   :: (a -> a -> Bool) -> [a] -> [a]
nubBy eq []              = []
nubBy eq (x:xs)          = x : nubBy eq (filter (\y -> not (eq x y)) xs)

delete                  :: (Eq a) => a -> [a] -> [a]
delete                   = deleteBy (==)

deleteBy                :: (a -> a -> Bool) -> a -> [a] -> [a]
deleteBy eq x []         = []
deleteBy eq x (y:ys)     = if x `eq` y then ys else y : deleteBy eq x ys

(\\)                    :: (Eq a) => [a] -> [a] -> [a]
(\\)                     = foldl (flip delete)

deleteFirstsBy          :: (a -> a -> Bool) -> [a] -> [a] -> [a]
deleteFirstsBy eq        = foldl (flip (deleteBy eq))

union                   :: (Eq a) => [a] -> [a] -> [a]
union                    = unionBy (==)    

unionBy                 :: (a -> a -> Bool) -> [a] -> [a] -> [a]
unionBy eq xs ys         = xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

intersect               :: (Eq a) => [a] -> [a] -> [a]
intersect                = intersectBy (==)

intersectBy             :: (a -> a -> Bool) -> [a] -> [a] -> [a]
intersectBy eq xs ys     = [x | x <- xs, any (eq x) ys]

intersperse             :: a -> [a] -> [a]
intersperse sep []       = []
intersperse sep [x]      = [x]
intersperse sep (x:xs)   = x : sep : intersperse sep xs

transpose               :: [[a]] -> [[a]]
transpose []             = []
transpose ([] : xss)     = transpose xss
transpose ((x:xs) : xss) = (x : [h | (h:t) <- xss]) :
                           transpose (xs : [ t | (h:t) <- xss])

partition               :: (a -> Bool) -> [a] -> ([a],[a])
partition p xs           = foldr select ([],[]) xs
                 where select x (ts,fs) | p x       = (x:ts,fs)
                                  | otherwise = (ts,x:fs)

-- group splits its list argument into a list of lists of equal, adjacent
-- elements.  e.g.,
-- group "Mississippi" == ["M","i","ss","i","ss","i","pp","i"]
group                   :: (Eq a) => [a] -> [[a]]
group                    = groupBy (==)

groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy eq []            = []
groupBy eq (x:xs)        = (x:ys) : groupBy eq zs
                           where (ys,zs) = span (eq x) xs

-- inits xs returns the list of initial segments of xs, shortest first.
-- e.g., inits "abc" == ["","a","ab","abc"]
inits                   :: [a] -> [[a]]
inits []                 = [[]]
inits (x:xs)             = [[]] ++ map (x:) (inits xs)

-- tails xs returns the list of all final segments of xs, longest first.
-- e.g., tails "abc" == ["abc", "bc", "c",""]
tails                   :: [a] -> [[a]]
tails []                 = [[]]
tails xxs@(_:xs)         = xxs : tails xs

isPrefixOf              :: (Eq a) => [a] -> [a] -> Bool
isPrefixOf [] _          = True
isPrefixOf _  []         = False
isPrefixOf (x:xs) (y:ys) = x == y && isPrefixOf xs ys

isSuffixOf              :: (Eq a) => [a] -> [a] -> Bool
isSuffixOf x y           = reverse x `isPrefixOf` reverse y

mapAccumL               :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccumL f s []         = (s, [])
mapAccumL f s (x:xs)     = (s'',y:ys)
                         where (s', y ) = f s x
                               (s'',ys) = mapAccumL f s' xs

mapAccumR               :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccumR f s []         = (s, [])
mapAccumR f s (x:xs)     = (s'', y:ys)
                         where (s'',y ) = f s' x
                               (s', ys) = mapAccumR f s xs

unfoldr                 :: (b -> Maybe (a,b)) -> b -> [a]
unfoldr f b              = case f b of Nothing    -> []
                                       Just (a,b) -> a : unfoldr f b

sort            :: (Ord a) => [a] -> [a]
sort             = sortBy compare

sortBy            :: (a -> a -> Ordering) -> [a] -> [a]
sortBy cmp         = foldr (insertBy cmp) []

insert                  :: (Ord a) => a -> [a] -> [a]
insert                   = insertBy compare

insertBy        :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertBy cmp x []     = [x]
insertBy cmp x ys@(y:ys')
             = case cmp x y of
                GT -> y : insertBy cmp x ys'
                _  -> x : ys

maximumBy               :: (a -> a -> Ordering) -> [a] -> a
maximumBy cmp []        =  error "List.maximumBy: empty list"
maximumBy cmp xs        =  foldl1 max xs
                where
                   max x y = case cmp x y of
                        GT -> x
                        _  -> y
    
minimumBy               :: (a -> a -> Ordering) -> [a] -> a
minimumBy cmp []        =  error "List.minimumBy: empty list"
minimumBy cmp xs        =  foldl1 min xs
                where
                   min x y = case cmp x y of
                        GT -> y
                        _  -> x
 
zip4            :: [a] -> [b] -> [c] -> [d] -> [(a,b,c,d)]
zip4             = zipWith4 (\a b c d -> (a, b, c, d))

zip5            :: [a] -> [b] -> [c] -> [d] -> [e] -> [(a,b,c,d,e)]
zip5             = zipWith5 (\a b c d e -> (a, b, c, d, e))

zip6            :: [a] -> [b] -> [c] -> [d] -> [e] -> [f] -> 
                              [(a,b,c,d,e,f)]
zip6             = zipWith6 (\a b c d e f -> (a, b, c, d, e, f))

zip7            :: [a] -> [b] -> [c] -> [d] -> [e] -> [f] ->
                              [g] -> [(a,b,c,d,e,f,g)]
zip7             = zipWith7 (\a b c d e f g -> (a, b, c, d, e, f, g))

zipWith4        :: (a->b->c->d->e) -> [a]->[b]->[c]->[d]->[e]
zipWith4 z (a:as) (b:bs) (c:cs) (d:ds)
             = z a b c d : zipWith4 z as bs cs ds
zipWith4 _ _ _ _ _     = []

zipWith5        :: (a->b->c->d->e->f) -> 
                           [a]->[b]->[c]->[d]->[e]->[f]
zipWith5 z (a:as) (b:bs) (c:cs) (d:ds) (e:es)
             = z a b c d e : zipWith5 z as bs cs ds es
zipWith5 _ _ _ _ _ _     = []

zipWith6        :: (a->b->c->d->e->f->g) ->
                           [a]->[b]->[c]->[d]->[e]->[f]->[g]
zipWith6 z (a:as) (b:bs) (c:cs) (d:ds) (e:es) (f:fs)
             = z a b c d e f : zipWith6 z as bs cs ds es fs
zipWith6 _ _ _ _ _ _ _     = []

zipWith7        :: (a->b->c->d->e->f->g->h) ->
                           [a]->[b]->[c]->[d]->[e]->[f]->[g]->[h]
zipWith7 z (a:as) (b:bs) (c:cs) (d:ds) (e:es) (f:fs) (g:gs)
           =  z a b c d e f g : zipWith7 z as bs cs ds es fs gs
zipWith7 _ _ _ _ _ _ _ _ = []

unzip4            :: [(a,b,c,d)] -> ([a],[b],[c],[d])
unzip4             = foldr (\(a,b,c,d) ~(as,bs,cs,ds) ->
                    (a:as,b:bs,c:cs,d:ds))
                 ([],[],[],[])

unzip5            :: [(a,b,c,d,e)] -> ([a],[b],[c],[d],[e])
unzip5             = foldr (\(a,b,c,d,e) ~(as,bs,cs,ds,es) ->
                    (a:as,b:bs,c:cs,d:ds,e:es))
                 ([],[],[],[],[])

unzip6            :: [(a,b,c,d,e,f)] -> ([a],[b],[c],[d],[e],[f])
unzip6             = foldr (\(a,b,c,d,e,f) ~(as,bs,cs,ds,es,fs) ->
                    (a:as,b:bs,c:cs,d:ds,e:es,f:fs))
                 ([],[],[],[],[],[])

unzip7        :: [(a,b,c,d,e,f,g)] -> ([a],[b],[c],[d],[e],[f],[g])
unzip7        =  foldr (\(a,b,c,d,e,f,g) ~(as,bs,cs,ds,es,fs,gs) ->
                (a:as,b:bs,c:cs,d:ds,e:es,f:fs,g:gs))
             ([],[],[],[],[],[],[])

-----------------------------------------------------------------------------
