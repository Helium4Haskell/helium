-----------------------------------------------------------------------------
-- Standard Library: List operations
--
-- Suitable for use with Helium
-----------------------------------------------------------------------------

module List where

import Maybe

find                    :: (a -> Bool) -> [a] -> Maybe a
find p                   = listToMaybe . filter p

findIndex               :: (a -> Bool) -> [a] -> Maybe Int
findIndex p              = listToMaybe . findIndices p

findIndices             :: (a -> Bool) -> [a] -> [Int]
findIndices p xs         = [ i | (x,i) <- zip xs [0..], p x ]

nubBy           :: (a -> a -> Bool) -> [a] -> [a]
nubBy _  []              = []
nubBy eq (x:xs)          = x : nubBy eq (filter (\y -> not (eq x y)) xs)

deleteBy                :: (a -> a -> Bool) -> a -> [a] -> [a]
deleteBy _  _ []         = []
deleteBy eq x (y:ys)     = if x `eq` y then ys else y : deleteBy eq x ys

deleteFirstsBy          :: (a -> a -> Bool) -> [a] -> [a] -> [a]
deleteFirstsBy eq        = foldl (flip (deleteBy eq))

unionBy                 :: (a -> a -> Bool) -> [a] -> [a] -> [a]
unionBy eq xs ys         = xs ++ foldl (flip (deleteBy eq)) (nubBy eq ys) xs

intersectBy             :: (a -> a -> Bool) -> [a] -> [a] -> [a]
intersectBy eq xs ys     = [x | x <- xs, any (eq x) ys]

intersperse             :: a -> [a] -> [a]
intersperse _   []       = []
intersperse _   [x]      = [x]
intersperse sep (x:xs)   = x : sep : intersperse sep xs

transpose               :: [[a]] -> [[a]]
transpose []             = []
transpose ([] : xss)     = transpose xss
transpose ((x:xs) : xss) = (x : [h | (h:_) <- xss]) :
                           transpose (xs : [ t | (_:t) <- xss])

partition               :: (a -> Bool) -> [a] -> ([a],[a])
partition p xs           = foldr select ([],[]) xs
                 where select x (ts,fs) | p x       = (x:ts,fs)
                                | otherwise = (ts,x:fs)

-- groupBy splits its list argument into a list of lists of equal, adjacent
-- elements.  e.g.,
-- groupBy "Mississippi" == ["M","i","ss","i","ss","i","pp","i"]

groupBy                 :: (a -> a -> Bool) -> [a] -> [[a]]
groupBy _  []            = []
groupBy eq (x:xs)        = (x:ys) : groupBy eq zs
                           where (ys,zs) = span (eq x) xs

-- inits xs returns the list of initial segments of xs, shortest first.
-- e.g., inits "abc" == ["","a","ab","abc"]
inits                   :: [a] -> [[a]]
inits []                 = [[]]
inits (x:xs)             = [[]] ++ map (\ys -> x:ys) (inits xs)

-- tails xs returns the list of all final segments of xs, longest first.
-- e.g., tails "abc" == ["abc", "bc", "c",""]
tails                   :: [a] -> [[a]]
tails []                 = [[]]
tails xxs@(_:xs)         = xxs : tails xs

mapAccumL               :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccumL _ s []         = (s, [])
mapAccumL f s (x:xs)     = (s'',y:ys)
                         where (s', y ) = f s x
                               (s'',ys) = mapAccumL f s' xs

mapAccumR               :: (a -> b -> (a, c)) -> a -> [b] -> (a, [c])
mapAccumR _ s []         = (s, [])
mapAccumR f s (x:xs)     = (s'', y:ys)
                         where (s'',y ) = f s' x
                               (s', ys) = mapAccumR f s xs

unfoldr                 :: (b -> Maybe (a,b)) -> b -> [a]
unfoldr f b              = case f b of Nothing    -> []
                                       Just (a,c) -> a : unfoldr f c

sortBy          :: (a -> a -> Ordering) -> [a] -> [a]
sortBy cmp       = foldr (insertBy cmp) []

insertBy        :: (a -> a -> Ordering) -> a -> [a] -> [a]
insertBy _   x []    = [x]
insertBy cmp x ys@(y:ys')
             = case cmp x y of
                GT -> y : insertBy cmp x ys'
                _  -> x : ys

maximumBy               :: (a -> a -> Ordering) -> [a] -> a
maximumBy _   []        =  error "List.maximumBy: empty list"
maximumBy cmp xs        =  foldl1 maxBy xs
                where
                   maxBy x y = case cmp x y of
                        GT -> x
                        _  -> y
    
minimumBy               :: (a -> a -> Ordering) -> [a] -> a
minimumBy _   []        =  error "List.minimumBy: empty list"
minimumBy cmp xs        =  foldl1 minBy xs
                where
                   minBy x y = case cmp x y of
                        GT -> y
                        _  -> x

-----------------------------------------------------------------------------
