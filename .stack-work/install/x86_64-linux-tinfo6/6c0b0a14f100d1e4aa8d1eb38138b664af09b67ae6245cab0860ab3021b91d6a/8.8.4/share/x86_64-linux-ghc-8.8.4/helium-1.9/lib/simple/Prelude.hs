{- The Simple (non-overloaded) Standard Prelude for the Helium Compiler -}

module Prelude where 

import PreludePrim

infixr 9  .
infixl 9  !!
infixr 8  ^, ^. -- , **.
-- infixl 7  *, *., `quot`, `rem`, `div`, `mod`, /., /         [PreludePrim]
-- infixl 6  +, -, +., -.                                      [PreludePrim]
infixr 5  ++
-- infixr 5 :                                                  [HeliumLang]
-- infix  4  ==, /=, <=, <, >, >=, ==., /=., <=., <., >., >=.  [PreludePrim]
infixr 3  &&
infixr 2  ||
infixr 0  $ --, $!                                             [PreludePrim]

{-----------------------------------------------
 -- Int
 -----------------------------------------------}

{- imported from PreludePrim

(+) :: Int -> Int -> Int
(-) :: Int -> Int -> Int
(*) :: Int -> Int -> Int

-}

-- for compatibility with Haskell textbooks
type Integer = Int

(/) :: Int -> Int -> Int
(/) = div

{- imported from PreludePrim

(<)    :: Int -> Int -> Bool
(<=)   :: Int -> Int -> Bool
(>)    :: Int -> Int -> Bool
(>=)   :: Int -> Int -> Bool
(==)   :: Int -> Int -> Bool
(/=)   :: Int -> Int -> Bool
rem    :: Int -> Int -> Int
div    :: Int -> Int -> Int
mod    :: Int -> Int -> Int
quot   :: Int -> Int -> Int
negate :: Int -> Int
-}

max :: Int -> Int -> Int
max x y = if x < y then y else x

min :: Int -> Int -> Int
min x y = if x < y then x else y

abs :: Int -> Int
abs x = if x < 0 then - x else x

absFloat :: Float -> Float
absFloat x = if x <. 0.0 then -. x else x

signum :: Int -> Int
signum x =
    case ordInt x 0 of
        LT -> -1
        EQ ->  0
        GT ->  1

even :: Int -> Bool
even n = n `rem` 2 == 0

odd :: Int -> Bool
odd  n = not (even n)

subtract :: Int -> Int -> Int
subtract a b = b - a

gcd :: Int -> Int -> Int
gcd 0 0 = error "Prelude.gcd: gcd 0 0 is undefined"
gcd x y = gcd' (abs x) (abs y)
   where gcd' :: Int -> Int -> Int
         gcd' x' 0  = x'
         gcd' x' y' = gcd' y' (x' `rem` y')

lcm :: Int -> Int -> Int
lcm _ 0 = 0
lcm 0 _ = 0
lcm x y = abs ((x `quot` gcd x y) * y)

(^) :: Int -> Int -> Int
_ ^ 0           = 1
i ^ n  | n > 0  = f i (n-1) i
       | otherwise = error "Prelude.^: negative exponent"
          where f :: Int -> Int -> Int -> Int
                f _ 0 y = y
                f x m y = g x m
                          where g :: Int -> Int -> Int
                                g x' m' | even m'    = g (x' * x') (m' `quot` 2)
                                        | otherwise  = f x' (m' - 1) (x' * y)

{-----------------------------------------------
 -- Float
 -----------------------------------------------}

{- imported from PreludePrim

(+.) :: Float -> Float -> Float
(-.) :: Float -> Float -> Float
(*.) :: Float -> Float -> Float
(/.) :: Float -> Float -> Float

(<.)  :: Float -> Float -> Bool
(<=.) :: Float -> Float -> Bool
(>.)  :: Float -> Float -> Bool
(>=.) :: Float -> Float -> Bool
(==.) :: Float -> Float -> Bool
(/=.) :: Float -> Float -> Bool

sqrt  :: Float -> Float
(**.) :: Float -> Float -> Float
exp   :: Float -> Float
log   :: Float -> Float
sin   :: Float -> Float
cos   :: Float -> Float
tan   :: Float -> Float
-}

signumFloat :: Float -> Int
signumFloat x =
    case ordFloat x 0.0 of
        LT -> -1
        EQ ->  0
        GT ->  1

(^.) :: Float -> Int -> Float
_ ^. 0           = 1.0
i ^. n  | n > 0  = f i (n-1) i
        | otherwise = error "Prelude.^.: negative exponent"
          where f :: Float -> Int -> Float -> Float
                f _ 0 y = y
                f x m y = g x m
                          where g :: Float -> Int -> Float
                                g x' m' | even m'    = g (x' *. x') (m' `quot` 2)
                                        | otherwise  = f x' (m' - 1) (x' *. y)

pi :: Float
pi = 3.141592653589793

{-----------------------------------------------
 -- Bool
 -----------------------------------------------}

not :: Bool -> Bool
not False = True
not _ = False

(||) :: Bool -> Bool -> Bool
(&&) :: Bool -> Bool -> Bool

x || y = if x then x else y
x && y = if x then y else x

otherwise :: Bool
otherwise = True

{-----------------------------------------------
 -- Maybe
 -----------------------------------------------}

data Maybe a
    = Nothing
    | Just a

maybe :: b -> (a -> b) -> Maybe a -> b
maybe e f m =
    case m of 
        Nothing -> e
        Just x  -> f x

{-----------------------------------------------
 -- Either
 -----------------------------------------------}

data Either a b = Left a | Right b

either :: (a -> c) -> (b -> c) -> Either a b -> c
either l r e =
    case e of 
        Left  x -> l x
        Right y -> r y

{-----------------------------------------------
 -- Ordering
 -----------------------------------------------}

data Ordering = LT | EQ | GT

{-----------------------------------------------
 -- Tuple
 -----------------------------------------------}

fst :: (a, b) -> a
fst (x, _) = x

snd :: (a, b) -> b
snd (_, x) = x

curry          :: ((a,b) -> c) -> (a -> b -> c)
curry f x y     = f (x,y)

uncurry        :: (a -> b -> c) -> ((a,b) -> c)
uncurry f p     = f (fst p) (snd p)

zip :: [a] -> [b] -> [(a,b)]
zip = zipWith  (\a b -> (a,b))

zip3 :: [a] -> [b] -> [c] -> [(a,b,c)]
zip3 = zipWith3 (\a b c -> (a,b,c))

zipWith :: (a -> b -> c) -> [a] -> [b] -> [c]
zipWith z (a:as) (b:bs)   = z a b : zipWith z as bs
zipWith _ _      _        = []

zipWith3 :: (a -> b -> c -> d) -> [a] -> [b] -> [c] -> [d]
zipWith3 z (a:as) (b:bs) (c:cs)
              = z a b c : zipWith3 z as bs cs
zipWith3 _ _ _ _          = []

unzip :: [(a,b)] -> ([a],[b])
unzip = foldr (\(a,b) (as,bs) -> (a:as, b:bs)) ([], [])

unzip3:: [(a,b,c)] -> ([a],[b],[c])
unzip3 = foldr (\(a,b,c) (as,bs,cs) -> (a:as,b:bs,c:cs)) ([],[],[])

{-----------------------------------------------
 -- List
 -----------------------------------------------}

 -- We can't import Char here because that would mean we couldn't import
-- it elsewhere. Therefore, we make local copies of the two functions 
-- from that module
localIsSpace :: Char -> Bool
localIsSpace c =
    i == ord ' '  || i == ord '\t' || i == ord '\n' ||
    i == ord '\r' || i == ord '\f' || i == ord '\v'
  where
    i = ord c

localIsDigit :: Char -> Bool
localIsDigit c = ord c >= ord '0' && ord c <= ord '9'


head :: [a] -> a
head (x:_) = x
head _ = error "Prelude.head: empty list"

last :: [a] -> a
last [x] = x
last (_:xs) = last xs
last _ = error "Prelude.last: empty list"

tail :: [a] -> [a]
tail (_:xs) = xs
tail _ = error "Prelude.tail: empty list"

init :: [a] -> [a]
init [_] = []
init (x:xs) = x : init xs
init _ = error "Prelude.init: empty list"

null :: [a] -> Bool
null [] = True
null _  = False

(++) :: [a] -> [a] -> [a]
(x:xs) ++ ys = x : (xs ++ ys)
[]     ++ ys = ys

map :: (a -> b) -> [a] -> [b]
map _ [] = []
map f (x:xs) = f x : map f xs

filter :: (a -> Bool) -> [a] -> [a]
filter p (x:xs) 
    | p x =  x : filter p xs 
    | otherwise = filter p xs
filter _ [] = []

{- 
Naive implementation of length (slow because of laziness)

length :: [a] -> Int
length [] = 0
length (_:xs) = 1 + length xs

Optimised implementation using strict foldl:
-}

length :: [a] -> Int
length xs = foldl' (\l _ -> l + 1) 0 xs

concat :: [[a]] -> [a]
concat = foldr (++) []

(!!) :: [a] -> Int -> a
xs !! n | n < 0     = error "Prelude.(!!): negative index"
        | null xs   = error "Prelude.(!!): index too large"
        | n == 0    = head xs
        | otherwise = tail xs !! (n - 1)

foldl :: (a -> b -> a) -> a -> [b] -> a
foldl _ z [] = z
foldl f z (x:xs) = foldl f (f z x) xs

foldl' :: (a -> b -> a) -> a -> [b] -> a
foldl' _ a [] = a
foldl' f a (x:xs) = (foldl' f $! f a x) xs

foldl1 :: (a -> a -> a) -> [a] -> a
foldl1 f (x:xs) = foldl f x xs
foldl1 _ [] = error "Prelude.foldl1: empty list"

scanl :: (a -> b -> a) -> a -> [b] -> [a]
scanl f q xxs =
    q
    :
    (case xxs of 
        x:xs -> scanl f (f q x) xs
        []   -> []
    )

scanl1           :: (a -> a -> a) -> [a] -> [a]
scanl1 _ []       = []
scanl1 f (x:xs)   = scanl f x xs

foldr :: (a -> b -> b) -> b -> [a] -> b
foldr _ z [] = z
foldr f z (x:xs) = x `f` (foldr f z xs)

foldr1           :: (a -> a -> a) -> [a] -> a
foldr1 _ [x]      = x
foldr1 f (x:xs)   = f x (foldr1 f xs)
foldr1 _ []       = error "Prelude.foldr1: empty list"

scanr            :: (a -> b -> b) -> b -> [a] -> [b]
scanr _ q0 []     = [q0]
scanr f q0 (x:xs) = 
    case scanr f q0 xs of
        qs@(q:_) -> f x q : qs
        _        -> error "Prelude.scanr"

scanr1           :: (a -> a -> a) -> [a] -> [a]
scanr1 _ []       = []
scanr1 _ [x]      = [x]
scanr1 f (x:xs)   = 
    case scanr1 f xs of
        qs@(q:_) -> f x q : qs
        _        -> error "Prelude.scanr"

iterate :: (a -> a) -> a -> [a]
iterate f x = x : iterate f (f x)

repeat :: a -> [a]
repeat x = xs where xs = x:xs

replicate :: Int -> a -> [a]
replicate n x = take n (repeat x)

cycle :: [a] -> [a]
cycle [] = error "Prelude.cycle: empty list"
cycle xs = xs' where xs'=xs++xs'

take :: Int -> [a] -> [a]
take n xs 
    | n <= 0   = []
    | otherwise = 
        case xs of 
            [] -> []
            (y:ys) -> y : take (n-1) ys

drop :: Int -> [a] -> [a]
drop n xs 
    | n <= 0 = xs
    | otherwise = 
        case xs of
            [] -> []
            (_:ys) -> drop (n-1) ys

splitAt :: Int -> [a] -> ([a], [a])
splitAt n xs 
    | n <= 0 = ([],xs)
    | otherwise = 
        case xs of 
            [] -> ([],[])
            (y:ys) -> (y:as,bs) where (as,bs) = splitAt (n-1) ys

takeWhile :: (a -> Bool) -> [a] -> [a]
takeWhile _ [] = []
takeWhile p (x:xs)
    | p x = x : takeWhile p xs 
    | otherwise = []

dropWhile :: (a -> Bool) -> [a] -> [a]
dropWhile _ [] = []
dropWhile p l@(x:xs)
    | p x = dropWhile p xs 
    | otherwise = l

span :: (a -> Bool) -> [a] -> ([a],[a])
span _ []            = ([],[])
span p xs@(x:xs')
     | p x       = (x:ys, zs)
     | otherwise = ([],xs)
                       where (ys,zs) = span p xs'

break :: (a -> Bool) -> [a] -> ([a],[a])
break p = span (not . p)

lines :: String -> [String]
lines ""   = []
lines s    = let l,s' :: String
                 (l,s') = break (\x -> x `eqChar` '\n') s
             in l : case s' of []      -> []
                               (_:s'') -> lines s''

words :: String -> [String]
words s =
    case dropWhile localIsSpace s of
        "" -> []
        s' -> w : words s''
              where w,s'' :: String
                    (w,s'') = break localIsSpace s'

unlines :: [String] -> String
unlines [] = []
unlines (l:ls) = l ++ '\n' : unlines ls

unwords :: [String] -> String
unwords [] = ""
unwords [w] = w
unwords (w:ws) = w ++ ' ' : unwords ws

reverse :: [a] -> [a]
reverse = foldl (flip (:)) []

and :: [Bool] -> Bool
and = foldr (&&) True

or :: [Bool] -> Bool
or = foldr (||) False

any :: (a -> Bool) -> [a] -> Bool
any p = or . map p

all :: (a -> Bool) -> [a] -> Bool
all p = and . map p

sum :: [Int] -> Int
sum = foldl' (+) 0

sumFloat :: [Float] -> Float
sumFloat = foldl' (+.) 0.0

product :: [Int] -> Int
product = foldl' (*) 1

maximum :: [Int] -> Int
maximum = foldl1 max

minimum :: [Int] -> Int
minimum = foldl1 min

concatMap :: (a -> [b]) -> [a] -> [b]
concatMap f = concat . map f

{-----------------------------------------------
 -- Char
 -----------------------------------------------

isSpace :: Char -> Bool
isSpace c =
    let
        i :: Int
        i = ord c
    in
        i == ord ' '  ||
        i == ord '\t' ||
        i == ord '\n' ||
        i == ord '\r' ||
        i == ord '\f' ||
        i == ord '\v'
        
isUpper :: Char -> Bool
isUpper c = ord c >= ord 'A' && ord c <= ord 'Z' 

isLower :: Char -> Bool
isLower c = ord c >= ord 'a' && ord c <= ord 'z'

isDigit :: Char -> Bool
isDigit c = ord c >= ord '0' && ord c <= ord '9'

isAlpha :: Char -> Bool
isAlpha c = isUpper c || isLower c

isAlphaNum :: Char -> Bool
isAlphaNum c =  isAlpha c || isDigit c

toUpper :: Char -> Char
toUpper c
    | isLower c = chr ( ord c - ord 'a' + ord 'A' )
    | otherwise = c

toLower :: Char -> Char
toLower c
    | isUpper c = chr ( ord c - ord 'A' + ord 'a' )
    | otherwise = c
 -}

    
{-----------------------------------------------
 -- Conversion
 -----------------------------------------------}

-- see also "read.." and "show.." below

{- imported from PreludePrim

ord :: Char -> Int
chr :: Int -> Char

intToFloat :: Int -> Float
round      :: Float -> Int
floor      :: Float -> Int
ceiling    :: Float -> Int
truncate   :: Float -> Int

-}

fromInt :: Int -> Float
fromInt = intToFloat

{-----------------------------------------------
 -- Some standard functions
 -----------------------------------------------}

fix :: (a -> a) -> a
fix f = x where x = f x 

id :: a -> a
id x = x

const :: a -> b -> a
const x _ = x

(.) :: (b -> c) -> (a -> b) -> (a -> c)
(.) f g x = f (g x)

flip :: (a -> b -> c) -> b -> a -> c
flip f x y = f y x

($) :: (a -> b) -> a -> b
f $ x = f x

{- imported from PreludePrim

seq :: a -> b -> b
($!) :: (a -> b) -> a -> b
error :: String -> a

-}

until :: (a -> Bool) -> (a -> a) -> a -> a
until p f x = if p x then x else until p f (f x)

undefined :: a
undefined = error "undefined"

{-----------------------------------------------
 -- IO
 -----------------------------------------------}

(>>=) :: IO a -> (a -> IO b) -> IO b
(>>=) io f = do x <- io
                f x

(>>) :: IO a -> IO b -> IO b
p >> q = p >>= \ _ -> q

{- imported from PreludePrim 
putChar :: Char -> IO ()
putChar c = primPutChar c

putStr :: String -> IO ()
putStr s = primPutStr s 

putStrLn :: String -> IO ()
putStrLn s = primPutStrLn s

unsafePerformIO :: IO a -> a 
unsafePerformIO = primUnsafePerformIO

return :: a -> IO a
-}

sequence :: [IO a] -> IO [a]
sequence [] = return []
sequence (c:cs) = do { x <- c; xs <- sequence cs; return (x:xs) }

sequence_ :: [IO a] -> IO ()
sequence_ = foldr (>>) (return ())

print :: (a -> String) -> a -> IO ()
print showElement e = putStrLn (showElement e)

getLine   :: IO String
getLine = do 
    c <- getChar
    if eqChar c '\n' 
        then return ""
        else do cs <- getLine
                return (c:cs)

writeFile :: String -> String -> IO ()
writeFile fname s
  = bracketIO (openFile fname WriteMode)
              (hClose)
              (\h -> hPutString h s)

readFile :: String -> IO String
readFile fname
  = bracketIO (openFile fname ReadMode)
              (hClose)
              (\h -> readAll h [])
  where
    readAll h acc 
      = do c  <- hGetChar h
           readAll h (c:acc) 
        `catchEof` (return (reverse acc))

bracketIO :: IO a -> (a -> IO b) -> (a -> IO c) -> IO c
bracketIO acquire release action
  = do x <- acquire
       finallyIO (action x) (release x)

finallyIO :: IO a -> IO b -> IO a
finallyIO io action
  = do x <- io `catch` (\exn -> do{ action; raise exn })
       action
       return x

{-----------------------------------------------
 -- HELIUM SPECIFIC
 -----------------------------------------------}

{-----------------------------------------------
 -- Eq
 -----------------------------------------------}

eqChar :: Char -> Char -> Bool
eqChar c1 c2 = 
    case ordChar c1 c2 of
        EQ -> True
        _  -> False

eqMaybe :: (a -> a -> Bool) -> Maybe a -> Maybe a -> Bool
eqMaybe _ Nothing Nothing = True
eqMaybe eq (Just a1) (Just a2) = a1 `eq` a2
eqMaybe _ _ _ = False

eqBool :: Bool -> Bool -> Bool
eqBool True True = True
eqBool False False = True
eqBool _ _ = False

eqList :: (a -> a -> Bool) -> [a] -> [a] -> Bool
eqList _      []     []     =  True
eqList eqElem (x:xs) (y:ys) = x `eqElem` y && eqList eqElem xs ys
eqList _      _      _      = False

eqTuple2 :: (a -> a -> Bool) -> (b -> b -> Bool) -> (a, b) -> (a, b) -> Bool
eqTuple2 eqA eqB (a1, b1) (a2, b2) = a1 `eqA` a2 && b1 `eqB` b2

eqString :: String -> String -> Bool
eqString s1 s2 = 
    case ordString s1 s2 of
        EQ -> True
        _  -> False

eqInt :: Int -> Int -> Bool
eqInt = (==)

eqFloat :: Float -> Float -> Bool
eqFloat = (==.)

{-----------------------------------------------
 -- Ord
 -----------------------------------------------}

ordString :: String -> String -> Ordering
ordString = ordList ordChar

ordChar :: Char -> Char -> Ordering
ordChar c1 c2 = ordInt (ord c1) (ord c2)

ordInt :: Int -> Int -> Ordering
ordInt x y 
    | x < y     = LT
    | x == y    = EQ
    | otherwise = GT
    
ordFloat :: Float -> Float -> Ordering
ordFloat x y 
    | x <. y    = LT
    | x ==. y   = EQ
    | otherwise = GT

ordList :: (a -> a -> Ordering) -> [a] -> [a] -> Ordering
ordList _ []     (_:_)  = LT
ordList _ []     []     = EQ
ordList _ (_:_)  []     = GT
ordList ordElem (x:xs) (y:ys) = 
    case ordElem x y of 
        GT -> GT
        LT -> LT
        EQ -> ordList ordElem xs ys

{-----------------------------------------------
 -- Show
 -----------------------------------------------}

{- Imported from HeliumLang:
    showFunction, showIO, showPolymorphic
    showChar, showString, showInt, showList, showBool, showUnit, showFloat  
    showTuple2, showTuple3, showTuple4, showTuple5, showTuple6, showTuple7
    showTuple8, showTuple9, showTuple10
-} 

{-----------------------------------------------
 -- Read
 -----------------------------------------------}

readInt :: String -> Int
readInt [] = 0
readInt ('-':s) = - readUnsigned s
readInt s = readUnsigned s

readUnsigned :: String -> Int
readUnsigned = 
    foldl (\a b -> a * 10 + b) 0
    .
    map (\c -> ord c - ord '0')
    .
    takeWhile localIsDigit

{-----------------------------------------------
 -- "Overloaded" functions
 -----------------------------------------------}

elemBy :: (a -> a -> Bool) -> a -> [a] -> Bool
elemBy _ _ [] = False
elemBy eq x (y:ys) 
  | x `eq` y = True
  | otherwise = elemBy eq x ys
  
notElemBy :: (a -> a -> Bool) -> a -> [a] -> Bool
notElemBy eq x ys = not (elemBy eq x ys)

lookupBy :: (a -> a -> Bool) -> a -> [(a,b)] -> Maybe b
lookupBy _ _ []       = Nothing
lookupBy eq k ((x,y):xys)
      | k `eq` x  = Just y
      | otherwise = lookupBy eq k xys  
      
