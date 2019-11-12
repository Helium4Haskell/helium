module Hoi where

-- import Fib

{-
data X = X
data Lorem = A | B | C | D X X X X X X X X X

-- const' a b = a
--id' x = x

foo :: MBool -> MBool
foo x@MTrue = x
foo x = x

-- main = foo MTrue
-- main = "Hello world! This is a very loooong string"
-}

--data Foo = Foo{-} | Bar Bool Bool-}
{-
id' x = x

const' a b = a

lorem = const' 1

-- lorem x = let Foo a = x in a

myconst x y = x

text = "hoi\n"

drie = 3
-}
fib :: Int -> Int
fib 0 = 1
fib 1 = 1
fib n = a `seq` b `seq` (a + b)
  where
	a = fib (n - 1)
	b = fib (n - 2)

testConst a b = const a b

hallo :: Int
hallo = b
  where
    a = (+b)
    b = a two

data A = A (Int ->  Bool)
data B a = B (a -> a) | C (B [a])

data DictEq a = DictEq (DictEq a -> a -> a -> Bool)

data Bin a = Node (Bin a) (Bin a) | Leaf a

data Rec = Rec (Rec, Rec) (Int, Bool)

{-
--fib n = fib1 n + fib2 n
{-
fib1 n = fib (n - 1)
fib2 n = fib (n - 2)
-}

fib' :: Int -> Int
fib' i = go 0 1 (i + 1)

go a b 0 = a
go a b 1 = b
go a b i = go b (a+b) (i-1)

bar = False

ipsum a b = b

echo :: IO a
echo = getChar >>= (\c -> putChar c) >>= (\_ -> echo)

data Hoi a b c = Hoi a b c deriving (Eq, Show)

barzz = Hoi 1

show2 = show



main :: IO Int
main = error $ show (Hoi 1 True "hi")
	-- seq (barzz True "yes") $ error $ show $ fib 16 -- return 24 >>= (\x -> return (x * 12))
	-- length (show True) -- length (show (fib 36)) -- error (show (fib 36)) --  length (tail (tail (showInt 2)))-- head (showInt 2)
	-- let a = length "abc" in let g = \x -> a + x in g 1
	
	-- error $ "Hello " ++ "World!" -- fib 36 -- error $ showInt 1
	
	-- fib 36
	-- fromEnum (head (tail (tail (showInt (42))))) -- 1 + 2 * 3
	
	--let a = 'x' : b; b = 'o' : a in error a
	
	-- 127 + 61 {-length x +-} {-length (tail x)-}
	-- head foo -- lorem bar -- 101
-- head $ tail "Abcdef" -- head (10 : undefined) -- length [9] -- MLeft HelloWorld
-- oo = [0]
-}
{-
main :: IO Int
main = error $ show $ fib 28
-}
{-
data Hopi a b c = Hopi a b c
main :: (Hopi Int) Integer String
main = Hopi 1 1 "a"-}
{-
echo2 :: IO a
echo2 = do
  c <- getChar
  let d = c
  putChar d
  echo2
 
type Hapy a b = a -> b -> a -> b

hapy :: Hapy Int Bool
hapy x y z = y
-}
-- hopiDict = "HopiDict\n"

myMain :: ()
myMain = unsafePerformIO (putChar 'a') -- (return 10 :: IO Int)
	-- apply (f2 two two) two
	-- error (show (fib 36))
	-- myLength [1]

two :: Int
two = 2

f1 :: Int -> Int -> Int
f1 = f2 two

f2 :: Int -> Int -> Int -> Int
f2 x = f3

f3 :: Int -> Int -> Int
f3 x y = x +# y


myLength :: [a] -> Int
myLength [] = 42
myLength (_:xs) = let y = myLength xs in (1 + y) 

myPlus :: Num a => a -> a -> a
myPlus x y = y --  `seq` x + x

testFn :: Int -> Int
testFn x = fakeStrict (foo x x)

foo :: Int -> Int -> Int
foo x = foo2 x

foo2 :: Int -> Int -> Int
foo2 x y = x +# y


apply :: (Int -> Int) -> Int -> Int
apply f x = fakeStrict (f x)

fakeStrict :: Int -> Int
fakeStrict f = if True then f else 0


main :: Int
main = error "hello"
	-- error (show (fib 35))
  where
		myConst :: Int -> Int -> Int
		myConst a = id
	-- unsafePerformIO (return 10) -- fib 36
	-- (error foo3) `seq` error "nope"
		
		{- case a of
		[] -> error "Nope"
		_ -> error a -}
		-- _ -> error "Nope"
	
	
	-- error (fooId True 'a') --exit (length (fooId True 'a')) `seq` return 1 -- error (safeShowChar True '\n')
	
test x = case x of
	'a' -> "Yup"
	_ -> "Nope"
	-- error (safeShowChar True '\n') -- (showInt (fib 10)) -- error (show (fib 16))
	-- exitBoth `seq` return 0
	-- hopiDict `seq` (hopiDict `seq` error "a")
	{- case ["hopi"] of
	(x:xs) -> error x
	_ -> error "b" -}

{-
foo x y = x + y

f = let g x = x + x in (g 1, g 1)
bar = let g x = x in (g 1, g 1)
-}
{-
f = let g y = y + 1 in h (g 2)

h x = x + x

k :: Num a => a -> a
k x = x + x

bar (t:ts) = t + bar ts
bar [] = 0

-- foo = map (\x -> x + 1) [1,3,4]

foo :: a -> ((a, Int), (a, Bool))
foo x = (baz 1, baz True)
	where
		baz y = (x, y)
{-
intId :: Int -> Int
intId x = x

lorem a b = (check a 1, check b True, id' a, id' b)

check :: a -> a
id' :: a -> a
(check, id') = (\x -> x, \z -> z)
-}

-- hopi = [even x | x <- [0..10]] ++ [1,2,3,4]

-- polyInComprehension = [(i "", i "") | let i x = x ]

minus x = x - 1
-}
data Foo = Foo !Int

strict = Foo (fib 10)

divides :: Int -> Int -> Bool
divides a b = mod b a == 0

checks :: [Bool]
checks =
  [ divides 2 2
  , divides 3 5
  ]
