f :: Int -> Int -> Int
f = (+)

data C = C Int Int

-- test the pretty printing of the infix's in 
-- the three type errors!

test = True `f` 3

g (True `C` False) = 5

x :: Bool
(x `C` y) = C 3 5
