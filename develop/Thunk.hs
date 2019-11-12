g x y = 0

--data P = P !Int !Int
--foo h = h 2 `P` h 3 -- + f 4

f = g 1

-- Fails:
main :: Int
-- main = f `seq` error (show (f 2))
main = error (seq f "a " ++ show (f 2) ++ " | " ++ show (f 3))

-- Ok:
{- main :: Int
main = bar (g 1)

bar h = h `seq` error (show (h 2) ++ " | " ++ show (h 3))
-}
