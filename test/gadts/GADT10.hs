data Expr a where
    I :: Int -> Expr Int
    B :: Bool -> Expr Bool
    Plus :: Num a => Expr a -> Expr a -> Expr a
    Equals :: Eq a => Expr a -> Expr a -> Expr Bool

eval :: Expr a -> a
eval (I i) = i
eval (B b) = b
eval (Plus x y) = eval x + eval y
eval (Equals x y) = eval x == eval y

-- 3 + 4 == 7
answer1 = eval (Equals (Plus (I 3) (I 4)) (I 7))