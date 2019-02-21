data Expr a where
    I :: Int -> Expr Int
    B :: Bool -> Expr Bool
    Plus :: Num a => Expr a -> Expr a -> Expr a

eval :: Expr a -> a
eval (I i) = i
eval (B b) = b
eval (Plus x y) = eval x + eval y