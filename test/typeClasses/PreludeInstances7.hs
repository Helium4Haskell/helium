data Expr a = Num a
            | Expr a :+: Expr a
            | Expr a :-: Expr a
            | Expr a :*: Expr a
            deriving Show

fromNum :: Num a => Expr a -> a
fromNum (Num n) = n

eval :: Num a => Expr a -> a
eval (Num n) = n
eval (e1 :+: e2) = fromNum $ e1 + e2
eval (e1 :*: e2) = fromNum $ e1 * e2
eval (e1 :-: e2) = fromNum $ e1 - e2

instance Num a => Eq (Expr a) where
    e1 == e2 = eval e1 == eval e2

instance Num a => Ord (Expr a) where
    e1 < e2 = eval e1 < eval e2

instance Num a => Num (Expr a) where
    --fromInt n = Num (fromInt n)
    e1 + e2 = Num $ eval e1 + eval e2
    e1 * e2 = Num $ eval e1 * eval e2
    e1 - e2 = Num $ eval e1 - eval e2
    negate e1 = Num $ (- eval e1)

main = show ((Num 1 :+: Num 2 :*: Num 3) * (Num 2 :+: Num 5) - (Num 6))