data Expr   = Num Int
            | Expr :+: Expr 
            | Expr :-: Expr
            | Expr :*: Expr
            deriving Show

fromNum :: Expr -> Int
fromNum (Num n) = n

eval :: Expr -> Int
eval (Num n) = n
eval (e1 :+: e2) = fromNum $ e1 + e2
eval (e1 :*: e2) = fromNum $ e1 * e2
eval (e1 :-: e2) = fromNum $ e1 - e2

instance Eq Expr where
    e1 == e2 = eval e1 == eval e2

instance Ord Expr where
    e1 < e2 = eval e1 < eval e2

instance Num Expr where
    fromInt n = Num n
    e1 + e2 = Num $ eval e1 + eval e2
    e1 * e2 = Num $ eval e1 * eval e2
    e1 - e2 = Num $ eval e1 - eval e2
    negate e1 = Num $ (- eval e1)

main = show ((Num 1 :+: Num 2 :*: Num 3) * (Num 2 :+: Num 5) - (Num 6))