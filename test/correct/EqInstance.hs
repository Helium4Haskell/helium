data A a = A Int a
         | B Char
    deriving Eq

data MyList a = Cons a (MyList a) | Nil
    deriving Eq
    
main =
    ( A 3 4 == B 'a'
    , A 3 4 == A 3 4
    , Cons 3 Nil == Nil
    , Cons 4 (Cons 5 Nil) == Cons 4 (Cons 5 Nil)
    , Cons 4 (Cons 6 Nil) == Cons 4 (Cons 5 Nil)
    )