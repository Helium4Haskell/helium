module PMC4 where

data MyList a = Cons a (MyList a) | Nil

main :: MyList Int
main = map2 (\x -> x + 1) (Cons 1 Nil)

map2 :: (a -> b) -> MyList a -> MyList b
map2 f Nil = Nil
map2 f (Cons x xs) = Cons (f x) (map2 f xs)
