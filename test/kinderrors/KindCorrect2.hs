data Apply f a = Apply (f a)

type Compose f g a = f (g a)

type Flip f x y = f y x

data HFix f a = HIn (f (HFix f) a)

data Fix a = In (a (Fix a))

data Tree a = Node (Tree a) (Tree a) | Leaf a

type Parser symbol result  =  [symbol] -> [(result,[symbol])]

data RoseTree a = RoseTree a [RoseTree a]

data GRoseTree f a = GRoseTree a (f (GRoseTree f a))

type IOTree = GRoseTree IO
