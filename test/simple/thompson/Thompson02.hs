data BTree a = EmptyBTree | Node a (BTree a) (BTree a)

card :: BTree a -> Int
card EmptyBTree = 0
card (Node x) lt rt = card lt + card rt
