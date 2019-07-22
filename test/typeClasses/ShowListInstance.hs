data A = B Int

instance Show A where
    show (B n) = show n
    showList [] s = "[]" ++ s
    showList (x:xs) s = show x ++ show xs ++ s

main = show [B 3, B 5, B 7]