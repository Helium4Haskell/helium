
main = (*) <$> (Just 3 >>= (\x -> (return 5 >>= (\y -> return $ x + y)))) <*> pure 5