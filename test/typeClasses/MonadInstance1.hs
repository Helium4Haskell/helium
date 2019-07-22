

main = do
        x <- return 3
        y <- Just "Hello"
        let z = True
        return (x, y, z)