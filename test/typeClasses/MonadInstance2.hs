
fail = Nothing

main = do
        x <- return 3
        y <- Just "Hello"
        fail
        let z = undefined
        return (x, y, z)