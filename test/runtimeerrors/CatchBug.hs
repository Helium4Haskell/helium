main = catch (do { [x] <- return [1, 2, 3]; return () }) 
             (\err -> putStr "Something is wrong")
             