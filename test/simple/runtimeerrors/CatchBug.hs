main = catch (do { [x] <- return [1, 2, 3]; return () }) 
             (\err -> putStrLn "The exception has been caught")
             