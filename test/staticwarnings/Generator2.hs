
main :: IO ()
main = do (True, _) <- return (True, True)
          return ()
