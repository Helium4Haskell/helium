module SimilarLiteral3 where

startsWithA :: String -> Bool
startsWithA s = case s of  
                  []      -> False
                  "A" : _ -> True
                  _       -> False
