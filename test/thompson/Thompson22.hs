foo :: Int -> [Char] 
foo x = ['1'] ++ foo(x div 10) 
