module PMCFloat where


f a b c 
   | d < 0.0  = 0
   | d > 0.0  = 2
   | d == 0.0 = 1
   | otherwise = 3
 where d = sqrt (b * b - 4.0 * a * c)

main = f 3.0 5.0 8.0
