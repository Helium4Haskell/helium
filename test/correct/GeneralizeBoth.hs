-- g1 and g2 should be assigned the same type class context.
--  (since they are part of the same binding group)

main = f True

f _ = let --g1 :: (Ord a, Show a) => a -> a -> String
          --g2 :: (Ord a, Show a) => a -> a -> String
          
          g1 x y = if x > y then show x else g2 x y
          g2 p q = g1 q p
      in g1 1 2
