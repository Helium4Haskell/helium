
f (x:xs) ks r | x == ks   = f xs ks r
              | otherwise = f x:xs ks r
f [] _ r = r  
-- Dit leidt tot loopende inferencer.
-- Weghalen van f [] _ r regel voorkomt het loopen.
-- Maar ook f naar twee argumenten omzetten lijkt het probleem te verhelpen.
-- Ook het weghalen van guardstructuur voorkomt loopen.
-- Loopen alleen als type graphs worden gebruikt, niet bij -M of -W bv.

--project :: [String] -> Table -> Table
--project x (t,k,r) = (t, x, project2 x k r [])
--                    where project2 (x:xs) (k:ks) r result | x==k = project2 xs   ks (colTail r) (colCons (colHead r) result)
--                                                          | x/=k = project2 x:xs ks (colTail r) result
--                         project2 [] _ _ result = result

