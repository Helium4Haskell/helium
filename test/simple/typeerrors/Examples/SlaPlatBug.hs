slaPlat :: [[Int]]->[Int]
slaPlat lijst | length(lijst)==1 = lijst
                | length(lijst)==2 = take 1 lijst ++ take 2 lijst
              | otherwise = slaPlat((take 1 lijst ++ take 2 lijst) ++ tail nieuweLijst)
              where nieuweLijst = tail lijst
