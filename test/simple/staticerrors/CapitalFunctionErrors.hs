X = 3 -- hint for "X"

Const x y = x -- hint for "Const"

data Exists = Exists Int Int
Exists a b = undefined -- correct!!!

data BlaBla = BlaBla Int Int
BlaBla = undefined -- incorrect, no hint

nee (Id) = undefined -- incorrect, but no hint

Exits c d = undefined -- two hints

gek = let Nee x y = undefined  -- hint for Nee
      in gek
