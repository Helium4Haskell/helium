-- Ulf Norell, 24 september 2003
type Fun = Int -> Int

foo :: Fun
foo x = x

bar :: Int
bar = foo [3]
