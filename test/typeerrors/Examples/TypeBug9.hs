module TypeBug9 where

infixl 6 <*>
infixl 7 <$>

type Parser symbol result = [symbol] -> [(result,[symbol])]

(<*>) :: Parser s (a -> b) -> Parser s a -> Parser s b
(<$>) :: (a -> b) -> Parser s a -> Parser s b

(<*>) = undefined
(<$>) = undefined

many     :: Parser s a -> Parser s [a]
many    = undefined

chainr :: Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainr pe po = h <$> many (j <$> pe <*> po) <*> pe
   where j x op = (x `op`)
         h fs x = foldr ($) fs x
