module Foreign where

-- type CInt = Int

newtype CInt = CInt Int

instance Show CInt where
    show (CInt i) = show i