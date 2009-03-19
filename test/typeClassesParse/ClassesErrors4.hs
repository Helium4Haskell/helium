class PrimaClass a where
  identity :: a -> a

instance PrimaClass Int where
  identity :: Int -> Int
  identity = id

  
