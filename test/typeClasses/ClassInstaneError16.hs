class X a where
    f :: a -> Int

instance Y a => X (Maybe a) where
    f _ = 3