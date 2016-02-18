-- Fixity declarations cannot be inside an instance scope

instance W Char where
  infixr 5 ++
  