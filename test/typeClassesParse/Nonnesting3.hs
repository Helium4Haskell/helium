-- Fixity declarations cannot be inside a class scope
-- The language report in fact says they can as long as they
-- are about operators defined in the class. Since these fixity
-- decls can also be at top-level, I have decided not to allow
-- them and keep things simple in a class.

class W a where
  infixr 5 ++
  
