class LegeClass a

class IdentityClass a where
     identiteit :: a -> a
     
class LegeClass a => MetContext a

class IdentityMetDefault a where
      identity :: a -> a
      identity b = id b
      
class ClassMetMeerdereMembers a where
      hallo :: a -> a
      hello :: a -> b -> a
      bonjour :: a -> (a -> a) -> a
  
