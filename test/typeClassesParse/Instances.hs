class LegeClass a

instance LegeClass Int

class IdentityClass a where
     identiteit :: a -> a
     
instance IdentityClass Bool where
 identiteit a = a
     
     
class LegeClass a => MetContext a

instance MetContext Int

class IdentityMetDefault a where
      identity :: a -> a
      identity b = id b
      
instance IdentityMetDefault Char     
      
class ClassMetMeerdereMembers a where
      hallo :: a -> a
      hello :: a -> b -> a
      bonjour :: a -> (a -> a) -> a
      
instance ClassMetMeerdereMembers Bool where
   hallo a = a
   hello a = True
   bonjour a b = a
  
