module Constraints where

type    Constraints s = [Constraint s]
newtype Constraint  s = Constraint (s (), s Bool, String)

class Monad s => SolvableConstraint c s where 
   solveConstraint :: c -> s ()

   checkConstraint :: c -> s Bool
   checkConstraint _ = return True
   
instance Show (Constraint s) where 
   show (Constraint (_, _, s)) = s

instance Monad s => SolvableConstraint (Constraint s) s where 
   solveConstraint (Constraint (f, _, _)) = f
   checkConstraint (Constraint (_, f, _)) = f

liftConstraint :: (SolvableConstraint c s, Show c) => c -> Constraint s
liftConstraint c = 
   Constraint (solveConstraint c, checkConstraint c, show c)

liftConstraints :: (SolvableConstraint c s, Show c) => [c] -> Constraints s
liftConstraints = map liftConstraint
