-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- Constraints.hs : Type constraints
--
-------------------------------------------------------------------------------

module Constraints where

import List                 ( union )
import Types

type Constraints a = [Constraint a]
data Constraint  a = Equiv        a Tp Tp                                          -- see (.==.)
                   | ExplInstance ((Tp,Tp) -> a, Predicate -> a) Tp TpScheme       -- see (.::.)
                   | ImplInstance ((Tp,Tp) -> a, Predicate -> a) Tp Tps Tp         -- see (.<=.)
                   | PredConstraint  a Predicate
                   | MakeConsistent

infix 3 .==.  , .::.  , .<=.

------------------------------------------------------------------------------
-- Type Constraint Constructors

(.==.) ::        Tp -> Tp ->       ((Tp,Tp) -> a) -> Constraint a
(.::.) ::        Tp -> TpScheme -> ((Tp,Tp) -> a) -> Constraint a
(.<=.) :: Tps -> Tp -> Tp ->       ((Tp,Tp) -> a) -> Constraint a

t1 .==. t2      = \cf -> Equiv (cf (t1,t2)) t1 t2
tp .::. ts      = \cf -> ExplInstance (cf,predicateError) tp ts
(.<=.) ms t1 t2 = \cf -> ImplInstance (cf,predicateError) t1 ms t2

predicateError :: Predicate -> a
predicateError p = error ("\nError for predicate:\n" ++ show p)

------------------------------------------------------------------------------
-- Apply a function to the constraint information

applyToConstraintInfo :: (a -> b) -> Constraint a -> Constraint b
applyToConstraintInfo function constraint =
   case constraint of
      Equiv a t1 t2                 -> Equiv (function a) t1 t2
      ExplInstance (f1,f2) tp tps   -> ExplInstance (function . f1, function . f2) tp tps
      ImplInstance (f1,f2) t1 ms t2 -> ImplInstance (function . f1, function . f2) t1 ms t2
      PredConstraint a p            -> PredConstraint (function a  ) p
      MakeConsistent                -> MakeConsistent

------------------------------------------------------------------------------
-- Instances for constraints 

instance Show a => Show (Constraint a) where  
   show constraint = let unknowns = (TCon "?", TCon "?")
                         brace s  = "   {"++s++"}"
                         pretty t | priorityOfType t == 2 = " "++show t
                                  | otherwise             = " ("++show t++")"  
                     in case constraint of   
                                         
      Equiv ci t1 t2               -> show t1 ++ " == " ++ show t2 ++ brace (show ci)
      ImplInstance (ci,_) t1 ns t2 -> show t1 ++ " <= " ++ show t2 ++ brace ("m="++show ns ++ ", " ++ show (ci unknowns))
      ExplInstance (ci,_) t1 t2    -> show t1 ++ " :: " ++ show t2 ++ brace (show (ci unknowns))
      PredConstraint ci p          -> show p                       ++ brace (show ci)
      MakeConsistent               -> "<MakeConsistent>"

instance Substitutable (Constraint info) where

   sub |-> constraint = case constraint of
                           Equiv        info t1 t2       -> Equiv info (sub |-> t1) (sub |-> t2)
                           ImplInstance info t1 monos t2 -> ImplInstance info (sub |-> t1) (sub |-> monos) (sub |-> t2)
                           ExplInstance info tp ts       -> ExplInstance info (sub |-> tp) (sub |-> ts)
                           PredConstraint info p         -> PredConstraint info (sub |-> p)
                           _                             -> constraint
                           
   ftv constraint = case constraint of
                       Equiv        info t1 t2       -> ftv t1 `union` ftv t2
                       ImplInstance info t1 monos t2 -> ftv t1 `union` ftv monos `union` ftv t2
                       ExplInstance info tp ts       -> ftv tp `union` ftv ts
                       PredConstraint info p         -> ftv p
                       _                             -> []
                     
