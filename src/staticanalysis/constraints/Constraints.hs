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
data Constraint  a = Equiv        a Tp Tp                          -- see (.==.)
                   | ExplInstance ((Tp,Tp) -> a) Tp TpScheme       -- see (.::.)
                   | ImplInstance ((Tp,Tp) -> a) Tp Tps Tp         -- see (.<=.)
                   | Predicate    a ClassPredicate
                   | MakeConsistent

infix 3 .==.  , .::.  , .<=.

------------------------------------------------------------------------------
-- Type Constraint Constructors

(.==.) ::        Tp -> Tp ->       ((Tp,Tp)      -> a) -> Constraint a
(.::.) ::        Tp -> TpScheme -> ((Tp,Tp)      -> a) -> Constraint a
(.<=.) :: Tps -> Tp -> Tp ->       ((Tp,Tp)      -> a) -> Constraint a

t1 .==. t2      = \cf -> Equiv (cf (t1,t2)) t1 t2
tp .::. ts      = \cf -> ExplInstance cf tp ts
(.<=.) ms t1 t2 = \cf -> ImplInstance cf t1 ms t2

------------------------------------------------------------------------------
-- Apply a function to the constraint information

applyToConstraintInfo :: (a -> b) -> Constraint a -> Constraint b
applyToConstraintInfo function constraint =
   case constraint of
      Equiv a t1 t2           -> Equiv (function a) t1 t2
      ExplInstance f tp tps   -> ExplInstance (function . f) tp tps
      ImplInstance f t1 ms t2 -> ImplInstance (function . f) t1 ms t2
      Predicate    a tuple    -> Predicate    (function a  ) tuple
      MakeConsistent          -> MakeConsistent

------------------------------------------------------------------------------
-- Instances for constraints 

instance Show a => Show (Constraint a) where  
   show constraint = let unknowns = (TCon "?", TCon "?")
                         brace s  = "   {"++s++"}"
                         pretty t | priorityOfType t == 2 = " "++show t
                                  | otherwise             = " ("++show t++")"  
                     in case constraint of   
                                         
      Equiv ci t1 t2           -> show t1 ++ " == " ++ show t2 ++ brace (show ci)
      ImplInstance ci t1 ns t2 -> show t1 ++ " <= " ++ show t2 ++ brace ("m="++show ns ++ ", " ++ show (ci unknowns))
      ExplInstance ci t1 t2    -> show t1 ++ " :: " ++ show t2 ++ brace (show (ci unknowns))
      Predicate    ci (s,tps)  -> s ++ concatMap pretty tps ++ brace (show ci)
      MakeConsistent           -> "<MakeConsistent>"

instance Substitutable (Constraint info) where

   sub |-> constraint = case constraint of
                           Equiv        info t1 t2       -> Equiv info (sub |-> t1) (sub |-> t2)
                           ImplInstance info t1 monos t2 -> ImplInstance info (sub |-> t1) (sub |-> monos) (sub |-> t2)
                           ExplInstance info tp ts       -> ExplInstance info (sub |-> tp) (sub |-> ts)
                           Predicate    info (s,tps)     -> Predicate    info (s,sub |-> tps)
                           _                             -> constraint
                           
   ftv constraint = case constraint of
                       Equiv        info t1 t2       -> ftv t1 `union` ftv t2
                       ImplInstance info t1 monos t2 -> ftv t1 `union` ftv monos `union` ftv t2
                       ExplInstance info tp ts       -> ftv tp `union` ftv ts
                       Predicate    info (s,tps)     -> ftv tps
                       _                             -> []
