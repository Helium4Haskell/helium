module TypeConstraints where

import List (union)
import Types

data TypeConstraint info 
   = Equality         info Tp Tp                   
   | ExplicitInstance ((Tp,Tp) -> info) Tp TpScheme 
   | ImplicitInstance ((Tp,Tp) -> info) Tp Tps Tp   
   | MakeConsistent -- :-(

type TypeConstraints info = [TypeConstraint info]

------------------------------------------------------------------------------
-- Type Constraint Constructors

infix 3 .==.  , .::.  , .<=.

(.==.) ::        Tp -> Tp ->       ((Tp,Tp) -> a) -> TypeConstraint a
(.::.) ::        Tp -> TpScheme -> ((Tp,Tp) -> a) -> TypeConstraint a
(.<=.) :: Tps -> Tp -> Tp ->       ((Tp,Tp) -> a) -> TypeConstraint a

t1 .==. t2      = \cf -> Equality (cf (t1,t2)) t1 t2
tp .::. ts      = \cf -> ExplicitInstance cf tp ts
(.<=.) ms t1 t2 = \cf -> ImplicitInstance cf t1 ms t2

------------------------------------------------------------------------------
-- Instances for constraints 

instance Show info => Show (TypeConstraint info) where
   show typeConstraint = 
      case typeConstraint of
         Equality info t1 t2 -> 
            show t1 ++ " == "++show t2++" : "++show info
         ExplicitInstance info tp ts -> 
            let unknowns = (TCon "?", TCon "?")
            in show tp ++ " :: "++show ts++" : "++show (info unknowns)
         ImplicitInstance info t1 ms t2 ->
            let unknowns = (TCon "?", TCon "?")
                monos    = if null ms then "" else "monos="++show (ftv ms)++"; "
            in show t1 ++ " <= " ++ show t2 ++ " : " ++ monos ++ show (info unknowns)            
         MakeConsistent -> "<MakeConsistent>"

instance Functor TypeConstraint where 
   fmap function constraint = 
      case constraint of
         Equality a t1 t2            -> Equality (function a) t1 t2
         ExplicitInstance a tp tps   -> ExplicitInstance (function . a) tp tps
         ImplicitInstance a t1 ms t2 -> ImplicitInstance (function . a) t1 ms t2
         MakeConsistent              -> MakeConsistent
            
instance Substitutable (TypeConstraint info) where

   sub |-> constraint = case constraint of
                           Equality         info t1 t2       -> Equality info (sub |-> t1) (sub |-> t2)
                           ImplicitInstance info t1 monos t2 -> ImplicitInstance info (sub |-> t1) (sub |-> monos) (sub |-> t2)
                           ExplicitInstance info tp ts       -> ExplicitInstance info (sub |-> tp) (sub |-> ts)
                           MakeConsistent                    -> MakeConsistent
                           
   ftv constraint = case constraint of
                       Equality         info t1 t2       -> ftv t1 `union` ftv t2
                       ImplicitInstance info t1 monos t2 -> ftv t1 `union` ftv monos `union` ftv t2
                       ExplicitInstance info tp ts       -> ftv tp `union` ftv ts  
                       MakeConsistent                    -> []                              
