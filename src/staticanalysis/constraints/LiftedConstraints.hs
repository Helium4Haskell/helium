-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- LiftedConstraints.hs : Type constraints lifted to finite maps.
--
-------------------------------------------------------------------------------

module LiftedConstraints where

import Top.Constraints.Constraints
import Top.Constraints.EqualityConstraint hiding ((.==.))
import Top.Constraints.InstanceConstraint hiding ((.::.), (.<=.))
import Top.States.BasicState
import Top.States.TIState
import Top.States.SubstState
import Top.Types
import Data.FiniteMap
import Top.Solvers.SolveConstraints

type TypeConstraints info = [TypeConstraint info]
data TypeConstraint  info
   = TC_Eq   (EqualityConstraint  info)
   | TC_Inst (InstanceConstraint  info)
             
instance (HasBasic m info, HasTI m info, HasSubst m info, Show info) => Solvable (TypeConstraint info) m where 
   solveConstraint (TC_Eq c)   = solveConstraint c
   solveConstraint (TC_Inst c) = solveConstraint c
   checkCondition  (TC_Eq c)   = checkCondition c
   checkCondition  (TC_Inst c) = checkCondition c
   
instance Show info => Show (TypeConstraint info) where
   show (TC_Eq c)   = show c
   show (TC_Inst c) = show c
   
instance Substitutable (TypeConstraint info) where
   sub |-> (TC_Eq   c) = TC_Eq   (sub |-> c)
   sub |-> (TC_Inst c) = TC_Inst (sub |-> c)
   ftv (TC_Eq   c) = ftv c
   ftv (TC_Inst c) = ftv c
   
------------

spreadFunction :: TypeConstraint info -> Maybe Int 
spreadFunction tc =
   case tc of
      TC_Eq (Equality t1 t2 info)              -> spreadFromType t2
      TC_Inst (ExplicitInstance tp ts info)    -> spreadFromType tp
      TC_Inst (ImplicitInstance t1 ms t2 info) -> spreadFromType t1

spreadFromType :: Tp -> Maybe Int
spreadFromType (TVar i) = Just i
spreadFromType _        = Nothing

dependencyTypeConstraint :: Substitution s => TypeConstraint info -> s -> Predicates -> TypeConstraint info
dependencyTypeConstraint constraint sub preds =
   case constraint of
      TC_Inst (ImplicitInstance t1 ms t2 info)
         -> let ms' = sub |-> ms
                t2' = sub |-> t2
                ts  = generalize (ftv ms') preds t2'
            in TC_Inst (ExplicitInstance t1 ts info)
      _  -> constraint

------------------------------------------------------------------------------
-- Lifted constructors

infix 3 .==., .===., .::., .:::., !:::!, .<=., .<==.

lift combinator = 
    \as bs cf -> 
       let constraints = concat (eltsFM (intersectFM_C f as bs))
           rest        = delListFromFM bs (keysFM as)
           f a list    = [ (a `combinator` b) (cf name) | (name,b) <- list ]
       in (constraints, rest)
       
(.==.) :: Show info => Tp -> Tp -> ((Tp,Tp) -> info) -> TypeConstraint info
(t1 .==. t2) cinfo = TC_Eq (Equality t1 t2 info)
   where info = cinfo (t1, t2)
       
(.===.) :: (Show info, Ord key) => FiniteMap key Tp -> FiniteMap key [(key,Tp)] -> (key -> (Tp,Tp) -> info) -> ([TypeConstraint info],FiniteMap key [(key,Tp)])
(.===.) = lift (.==.)

(.::.) :: (Show info, SetReduction info, OriginalTypeScheme info) => Tp -> TpScheme -> ((Tp,Tp) -> info) -> TypeConstraint info
(tp .::. ts) cinfo = TC_Inst (ExplicitInstance tp ts (setTypeScheme ts . cinfo, setReduction))

(.:::.) :: (Show info, SetReduction info, Ord key, OriginalTypeScheme info) => FiniteMap key TpScheme -> FiniteMap key [(key,Tp)] -> (key -> (Tp,Tp) -> info) -> ([TypeConstraint info],FiniteMap key [(key,Tp)])  
(as .:::. bs) cinfo = lift (flip (.::.)) as bs cinfo

(!:::!) :: (Show info, SetReduction info, Ord key, OriginalTypeScheme info) => FiniteMap key TpScheme -> FiniteMap key Tp -> (key -> (Tp,Tp) -> info) -> ([TypeConstraint info],FiniteMap key Tp)  
(as !:::! bs) cf = let bs' = mapFM (\name tp -> [(name,tp)]) bs
                       (xs,ys) = (as .:::. bs') cf                           
                       ys' = mapFM (\_ -> snd . head) ys
                   in (xs,ys')
                   
(.<=.) :: (Show info, SetReduction info, OriginalTypeScheme info) => Tps -> Tp -> Tp -> ((Tp, Tp) -> info) -> TypeConstraint info
(.<=.) ms t1 t2 cinfo = TC_Inst (ImplicitInstance t1 ms t2 (cinfo, setReduction))

(.<==.) :: (Show info, SetReduction info, Ord key, OriginalTypeScheme info) => FiniteMap key Tp -> FiniteMap key Tp -> FiniteMap key [(key,Tp)] -> (key -> (Tp,Tp) -> info) -> ([TypeConstraint info],FiniteMap key [(key,Tp)])
(.<==.) ms as bs cinfo = lift (flip ((.<=.) (eltsFM ms))) as bs cinfo
                   
class SetReduction a where
   setReduction :: Predicate -> a -> a
   setReduction _ = id -- default

class OriginalTypeScheme a where
   setTypeScheme :: TpScheme -> a -> a
   setTypeScheme _ = id -- default
