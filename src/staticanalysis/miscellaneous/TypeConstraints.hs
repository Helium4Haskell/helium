{-# OPTIONS -fallow-undecidable-instances #-}
{-| Module      :  TypeConstraints
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    The type constraints used by the Helium compiler (all derived from the
	basic constraints that are supplied by the Top framework). Some constraints
	are lifted to work on finite maps as well.
-}

module TypeConstraints where

import Top.Constraints.Constraints
import Top.Constraints.Equality hiding ((.==.))
import Top.Constraints.ExtraConstraints hiding ((.::.))
import Top.Constraints.TypeConstraintInfo
import Top.States.BasicState
import Top.States.TIState
import Top.States.SubstState
import Top.States.QualifierState
import Top.Qualifiers.TypeClasses ()
import Top.Types
import Data.FiniteMap
import Top.Solvers.SolveConstraints

type TypeConstraints info = [TypeConstraint info]
data TypeConstraint  info
   = TC1 (EqualityConstraint info)
   | TC2 (ExtraConstraint Predicates info)
   | TCOper String (forall m . HasSubst m info => m ())

instance (HasBasic m info, HasTI m info, HasSubst m info, HasQual m Predicates info, PolyTypeConstraintInfo Predicates info) 
            => Solvable (TypeConstraint info) m where 
   solveConstraint (TC1 c)      = solveConstraint c
   solveConstraint (TC2 c)      = solveConstraint c
   solveConstraint (TCOper _ f) = f
   checkCondition  (TC1 c)      = checkCondition c
   checkCondition  (TC2 c)      = checkCondition c
   checkCondition  (TCOper _ _) = return True

instance Show info => Show (TypeConstraint info) where
   show (TC1 c)      = show c
   show (TC2 c)      = show c
   show (TCOper s _) = s

instance Substitutable (TypeConstraint info) where
   sub |-> (TC1 c) = TC1 (sub |-> c)
   sub |-> (TC2 c) = TC2 (sub |-> c)
   sub |-> tc     = tc
   ftv (TC1 c)    = ftv c
   ftv (TC2 c)    = ftv c
   ftv _          = []

------------

spreadFunction :: TypeConstraint info -> Maybe Int 
spreadFunction tc =
   case tc of
      TC1 (Equality t1 t2 info)       -> spreadFromType t2
      TC2 (Instantiate tp ts info)    -> spreadFromType tp
      TC2 (Implicit t1 (ms, t2) info) -> spreadFromType t1
      _                               -> Nothing

spreadFromType :: Tp -> Maybe Int
spreadFromType (TVar i) = Just i
spreadFromType _        = Nothing

dependencyTypeConstraint :: Substitution s => TypeConstraint info -> s -> Predicates -> TypeConstraint info
dependencyTypeConstraint constraint sub preds =
   case constraint of
      TC2 (Implicit t1 (ms, t2) info)
         -> let ms' = sub |-> ms
                t2' = sub |-> t2
                ts  = makeScheme (ftv ms') preds t2'
            in TC2 (Instantiate t1 (SigmaScheme ts) info)
      _  -> constraint

------------------------------------------------------------------------------
-- Lifted constructors

infix 3 .==., .===., .::., .:::., !:::!, .<=., .<==.
dummy = (voidType, voidType) -- !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!
lift combinator = 
    \as bs cf -> 
       let constraints = concat (eltsFM (intersectFM_C f as bs))
           rest        = delListFromFM bs (keysFM as)
           f a list    = [ (a `combinator` b) (cf name) | (name,b) <- list ]
       in (constraints, rest)
      
(.==.) :: Show info => Tp -> Tp -> ((Tp,Tp) -> info) -> TypeConstraint info
(t1 .==. t2) cinfo = TC1 (Equality t1 t2 info)
   where info = cinfo (t1, t2)
    
(.===.) :: (Show info, Ord key) => FiniteMap key Tp -> FiniteMap key [(key,Tp)] -> (key -> (Tp,Tp) -> info) -> ([TypeConstraint info],FiniteMap key [(key,Tp)])
(.===.) = lift (.==.)

(.::.) :: Show info => Tp -> TpScheme -> ((Tp,Tp) -> info) -> TypeConstraint info
(tp .::. ts) cinfo = TC2 (Instantiate tp (SigmaScheme ts) (cinfo dummy)) -- (setTypeScheme ts . cinfo, setReduction))

(.:::.) :: (Show info, Ord key) => FiniteMap key TpScheme -> FiniteMap key [(key,Tp)] -> (key -> (Tp,Tp) -> info) -> ([TypeConstraint info],FiniteMap key [(key,Tp)])  
(as .:::. bs) cinfo = lift (flip (.::.)) as bs cinfo

(!:::!) :: (Show info, Ord key) => FiniteMap key TpScheme -> FiniteMap key Tp -> (key -> (Tp,Tp) -> info) -> ([TypeConstraint info],FiniteMap key Tp)  
(as !:::! bs) cf = let bs' = mapFM (\name tp -> [(name,tp)]) bs
                       (xs,ys) = (as .:::. bs') cf                           
                       ys' = mapFM (\_ -> snd . head) ys
                   in (xs,ys')
                 
(.<=.) :: Show info => Tps -> Tp -> Tp -> ((Tp, Tp) -> info) -> TypeConstraint info
(.<=.) ms t1 t2 cinfo = TC2 (Implicit t1 (ms, t2) (cinfo dummy))

(.<==.) :: (Show info, Ord key) => Tps -> FiniteMap key Tp -> FiniteMap key [(key,Tp)] -> (key -> (Tp,Tp) -> info) -> ([TypeConstraint info],FiniteMap key [(key,Tp)])
(.<==.) ms as bs cinfo = lift (flip ((.<=.) ms)) as bs cinfo

predicate :: Predicate -> info -> TypeConstraint info
predicate p cinfo = TC2 (Prove [p] cinfo)