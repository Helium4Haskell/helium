-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- LiftedConstraints.hs : Type constraints lifted to finite maps.
--
-------------------------------------------------------------------------------

module LiftedConstraints where

import TypeConstraints
import Types
import Data.FiniteMap

infix 3 .===. , .:::. , .<==. , !:::!

------------------------------------------------------------------------------
-- Lifted constructors

lift combinator = 
    \as bs cf -> 
       let constraints = concat (eltsFM (intersectFM_C f as bs))
           rest        = delListFromFM bs (keysFM as)
           f a list    = [ (a `combinator` b) (cf name) | (name,b) <- list ]
       in (constraints, rest)
    
(.===.) :: Ord key =>        FiniteMap key Tp       -> FiniteMap key [(key,Tp)] -> (key -> (Tp,Tp) -> info) -> (TypeConstraints info,FiniteMap key [(key,Tp)])
(.:::.) :: Ord key =>        FiniteMap key TpScheme -> FiniteMap key [(key,Tp)] -> (key -> (Tp,Tp) -> info) -> (TypeConstraints info,FiniteMap key [(key,Tp)])  
(.<==.) :: Ord key => Tps -> FiniteMap key Tp       -> FiniteMap key [(key,Tp)] -> (key -> (Tp,Tp) -> info) -> (TypeConstraints info,FiniteMap key [(key,Tp)])
(!:::!) :: Ord key =>        FiniteMap key TpScheme -> FiniteMap key Tp         -> (key -> (Tp,Tp) -> info) -> (TypeConstraints info,FiniteMap key Tp)  

(.===.)    = lift (.==.) 
(.:::.)    = lift (flip (.::.))
(.<==.) ms = lift (flip ((.<=.) ms))

(as !:::! bs) cf = let bs' = mapFM (\name tp -> [(name,tp)]) bs
                       (xs,ys) = (as .:::. bs') cf                           
                       ys' = mapFM (\_ -> snd . head) ys
                   in (xs,ys')
                   
variableInConstraint :: TypeConstraint info -> Maybe Int
variableInConstraint constraint = 
   case constraint of
      Equality _ _ (TVar i)           -> Just i
      ExplicitInstance _ (TVar i) _   -> Just i 
      ImplicitInstance _ (TVar i) _ _ -> Just i 
      _                               -> Nothing                   

dependencyTypeConstraint :: Substitution substitution => TypeConstraint a -> substitution -> Predicates -> TypeConstraint a
dependencyTypeConstraint constraint sub preds = 
   case constraint of
      ImplicitInstance info t1 ms t2 
         -> let ms' = sub |-> ms
                t2' = sub |-> t2
                ts  = generalize (ftv ms') preds t2'
            in (t1 .::. ts) info
      _  -> constraint
