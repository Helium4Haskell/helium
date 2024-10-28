{-# LANGUAGE FlexibleInstances, MultiParamTypeClasses #-}
-----------------------------------------------------------------------------
-- | License      :  GPL
-- 
--   Maintainer   :  helium@cs.uu.nl
--   Stability    :  provisional
--   Portability  :  non-portable (requires extensions)
--
-- Constraints for overloading
--
-----------------------------------------------------------------------------


module Helium.Top.Top.Constraint.Qualifier where

import Helium.Top.Top.Types
import Helium.Top.Top.Constraint
import Helium.Top.Top.Constraint.Information
import Helium.Top.Top.Interface.Qualification
import Data.List

data ExtraConstraint info 
   = Prove Predicate info
   | Assume Predicate info

instance Show info => Show (ExtraConstraint info) where
   show typeConstraint =
      case typeConstraint of
         Prove p info ->
            "Prove (" ++ intercalate ", " (showQualifiers p) ++ ")" ++ showInfo info 
         Assume p info ->
            "Assume (" ++ intercalate ", " (showQualifiers p) ++ ")" ++ showInfo info
            
    where showInfo info = "   : {" ++ show info ++ "}"

instance Functor ExtraConstraint where
   fmap f typeConstraint = 
      case typeConstraint of
         Prove p info                   -> Prove p (f info) 
         Assume p info                  -> Assume p (f info) 

instance Substitutable (ExtraConstraint info) where
   sub |-> typeConstraint =
      case typeConstraint of
         Prove p info                   -> Prove (sub |-> p) info
         Assume p info                  -> Assume (sub |-> p) info 
      
   ftv typeConstraint =
      case typeConstraint of
         Prove p _                 -> ftv p
         Assume p _                -> ftv p

instance ( HasQual m info
         , PolyTypeConstraintInfo info
         ) => 
           Solvable (ExtraConstraint info) m 
   where
      solveConstraint typeConstraint =
         case typeConstraint of
            Prove p info ->       
               proveQualifier info p
               
            Assume p info ->
               assumeQualifier info p