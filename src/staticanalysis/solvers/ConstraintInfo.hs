-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- ConstrainInfo.hs : Information that is stored for each constraint.
--
-------------------------------------------------------------------------------

module ConstraintInfo where

import Types
import Utils

class ConstraintInfo constraintinfo where
   
   setOriginalTypeScheme    :: TpScheme  -> constraintinfo -> constraintinfo  
   setConstraintPhaseNumber :: Int       -> constraintinfo -> constraintinfo   
   setReductionError        :: Predicate -> constraintinfo -> constraintinfo 
   
   setOriginalTypeScheme    _ = id    -- default definition (do nothing)
   setConstraintPhaseNumber _ = id    -- default definition (do nothing) 
   setReductionError        _ = id    -- default definition (do nothing) 
   
