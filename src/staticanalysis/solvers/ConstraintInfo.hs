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

class Substitutable constraintinfo => ConstraintInfo constraintinfo where
   
   setOriginalTypeScheme :: TpScheme         -> constraintinfo -> constraintinfo   
   setOriginalTypeScheme _ = id    -- default definition (do nothing)
