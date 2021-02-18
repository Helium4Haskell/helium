module Helium.CodeGeneration.Iridium.RegionSize.Utils
    ( rsError, rsInfo
    ) where

import qualified Debug.Trace as T

----------------------------------------------------------------
-- Console messages
----------------------------------------------------------------

rsError :: String -> a
rsError = error . (++) "[RegionSize] " 

rsInfo :: a -> String -> a
rsInfo v s = T.trace ("\n[INFO] "++ s) v