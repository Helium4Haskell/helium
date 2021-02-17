module Helium.CodeGeneration.Iridium.RegionSize.Utils
    (rsError)
where

----------------------------------------------------------------
-- Crash notices
----------------------------------------------------------------

rsError :: String -> a
rsError = error . (++) "[RegionSize] " 