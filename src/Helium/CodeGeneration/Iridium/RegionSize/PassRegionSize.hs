module Helium.CodeGeneration.Iridium.RegionSize.PassRegionSize
    (passRegionSize)
where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.Data

passRegionSize :: NameSupply -> Module -> IO Module
passRegionSize supply m = return m
 