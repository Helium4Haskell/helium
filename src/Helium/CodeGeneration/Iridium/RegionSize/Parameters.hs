module Helium.CodeGeneration.Iridium.RegionSize.Parameters
where
----------------------------------------------------------------
-- Parameters
----------------------------------------------------------------

removeEmpty :: Bool
removeEmpty = True

max_bound :: Int
max_bound = 1

max_iterations :: Int
max_iterations = 7

----------------------------------------------------------------
-- Debug flags
----------------------------------------------------------------

-- Global enable/disable
debug,disable :: Bool
debug           = True -- ^ Enable debug mode
disable         = False -- ^ Disable region size analysis

-- Print the annotations of a single method (empty = no method selected)
targetMethod :: String
targetMethod = if debug 
               then "" -- Fill in target name here, leave empty to disable
               else "" -- Do not change this one
stopOnTarget :: Bool
stopOnTarget = True && debug

-- Sorting of annotations
sortDerived,sortSimplified,sortFixpoint,sortWithLocals,checkSortsEq :: Bool
sortDerived     = False && debug
sortSimplified  = False && debug
sortFixpoint    = False && debug
checkSortsEq    = False && debug
sortWithLocals  = False && debug

-- Printing of annotations/sorts
printDerived,printSimplified,printFixpoint,printWithLocals,printEffects,printMethodName :: Bool
printDerived    = False && debug
printSimplified = False && debug
printFixpoint   = False && debug
printWithLocals = False && debug
printEffects    = False && debug
printMethodName = ((False && debug) || printDerived || printSimplified || printFixpoint || printWithLocals || printEffects)

-- Printing datatypes
printDTInfo,printDTSorts,printDTRegions,printDTStructs,printDTDestructs :: Bool
printDTInfo      = False && debug
printDTSorts     = True && printDTInfo
printDTRegions   = True && printDTInfo
printDTStructs   = True && printDTInfo
printDTDestructs = True && printDTInfo