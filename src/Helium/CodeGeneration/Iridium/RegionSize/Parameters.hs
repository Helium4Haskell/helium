module Helium.CodeGeneration.Iridium.RegionSize.Parameters
where
----------------------------------------------------------------
-- Parameters
----------------------------------------------------------------

removeEmpty :: Bool
removeEmpty = False

max_bound :: Int
max_bound = 1000

max_iterations :: Int
max_iterations = 10

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
               then "Test.fib" -- Fill in target name here
               else "" -- Do not change this one
stopOnTarget :: Bool
stopOnTarget = True

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
printMethodName = (False || printDerived || printSimplified || printFixpoint || printWithLocals || printEffects)

-- Printing datatypes
printDTInfo,printDTSorts,printDTRegions,printDTStructs,printDTDestructs :: Bool
printDTInfo      = False && debug
printDTSorts     = True && printDTInfo
printDTRegions   = True && printDTInfo
printDTStructs   = True && printDTInfo
printDTDestructs = True && printDTInfo