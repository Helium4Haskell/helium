module Helium.CodeGeneration.Iridium.RegionSize.PassRegionSize
    (passRegionSize)
where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Core.TypeEnvironment
import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.BindingGroup

import Helium.CodeGeneration.Iridium.RegionSize.Analysis
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Environments
import Helium.CodeGeneration.Iridium.RegionSize.Evaluate
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Sorting
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Fixpoint

import qualified Control.Exception as Exc

-- | TODO: There is still an evalutation bug.. Test.recu, first bound to a (fix) after eval bound to b

-- | Infer the size of regions
passRegionSize :: NameSupply -> Module -> IO Module
passRegionSize supply m = do 
  print "=================="
  print "[PASS REGION SIZE]"
  print "=================="
  print $ moduleName m
  let gEnv = initialGEnv m
  let groups = map BindingNonRecursive $ moduleMethods m
  (_, methods) <- mapAccumLM (analyseGroup $ stringFromId $ moduleName m) gEnv groups
  return m{moduleMethods = concat methods}


{- Analyses a binding group of a single non-recursive function
   or a group of (mutual) recursive functions.
-} -- TODO: Remove module name from params
analyseGroup :: String -> GlobalEnv -> BindingGroup Method -> IO (GlobalEnv, [Declaration Method])
analyseGroup _ _ (BindingRecursive _) = rsError "Cannot analyse (mutual) recursive functions yet"
analyseGroup modName gEnv (BindingNonRecursive decl@(Declaration methodName _ _ _ method)) = do
  putStrLn $ "\n# Analyse method " ++ show methodName
  if True
  then do
    let mAnn  = analyse gEnv methodName method
        simpl = eval mAnn
        fixed = solveFix simpl
        -- mSrt1 = sort mAnn
        -- mSrt2 = sort simpl
    if((modName == "LvmLang"        && True)
      || (modName == "HeliumLang"   && True) 
      || (modName == "PreludePrim"  && True)
      || (modName == "Prelude"      && True)
      || (modName == "LvmException" && True))
    then do putStrLn "-"
    else do
      print mAnn
      -- putStrLn $ "\n# Simplified: " ++ show methodName
      -- print simpl 
      -- putStrLn $ "\n# Fixpoint: " ++ show methodName
      -- print fixed 
      -- putStrLn $ "\n# Sort: " ++ show methodName
      -- print mSrt2 

      -- if mSrt1 /= mSrt2
      -- then putStrLn $ "Evaluation returned different sort!"
      --               ++ "\n\tPre-eval:  " ++ show mSrt1
      --               ++ "\n\tPost-eval: " ++ show mSrt2 
      -- else return ()
      putStrLn ""
      putStrLn ""

    let gEnv' = insertGlobal gEnv methodName fixed 
    return (gEnv', [decl{ declarationValue = method }])
  else do
    return (gEnv, [decl{ declarationValue = method }])

