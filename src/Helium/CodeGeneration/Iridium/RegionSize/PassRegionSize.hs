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

import Data.List (intercalate)

-- | TODO: There is still an evalutation bug.. Test.recu, first bound to a (fix) after eval bound to b

-- | Infer the size of regions
passRegionSize :: NameSupply -> Module -> IO Module
passRegionSize supply m = do 
  print "=================="
  print "[PASS REGION SIZE]"
  print "=================="
  print $ moduleName m
  let gEnv = initialGEnv m
  let groups = methodBindingGroups $ moduleMethods m
  (_, methods) <- mapAccumLM (analyseGroup $ stringFromId $ moduleName m) gEnv groups
  return m{moduleMethods = concat methods}


{- Analyses a binding group of a single non-recursive function
   or a group of (mutual) recursive functions.
-} -- TODO: Remove module name from params
analyseGroup :: String -> GlobalEnv -> BindingGroup Method -> IO (GlobalEnv, [Declaration Method])
analyseGroup modName gEnv (BindingRecursive bindings) = do
  let methods = map (\(Declaration methodName _ _ _ method) -> (methodName, method)) bindings
  (gEnv, transformeds) <- temp modName gEnv methods
  let bindings' = map (\(decl, (_,transformed)) -> decl{declarationValue=transformed}) $ zip bindings transformeds
  return (gEnv, bindings')
analyseGroup modName gEnv (BindingNonRecursive decl@(Declaration methodName _ _ _ method)) = do
  putStrLn $ "\n# Analyse method " ++ show methodName
  (gEnv, [(_,transformed)]) <- temp modName gEnv [(methodName,method)]
  return (gEnv, [decl{ declarationValue = transformed }])


temp ::  String -> GlobalEnv -> [(Id,Method)] -> IO (GlobalEnv, [(Id,Method)])
temp modName gEnv methods = do
  putStrLn $ "\n# Analyse methods:\n" ++ (intercalate "\n" $ map (show.fst) methods)
  if True
  then do
    let mAnn  = analyseMethods gEnv methods
        simpl = eval <$> mAnn
        fixed = solveFixpoints simpl
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
      putStrLn $ "\n# Simplified: "
      putStrLn $ intercalate "\n\n" (show <$> simpl) 
      putStrLn $ "\n# Fixpoint: "
      putStrLn $ intercalate "\n\n" (show <$> fixed) 
      -- putStrLn $ "\n# Sort: " ++ show methodName
      -- print mSrt2 

      -- if mSrt1 /= mSrt2
      -- then putStrLn $ "Evaluation returned different sort!"
      --               ++ "\n\tPre-eval:  " ++ show mSrt1
      --               ++ "\n\tPost-eval: " ++ show mSrt2 
      -- else return ()
      putStrLn ""
      putStrLn ""

    let gEnv' = foldl (\env (name,ann) -> insertGlobal env name ann) gEnv $ zip (fst <$> methods) fixed
    return (gEnv', methods)
  else do
    return (gEnv, methods)

