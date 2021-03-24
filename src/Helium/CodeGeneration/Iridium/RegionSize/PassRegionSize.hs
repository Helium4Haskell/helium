module Helium.CodeGeneration.Iridium.RegionSize.PassRegionSize
    (passRegionSize)
where

import Lvm.Common.Id

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.BindingGroup

import Helium.CodeGeneration.Iridium.RegionSize.Analysis
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Environments
import Helium.CodeGeneration.Iridium.RegionSize.Evaluate
import Helium.CodeGeneration.Iridium.RegionSize.Sorting
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Fixpoint


import Data.List (intercalate)


-- | TODO: There is still an evalutation bug.. Test.recu, first bound to a (fix) after eval bound to b

-- | Infer the size of regions
passRegionSize :: NameSupply -> Module -> IO Module
passRegionSize _ m = do 
  let gEnv = initialGEnv m
  let groups = methodBindingGroups $ moduleMethods m

  (_, methods) <- mapAccumLM (analyseGroup (stringFromId $ moduleName m)) gEnv groups

  return m{moduleMethods = concat methods}


{- Analyses a binding group of a single non-recursive function
   or a group of (mutual) recursive functions.
-} -- TODO: Remove module name from params
analyseGroup :: String -> GlobalEnv -> BindingGroup Method -> IO (GlobalEnv, [Declaration Method])
analyseGroup modName gEnv (BindingRecursive bindings) = do
  let methods = map (\(Declaration methodName _ _ _ method) -> (methodName, method)) bindings

  (gEnv', transformeds) <- temp modName gEnv methods

  let bindings' = map (\(decl, (_,transformed)) -> decl{declarationValue=transformed}) $ zip bindings transformeds
  return (gEnv', bindings')

analyseGroup modName gEnv (BindingNonRecursive decl@(Declaration methodName _ _ _ method)) = do
  (gEnv', [(_,transformed)]) <- temp modName gEnv [(methodName,method)]

  return (gEnv', [decl{ declarationValue = transformed }])


temp ::  String -> GlobalEnv -> [(Id,Method)] -> IO (GlobalEnv, [(Id,Method)])
temp modName gEnv methods = do
  putStrLn $ "\n# Analyse methods:\n" ++ (intercalate "\n" $ map (show.fst) methods)
  if True
  then do
    let mAnn  = analyseMethods gEnv methods
        simpl = eval mAnn
        fixed = solveFixpoints simpl
        -- mSrt1 = sort mAnn
        mSrt2 = sort fixed
    if((modName == "LvmLang"        && True)
      || (modName == "HeliumLang"   && True) 
      || (modName == "PreludePrim"  && True)
      || (modName == "Prelude"      && True)
      || (modName == "LvmException" && True))
    then do putStrLn "-"
    else do
      print mAnn
      putStrLn $ "\n# Simplified: "
      putStrLn $ (show simpl) 
      putStrLn $ "\n# Fixpoint: "
      putStrLn $ (show fixed) 
      putStrLn $ "\n# Sort: "
      print mSrt2 

      -- if mSrt1 /= mSrt2
      -- then putStrLn $ "Evaluation returned different sort!"
      --               ++ "\n\tPre-eval:  " ++ show mSrt1
      --               ++ "\n\tPost-eval: " ++ show mSrt2 
      -- else return ()
      putStrLn ""
      putStrLn ""
    let fixed' = unsafeUnliftTuple fixed
    let gEnv' = foldl (\env (name,ann) -> insertGlobal env name ann) gEnv $ zip (fst <$> methods) fixed'
        methods' = map (\((name,Method a b c d e anns f g), ann) -> (name, Method a b c d e (MethodAnnotateRegionSize ann:anns) f g)) $ zip methods fixed'
    return (gEnv', methods')
  else do
    return (gEnv, methods)

-- | Get an array of annotations from a tuple
unsafeUnliftTuple :: Annotation -> [Annotation]
unsafeUnliftTuple (ATuple as) = as
unsafeUnliftTuple a = rsError $ "unsafeUnliftTuple: Called unsafe unlift tuple on non-tuple: " ++ show a
