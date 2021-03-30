module Helium.CodeGeneration.Iridium.RegionSize.PassRegionSize
    (passRegionSize)
where

import Lvm.Common.Id
import Lvm.Core.Type

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
import Data.Either (rights, lefts)

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
  if((modName == "LvmLang"        && True)
    || (modName == "HeliumLang"   && True) 
    || (modName == "PreludePrim"  && True)
    || (modName == "Prelude"      && True)
    || (modName == "LvmException" && True))
  then do
    return (gEnv, methods)
  else do

    putStrLn $ "\n# Analyse methods:\n" ++ (intercalate "\n" $ map (show.fst) methods)
    
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
    fixed' <- case mSrt2 of
                Left  e -> putStrLn e >>= \_ -> rsError "nope"
                Right _ -> return $ unsafeUnliftTuple fixed
    let zerod = uncurry fixZeroArity <$> zip methods fixed'

    -- Update the global environment with the found annotations
    let gEnv' = foldr (uncurry insertGlobal) gEnv $ zip (fst <$> methods) zerod
    -- Save the annotation on the method
    let methods' = map (\((name,Method a b c d e anns f g), ann) -> (name, Method a b c d e (MethodAnnotateRegionSize ann:anns) f g)) $ zip methods zerod
    
    return (gEnv', methods')


-- | Get an array of annotations from a tuple
unsafeUnliftTuple :: Annotation -> [Annotation]
unsafeUnliftTuple (ATuple as) = as
unsafeUnliftTuple a = rsError $ "unsafeUnliftTuple: Called unsafe unlift tuple on non-tuple: " ++ show a


-- TODO: Quantifiers
-- | Fix problems arising from zero arity functions
fixZeroArity :: (Id, Method) -> Annotation -> Annotation
fixZeroArity (name, Method _ aRegs args _ rRegs _ _ _) ann =
  case length $ rights args of
    0 -> let 
             aplARegs = AApl ann      $ regionVarsToGlobal aRegs
             newQuantIndexes = reverse $ TVar <$> [1..(length $ lefts args)]
             aplTypes = foldl AInstn aplARegs newQuantIndexes
             aplRRegs = AApl aplTypes $ regionVarsToGlobal rRegs
             quants :: Annotation -> Annotation
             quants a = foldr (const AQuant) a (lefts args)
         in eval $ quants aplRRegs
    _ -> ann 

-- | Create an annotation that assigns all regionvars the global region
regionVarsToGlobal :: RegionVars -> Annotation
regionVarsToGlobal (RegionVarsSingle r) = AReg RegionGlobal
regionVarsToGlobal (RegionVarsTuple rs) = ATuple $ regionVarsToGlobal <$> rs