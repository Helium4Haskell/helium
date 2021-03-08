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

import qualified Control.Exception as Exc

-- | Infer the size of regions
passRegionSize :: NameSupply -> Module -> IO Module
passRegionSize supply m = do 
  if (stringFromId (moduleName m) == "LvmLang"        && True)
    || (stringFromId (moduleName m) == "HeliumLang"   && True) 
    || (stringFromId (moduleName m) == "PreludePrim"  && True)
    || (stringFromId (moduleName m) == "Prelude"      && True)
    || (stringFromId (moduleName m) == "LvmException" && True)
  then return m
  else do
    print "=================="
    print "[PASS REGION SIZE]"
    print "=================="
    print $ moduleName m
    let gEnv = initialGEnv m
    let groups = map BindingNonRecursive $ moduleMethods m
    (_, methods) <- mapAccumLM analyseGroup gEnv groups
    return m{moduleMethods = concat methods}
    error "Don!"


{- Analyses a binding group of a single non-recursive function
   or a group of (mutual) recursive functions.
-}
analyseGroup :: GlobalEnv -> BindingGroup Method -> IO (GlobalEnv, [Declaration Method])
analyseGroup _ (BindingRecursive _) = rsError "Cannot analyse (mutual) recursive functions yet"
analyseGroup gEnv (BindingNonRecursive decl@(Declaration methodName _ _ _ method)) = do
  putStrLn $ "\n# Analyse method " ++ show methodName
  if True
  then do
    let mAnn  = analyse gEnv methodName method
        simpl = eval mAnn
    print mAnn
    putStrLn $ "\n# Simplified: " ++ show methodName
    print simpl 
    let mSrt1 = sort mAnn
        mSrt2 = sort simpl
    putStrLn $ "\n# Sort: " ++ show methodName
    print mSrt1 
    
    if mSrt1 /= mSrt2
    then putStrLn $ "Evaluation returned different sort!"
                  ++ "\n\tPre-eval:  " ++ show mSrt1
                  ++ "\n\tPost-eval: " ++ show mSrt2 
    else return ()
    putStrLn ""
    putStrLn ""

    let gEnv' = insertGlobal gEnv methodName simpl 
    return (gEnv', [decl{ declarationValue = method }])
  else do
    return (gEnv, [decl{ declarationValue = method }])



-- TODO: Move
-- | Accumulate left side of tuple
mapAccumLM :: Monad m => (a -> b -> m (a,c)) -> a -> [b] -> m (a,[c])
mapAccumLM _ s1 [] = return (s1, [])
mapAccumLM f s1 (x:xs) = do 
  (s2, y) <- f s1 x
  fmap (y:) <$> mapAccumLM f s2 xs



