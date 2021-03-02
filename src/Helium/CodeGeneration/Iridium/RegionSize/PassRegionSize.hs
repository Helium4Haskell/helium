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
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Environments

-- | Infer the size of regions
passRegionSize :: NameSupply -> Module -> IO Module
passRegionSize supply m = do 
  let gEnv = initialGEnv m
  let groups = map BindingNonRecursive $ moduleMethods m
  (_, methods) <- mapAccumLM analyseGroup gEnv groups
  return m{moduleMethods = concat methods}


{- Analyses a binding group of a single non-recursive function
   or a group of (mutual) recursive functions.
-}
analyseGroup :: GlobalEnv -> BindingGroup Method -> IO (GlobalEnv, [Declaration Method])
analyseGroup _ (BindingRecursive _) = rsError "Cannot analyse (mutual) recursive functions yet"
analyseGroup gEnv (BindingNonRecursive decl@(Declaration methodName _ _ _ method)) = do
  putStrLn $ "# Analyse method " ++ show methodName
  let (mAnn, mEff) = analyse gEnv methodName method -- TODO: finish annotation (or do it in analyseMethod)
--   print annotation
--   let simplified = simplify dataTypeEnv annotation
--   putStrLn "Simplified:"
--   print simplified
  return (gEnv, [decl{ declarationValue = method }])



-- TODO: Move
-- | Accumulate left side of tuple
mapAccumLM :: Monad m => (a -> b -> m (a,c)) -> a -> [b] -> m (a,[c])
mapAccumLM _ s1 [] = return (s1, [])
mapAccumLM f s1 (x:xs) = do 
  (s2, y) <- f s1 x
  fmap (y:) <$> mapAccumLM f s2 xs



