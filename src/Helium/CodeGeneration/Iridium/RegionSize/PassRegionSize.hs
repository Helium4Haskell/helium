module Helium.CodeGeneration.Iridium.RegionSize.PassRegionSize
    (passRegionSize)
where

import Lvm.Common.Id
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.BindingGroup

import Helium.CodeGeneration.Iridium.RegionSize.Analysis
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.Constraints
import Helium.CodeGeneration.Iridium.RegionSize.DataTypes
import Helium.CodeGeneration.Iridium.RegionSize.Environments
import Helium.CodeGeneration.Iridium.RegionSize.Evaluate
import Helium.CodeGeneration.Iridium.RegionSize.Sort
import Helium.CodeGeneration.Iridium.RegionSize.SortUtils
import Helium.CodeGeneration.Iridium.RegionSize.Sorting
import Helium.CodeGeneration.Iridium.RegionSize.Transform
import Helium.CodeGeneration.Iridium.RegionSize.Utils
import Helium.CodeGeneration.Iridium.RegionSize.Fixpoint

import Data.List (intercalate)
import Data.Either (rights, lefts)
import qualified Data.Map as M 

-- | Infer the size of regions
passRegionSize :: NameSupply -> Module -> IO Module
passRegionSize _ m = do 
  if(((stringFromId $ moduleName m) == "LvmLang"        && True)
    || ((stringFromId $ moduleName m) == "HeliumLang"   && True) 
    || ((stringFromId $ moduleName m) == "PreludePrim"  && True)
    || ((stringFromId $ moduleName m) == "Prelude"      && True)
    || ((stringFromId $ moduleName m) == "LvmException" && True))
  then do
    return m
  else do
    let gEnv = initialGEnv m
    let groups = methodBindingGroups $ moduleMethods m

    ((_, finite, infinite), methods) <- mapAccumLM (analyseGroup (stringFromId $ moduleName m)) (gEnv,0,0) groups
    putStrLn $ "Finite:   " ++ show finite
    putStrLn $ "Infinite: " ++ show infinite

    return m{moduleMethods = concat methods}


{- Analyses a binding group of a single non-recursive function
   or a group of (mutual) recursive functions.
-} -- TODO: Remove module name from params
analyseGroup :: String -> (GlobalEnv, Int, Int) -> BindingGroup Method -> IO ((GlobalEnv, Int, Int), [Declaration Method])
-- Recurisve bindings
analyseGroup modName (gEnv, finite, infinite) (BindingRecursive bindings) = do
  let methods = map (\(Declaration methodName _ _ _ method) -> (methodName, method)) bindings

  ((gEnv', finite2, infinite2), transformeds) <- temp modName gEnv methods

  let bindings' = map (\(decl, (_,transformed)) -> decl{declarationValue=transformed}) $ zip bindings transformeds
  return ((gEnv', finite+finite2, infinite+infinite2)
         , bindings')
-- Non recursive binding
analyseGroup modName (gEnv, finite, infinite) (BindingNonRecursive decl@(Declaration methodName _ _ _ method)) = do
  ((gEnv', finite2, infinite2), [(_,transformed)]) <- temp modName gEnv [(methodName,method)]

  return ((gEnv', finite+finite2, infinite+infinite2)
         , [decl{ declarationValue = transformed }])


temp ::  String -> GlobalEnv -> [(Id,Method)] -> IO ((GlobalEnv, Int, Int), [(Id,Method)])
temp modName gEnv methods = do
  if((modName == "LvmLang"        && False)
    || (modName == "HeliumLang"   && False) 
    || (modName == "PreludePrim"  && False)
    || (modName == "Prelude"      && False)
    || (modName == "LvmException" && False))
  then do
    return ((gEnv, 0, 0), methods)
  else do
    -- Generate the annotations     
    let mAnn  = analyseMethods 0 gEnv methods
  
    -- Simplify the generated annotation
    let simpl = eval mAnn
    -- Solve the fixpoints
    let fixed = solveFixpoints simpl
    -- Check if the resulting annotation is well-sroted
    -- let sorts = sort fixed
    -- fixed' <- case sorts of
    --       Left  _ -> return $ flip ATop constrBot . methodSortAssign (globDataEnv gEnv) <$> (snd <$> methods) 
    --       Right _ -> return $ unsafeUnliftTuple fixed
    
    -- Fix the annotations of zero arity definitions
    let zerod = uncurry fixZeroArity <$> zip methods (unsafeUnliftTuple fixed)
    
    -- Update the global environment with the found annotations
    let gEnv' = foldr (uncurry insertGlobal) gEnv $ zip (fst <$> methods) zerod
    -- Save the annotation on the method
    let methods' = map (\((name,Method a b c d e anns f g), ann) -> (name, Method a b c d e (MethodAnnotateRegionSize ann:anns) f g)) $ zip methods zerod

    -- Compute the second pass
    let effects = collectEffects 
              <$> (unsafeUnliftTuple 
                  . eval 
                  . solveFixpoints 
                  $ analyseMethods 1 gEnv' methods')
    let arePrimitive = foldr (||) False (isPrimitiveType [] <$> methodType . snd <$> methods)
    let finite   = if arePrimitive 
                   then sum $ length <$> filter (not . (== Infty) . snd) <$> filter (not . (== Region RegionGlobal) . fst) <$> M.toList <$> effects
                   else 0
    let infinite = if arePrimitive 
                   then (sum $ length <$> filter (not . (== Region RegionGlobal) . fst) <$> M.toList <$> effects) - finite 
                   else 0

    -- Do the program transformation & remove empty regions
    let transformed = uncurry transform <$> zip effects (snd <$> methods')
    let emptyRegs   = collectEmptyRegs <$> transformed
    let cleaned     = uncurry remEmptyRegs <$> zip emptyRegs transformed

    if((modName == "LvmLang"        && True)
      || (modName == "HeliumLang"   && True) 
      || (modName == "PreludePrim"  && True)
      || (modName == "Prelude"      && True)
      || (modName == "LvmException" && True))
    then do return () --putStrLn "-"
    else do
      putStrLn $ "\n# Analyse methods:\n" ++ (intercalate "\n" $ map (show.fst) methods)
      print mAnn
      putStrLn $ "\n# Simplified: "
      print simpl 
      putStrLn $ "\n# Fixpoint: "
      print fixed
      -- fixed' <- case sorts of
      --       Left  e -> putStrLn e >>= \_ -> rsError "nope"
      --       Right _ -> return fixed
      -- putStrLn $ "\n# Sort: "
      -- print sorts 
      -- putStrLn $ "\n# Zerod: "
      -- print zerod 
      -- putStrLn $ "\n# Effects: "
      -- print effects

      -- if mSrt1 /= mSrt2
      -- then putStrLn $ "Evaluation returned different sort!"
      --               ++ "\n\tPre-eval:  " ++ show mSrt1
      --               ++ "\n\tPost-eval: " ++ show mSrt2 
      -- else return ()

      -- putStrLn ""
      putStrLn ""

    return ((gEnv', finite, infinite), zip (fst <$> methods) cleaned)

-- TODO: Correct bottom for offsets 
methodSortAssign :: DataTypeEnv -> Method -> Sort
methodSortAssign dEnv = SortLam SortUnit . sortAssign dEnv . methodType 

-- | Get an array of annotations from a tuple
unsafeUnliftTuple :: Annotation -> [Annotation]
unsafeUnliftTuple (ATuple as) = as
unsafeUnliftTuple (ATop a b) = repeat $ ATop a b
unsafeUnliftTuple a = rsError $ "unsafeUnliftTuple: Called unsafe unlift tuple on non-tuple: " ++ show a


{-| Fix problems arising from zero arity functions
  Assigns the global regions to the return regions and additional regions.
-}
fixZeroArity :: (Id, Method) -> Annotation -> Annotation
fixZeroArity (_, Method _ aRegs args _ rRegs _ _ _) ann =
  case length $ rights args of
    0 -> let aplARegs = AApl ann $ regionVarsToGlobal aRegs
             newQuantIndexes = reverse $ TVar <$> [1..(length $ lefts args)]
             quants a = foldr (const AQuant) a (lefts args)
             aplTypes = foldl AInstn aplARegs newQuantIndexes
             aplRRegs = AApl aplTypes $ regionVarsToGlobal rRegs
         in ALam SortUnit $ eval $ quants $ AProj 0 aplRRegs
    _ -> ann 

-- | Create an annotation that assigns all regionvars the global region
regionVarsToGlobal :: RegionVars -> Annotation
regionVarsToGlobal (RegionVarsSingle _) = AReg RegionGlobal
regionVarsToGlobal (RegionVarsTuple rs) = ATuple $ regionVarsToGlobal <$> rs


collectEffects :: Annotation -> Constr
collectEffects = foldAnnAlg collectAlg
    where collectAlg = AnnAlg {
        aVar    = \_ _   -> constrBot,
        aReg    = \_ _   -> constrBot,
        aLam    = \_ _ a -> a,
        aApl    = \_ a b -> constrAdd a b,
        aConstr = \_ c   -> c,
        aUnit   = \_     -> constrBot,
        aTuple  = \_ as  -> foldr constrAdd constrBot as,
        aProj   = \_ _ a -> a,
        aAdd    = \_ a b -> constrAdd a b,
        aMinus  = \_ a _ -> a,
        aJoin   = \_ a b -> constrAdd a b,
        aQuant  = \_ a   -> a,
        aInstn  = \_ a _ -> a,
        aTop    = \_ _ c -> c,
        aBot    = \_ _   -> constrBot,
        aFix    = \_ _ a -> foldr constrAdd constrBot a
    }

isPrimitiveType  :: [Type] -> Type -> Bool
isPrimitiveType  ts (TStrict a)     = isPrimitiveType ts a
isPrimitiveType  ts (TForall _ _ a) = isPrimitiveType ts a
isPrimitiveType  ts (TVar a)        = True
isPrimitiveType  ts (TAp t1 t2)     = isPrimitiveType (t2:ts) t1
isPrimitiveType  [t1,t2] (TCon TConFun)       = isPrimitiveType [] t1 && isPrimitiveType [] t2  
isPrimitiveType  ts      (TCon (TConTuple n)) = foldr (&&) True $ isPrimitiveType [] <$> ts
isPrimitiveType  []      (TCon (TConDataType _))            = True
isPrimitiveType  [a]     (TCon (TConTypeClassDictionary _)) = False
isPrimitiveType  _       (TCon (TConDataType _)) = True
isPrimitiveType  _ t = rsError $ "nope"
