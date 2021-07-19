module Helium.CodeGeneration.Iridium.RegionSize.PassRegionSize
    (passRegionSize)
where

import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Show()
import Helium.CodeGeneration.Iridium.BindingGroup

import Helium.CodeGeneration.Iridium.RegionSize.Analysis
import Helium.CodeGeneration.Iridium.RegionSize.Annotation
import Helium.CodeGeneration.Iridium.RegionSize.AnnotationUtils
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
import Helium.CodeGeneration.Iridium.RegionSize.Parameters

import Data.List (intercalate, foldl')

import System.CPUTime
import Text.Printf

---------------------------------------------------------------
-- Interface
----------------------------------------------------------------

-- | Infer the size of regions
passRegionSize :: NameSupply -> Module -> IO Module
passRegionSize _ m = if disable then return m else do
    start <- getCPUTime 

    -- Construct the global environment for the module
    let gEnv = initialGEnv m
    printDataTypes gEnv

    -- Run the analysis on the binding groups
    let groups = methodBindingGroups $ moduleMethods m
    (statistics, methods) <- mapAccumLM analyseBindingGroup (gEnv,0,0,0) groups

    printMetrics start statistics 

    -- Return the updated methods
    return m{moduleMethods = concat methods}


{- Analyses a binding group of a single non-recursive function
   or a group of (mutual) recursive functions.
-} 
analyseBindingGroup :: (GlobalEnv, Int, Int, Int) -> BindingGroup Method -> IO ((GlobalEnv, Int, Int, Int), [Declaration Method])
-- Recurisve bindings (call pipeline with the list of recursive methods)
analyseBindingGroup (gEnv, finite, infinite, zero) (BindingRecursive bindings) = do
  let methods = (\(Declaration methodName _ _ _ method) -> (methodName, method)) <$> bindings
  ((gEnv', finite2, infinite2,zero2), transformeds) <- pipeline gEnv methods
  let bindings' = map (\(decl, (_,transformed)) -> decl{declarationValue=transformed}) $ zip bindings transformeds
  return ((gEnv', finite+finite2, infinite+infinite2, zero+zero2)
         , bindings')
-- Non recursive binding (call pipeline with singleton list)
analyseBindingGroup (gEnv, finite, infinite, zero) (BindingNonRecursive decl@(Declaration methodName _ _ _ method)) = do
  ((gEnv', finite2, infinite2,zero2), [(_,transformed)]) <- pipeline gEnv [(methodName,method)]
  return ((gEnv', finite+finite2, infinite+infinite2, zero+zero2)
         , [decl{ declarationValue = transformed }])


-- | Run the analysis on a group of methods
pipeline ::  GlobalEnv -> [(Id,Method)] -> IO ((GlobalEnv, Int, Int, Int), [(Id,Method)])
pipeline gEnv methods = do
    let dEnv = globDataEnv gEnv
        isTargetMethod = debug && (idFromString targetMethod `elem` (fst <$> methods))

    if printMethodName || isTargetMethod then do
      putStrLn $ "\n# Analyse methods:\n" ++ (intercalate "\n" $ map (show.fst) methods)
    else return ()

    -- Derive anotation, print and sort
    -- TODO: For calculating a bound on the global region, you need the zeroing effects.
    let (ann, zeroingEffect) = analyseMethods 0 gEnv methods
    let derived = inlineFixpoints ann
    _ <- printAnnotation (printDerived || isTargetMethod) "Derived" derived
    _ <- checkSort sortDerived dEnv "derived" derived

    -- Simplify annotation, print and sort
    let simplified = eval dEnv derived
    _ <- printAnnotation (printSimplified || isTargetMethod) "Simplified" simplified
    _ <- checkSort sortSimplified dEnv "simplified" simplified

    -- Calculate the fixpoint, print an sort
    let fixpoint = solveFixpoints (fst <$> methods) dEnv simplified
    _ <- printAnnotation (printFixpoint || isTargetMethod) "Fixpoint" fixpoint
    _ <- checkSort sortFixpoint dEnv "fixpoint" fixpoint

    -- Check if the sort did not change during evalutations
    _ <- checkAnnotationSorts checkSortsEq dEnv [derived,simplified,fixpoint]

    -- Update the global environment with the found annotations
    let unpacked = unsafeUnliftTuple fixpoint
    let gEnv' = foldr (uncurry insertGlobal) gEnv $ zip (fst <$> methods) unpacked
    -- Save the annotation on the method
    let methods' = uncurry methodAddRegionSizeAnnotation <$> zip methods unpacked

    -- Derive again, but now with the local regions.
    let withLocals = (unsafeUnliftTuple 
            . solveFixpoints (fst <$> methods) dEnv
            . eval dEnv 
            . fst
            $ analyseMethods 1 gEnv' methods')
    _ <- printAnnotation (printWithLocals || isTargetMethod) "With locals (fixpoint)" $ ATuple withLocals
    _ <- checkSort sortWithLocals dEnv "withLocals" $ ATuple withLocals

    -- Extract effects and transform program
    let --zeroingEffect'   = constrRemVarRegs <$> unAConstr . solveFixpoints (fst <$> methods) . eval dEnv <$> zeroingEffect
        annotationEffect = constrRemVarRegs <$> collectEffects <$> withLocals
        higherOrderFix   = constrRemVarRegs <$> fixHigherOrderApplication <$> withLocals
    let effects = zipWith constrAdd annotationEffect higherOrderFix
    _ <- printAnnotation (printWithLocals || isTargetMethod) "Effects" $ ATuple $ AConstr <$> effects
    
    let transformed   = uncurry transform <$> zip effects (snd <$> methods')
    let emptyRegs     = collectEmptyRegs     <$> transformed
    let boundedRegs   = collectBoundedRegs   <$> transformed
    let unboundedRegs = collectUnboundedRegs <$> transformed
    let cleaned     = if removeEmpty
                      then uncurry remEmptyRegs <$> zip emptyRegs transformed
                      else transformed

    -- Count bounded and unbouned regions
    let (finite, infinite, zero) = (length $ concat boundedRegs, length $ concat unboundedRegs, length $ concat emptyRegs)

    if stopOnTarget && isTargetMethod
    then rsError $ "Stopped by target method: " ++ show targetMethod
    else return ()

    return ((gEnv', finite, infinite, zero), zip (fst <$> methods) cleaned)

{-| When a local region is applied to a higher order function
  we must make said region unbounded. We cannot know the true bound.
  This could also be corrected with a change in region inference.
-}
fixHigherOrderApplication :: Annotation -> Constr
fixHigherOrderApplication = constrRemVarRegs . flip go constrBot
  where go (AVar   _  ) c = c
        go (AApl   f x) c = go f . constrJoins $ c : (constrInfty <$> gatherLocals x)
        go (ALam   _ a) _ = go a constrBot
        go (ATuple as ) _ = constrJoins $ flip go constrBot <$> as
        go (AProj  _ a) _ = go a constrBot
        go (AAdd   a b) _ = constrJoin (go a constrBot) (go b constrBot)
        go (AJoin  a b) _ = constrJoin (go a constrBot) (go b constrBot)
        go (AQuant a  ) _ = go a constrBot
        go (AInstn a _) _ = go a constrBot
        go (AFix  _ as) _ = constrJoins $ flip go constrBot <$> as
        go _ _ = constrBot

-- | Add the derived annotation to the methods annotations
methodAddRegionSizeAnnotation :: (Id,Method) -> Annotation -> (Id,Method)
methodAddRegionSizeAnnotation (name,method) ann = (name, methodAddAnnotation (MethodAnnotateRegionSize ann) method)     

----------------------------------------------------------
-- Initial global environment
----------------------------------------------------------------

-- | Initial analysis environment
initialGEnv :: Module -> GlobalEnv
initialGEnv m = GlobalEnv typeEnv functionEnv dataTypeEnv
  where
    -- Environment is only used for type synonyms
    typeEnv = TypeEnvironment synonyms emptyMap emptyMap

    -- Type synonims
    synonyms :: IdMap Type
    synonyms = mapFromList [(name, tp) | Declaration name _ _ _ (TypeSynonym _ tp) <- moduleTypeSynonyms m]

    -- Functions
    functionEnv :: IdMap Annotation
    functionEnv = mapFromList abstracts

    abstracts :: [(Id, Annotation)]
    abstracts = abstract <$> moduleAbstractMethods m
    abstract (Declaration name _ _ _ (AbstractMethod tp _ _ anns)) = (name, regionSizeAnn tp anns)

    regionSizeAnn :: Type -> [MethodAnnotation] -> Annotation
    regionSizeAnn _ (MethodAnnotateRegionSize a:_) = a
    regionSizeAnn tp (_:xs) = regionSizeAnn tp xs
    regionSizeAnn tp []     = top tp

    -- Top of type
    top :: Type -> Annotation
    top = flip ATop constrBot . SortLam SortUnit . sortAssign dataTypeEnv . typeNormalize typeEnv

    -- ~~~~~~~~~
    -- Datatypes
    -- ~~~~~~~~~

    dataTypeEnv :: DataTypeEnv
    dataTypeEnv = DataTypeEnv moduleDataTypeSorts moduleDataTypeRegions moduleDataTypeConstructors moduleDataTypeDestructors

    -- Data type sorts
    moduleDataTypeSorts, moduleDataTypeRegions :: IdMap DataSort
    moduleDataTypeSorts = foldl' (declDataTypeSort typeEnv moduleDataTypeRegions) recDSorts dataTypeGroups
    moduleDataTypeRegions = foldl' (declDataTypeRegions typeEnv) recDSorts dataTypeGroupsRegs
    -- Constructor annotations
    moduleDataTypeConstructors :: IdMap Annotation
    moduleDataTypeConstructors = mapFromList $ dataTypeGroups >>= makeDataTypeConstructors (emptyDEnv{dtSorts=moduleDataTypeSorts})
    -- Destructor annotations
    moduleDataTypeDestructors :: IdMap [Annotation]
    moduleDataTypeDestructors = mapFromList $ dataTypeGroups >>= makeDataTypeDestructors (emptyDEnv{dtSorts=moduleDataTypeSorts})

    -- Environment used for the recursive positions of data types (Unit sort qith quantifications)
    recDSorts :: IdMap DataSort
    recDSorts = mapFromList . map makeRecDataTypeSort $ moduleDataTypes m
    makeRecDataTypeSort ::  Declaration DataType -> (Id, DataSort)
    makeRecDataTypeSort decl = (declarationName decl, Complex . foldr (const SortQuant) SortUnit . dataTypeQuantors $ declarationValue decl)
    dataTypeGroups,dataTypeGroupsRegs :: [BindingGroup DataType]
    dataTypeGroups     = dataTypeBindingGroups True  $ moduleDataTypes m
    dataTypeGroupsRegs = dataTypeBindingGroups False $ moduleDataTypes m

----------------------------------------------------------------
-- Debug stuff
----------------------------------------------------------------

-- | Check the sort of an annotation
checkSort :: Bool       -- ^ Debug flag (sort yes/no)
          -> DataTypeEnv
          -> String     -- ^ Annotation name
          -> Annotation -- ^ Annotation
          -> IO ()
checkSort False _ _ _ = return ()
checkSort True dEnv name ann =
   case sort dEnv ann of
     Left  s -> do
       putStrLn ""
       putStrLn $ cleanTUP s
       rsError $ "# Wrong sort (" ++ name ++ ")"
     Right _ -> return ()

-- | Check if the sort did not change during evaluation
checkAnnotationSorts :: Bool -- ^ Debug flag (check eq yes/no)
                     -> DataTypeEnv -> [Annotation] -> IO ()
checkAnnotationSorts False _    _  = return ()                   
checkAnnotationSorts _     _    [] = return ()                   
checkAnnotationSorts True  dEnv xs = 
  let (s:ss) = sort dEnv <$> xs
  in if all (s ==) ss
     then return ()
     else rsError "Sort changed during evaluation."           

-- | Print the annotation depending on the debug flag
printAnnotation :: Bool       -- ^ Debug flag (sort yes/no)
                -> String     -- ^ Annotation name
                -> Annotation -- ^ Annotation
                -> IO ()
printAnnotation False _ _ = return ()
printAnnotation True name ann = 
  do putStrLn $ "\n# " ++ name ++ ": " 
     print ann 

-- | Print out the derive datatypes sorts and annotations
printDataTypes :: GlobalEnv -> IO ()
printDataTypes gEnv = do
    if printDTSorts then do
      putStrLn "=================================================================="
      putStrLn "Sorts:"
      putStrLn "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
      putStrLn . intercalate "\n" $ show <$> (listFromMap . dtSorts $ globDataEnv gEnv)
    else return ()
    if printDTRegions then do
      putStrLn "=================================================================="
      putStrLn "Regions:"
      putStrLn "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
      putStrLn . intercalate "\n" $ show <$> (listFromMap . dtRegions $ globDataEnv gEnv)
    else return ()
    if printDTStructs then do
      putStrLn "=================================================================="
      putStrLn "Structors:"
      putStrLn "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
      putStrLn . intercalate "\n" $ show <$> (listFromMap . dtStructs $ globDataEnv gEnv)
    else return ()
    if printDTDestructs then do
      putStrLn "=================================================================="
      putStrLn "Destructors:"
      putStrLn "~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~"
      putStrLn . intercalate "\n" $ show <$> (listFromMap . dtDestructs $ globDataEnv gEnv)
      putStrLn "=================================================================="
    else return ()
    return ()

-- | Print out the collected metrics for the module
printMetrics :: Integer -> (GlobalEnv, Int, Int, Int) -> IO ()
printMetrics start (_, finite, infinite, zero) =
    -- Print CPU time and region metrics
    if debug then do
      putStrLn $ "Finite:   " ++ show finite
      putStrLn $ "Infinite: " ++ show infinite
      putStrLn $ "Zero:     " ++ show zero
      end <- getCPUTime
      let diff = ((fromIntegral (end - start)) :: Double) / ((10::Double)^(12::Int))
      printf "Computation time: %0.3f sec\n" diff 
    else return ()
