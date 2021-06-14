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

import Data.List (intercalate)
import qualified Data.Map as M 

-- | Infer the size of regions
passRegionSize :: NameSupply -> Module -> IO Module
passRegionSize _ m = do
    putStrLn "=================================================================="
    print (moduleName m)
    putStrLn "=================================================================="
    let gEnv = initialGEnv m
    putStrLn . intercalate "\n" $ show <$> (listFromMap . dtSorts $ globDataEnv gEnv)
    putStrLn "=================================================================="
    putStrLn . intercalate "\n" $ show <$> (listFromMap . dtRegions $ globDataEnv gEnv)
    putStrLn "=================================================================="
    putStrLn . intercalate "\n" $ show <$> (listFromMap . dtStructs $ globDataEnv gEnv)

    let groups = methodBindingGroups $ moduleMethods m

    ((_, finite, infinite), methods) <- mapAccumLM analyseBindingGroup (gEnv,0,0) groups
    putStrLn $ "Finite:   " ++ show finite
    putStrLn $ "Infinite: " ++ show infinite

    return m{moduleMethods = concat methods}


{- Analyses a binding group of a single non-recursive function
   or a group of (mutual) recursive functions.
-} 
analyseBindingGroup :: (GlobalEnv, Int, Int) -> BindingGroup Method -> IO ((GlobalEnv, Int, Int), [Declaration Method])
-- Recurisve bindings
analyseBindingGroup (gEnv, finite, infinite) (BindingRecursive bindings) = do
  let methods = map (\(Declaration methodName _ _ _ method) -> (methodName, method)) bindings

  ((gEnv', finite2, infinite2), transformeds) <- pipeline gEnv methods

  let bindings' = map (\(decl, (_,transformed)) -> decl{declarationValue=transformed}) $ zip bindings transformeds
  return ((gEnv', finite+finite2, infinite+infinite2)
         , bindings')
-- Non recursive binding
analyseBindingGroup (gEnv, finite, infinite) (BindingNonRecursive decl@(Declaration methodName _ _ _ method)) = do
  ((gEnv', finite2, infinite2), [(_,transformed)]) <- pipeline gEnv [(methodName,method)]

  return ((gEnv', finite+finite2, infinite+infinite2)
         , [decl{ declarationValue = transformed }])


-- | Run the analysis on a group of methods
pipeline ::  GlobalEnv -> [(Id,Method)] -> IO ((GlobalEnv, Int, Int), [(Id,Method)])
pipeline gEnv methods = do
    let canDerive = ((and (not.isDataTypeMethod (globDataEnv gEnv) . typeNormalize (globTypeEnv gEnv) . methodType . snd <$> methods))
                 && (and (not.isDataTypeMethod (globDataEnv gEnv) . typeNormalize (globTypeEnv gEnv) . localType <$> concat (methodLocals False (globTypeEnv gEnv) . snd <$> methods))))

    if not canDerive
    then do
      -- | Insert top for bad methods
      let top = flip ATop constrBot . methodSortAssign (globTypeEnv gEnv) (globDataEnv gEnv) . snd <$> methods
      let gEnv' = foldr (uncurry insertGlobal) gEnv $ zip (fst <$> methods) top
      let methods' = map (\((name,Method a b c d e anns f g), ann) -> (name, Method a b c d e (MethodAnnotateRegionSize ann:anns) f g)) $ zip methods top
      return ((gEnv', 0, 0), methods')
    else do
      putStrLn $ "\n# Analyse methods:\n" ++ (intercalate "\n" $ map (show.fst) methods)
      putStrLn $ "\n# Can derive: " ++ show canDerive ++ "\n" ++ (show $ typeNormalize (globTypeEnv gEnv) . methodType . snd <$> methods)
      let dEnv = globDataEnv gEnv

      -- Generate the annotations     
      let mAnn  = inlineFixpoints $ analyseMethods 0 gEnv methods
      let simpl = eval dEnv $ inlineFixpoints $ eval dEnv mAnn
      let fixed = solveFixpoints dEnv simpl

      putStrLn $ "\n# Derived annotation: "
      print mAnn
      
      putStrLn $ "\n# Simplified: "
      print simpl
      -- Check if the resulting annotation is well-sroted
      _ <- case sort dEnv simpl of
              Left  s -> do
                putStrLn ""
                putStrLn s
                rsError $ "Wrong sort"
              Right _ -> return simpl


      -- Solve the fixpoints
      putStrLn $ "\n# Fixpoint: "
      print fixed 

      -- Check if the resulting annotation is well-sroted
      fixed' <- case sort dEnv fixed of
              Left  s -> do
                putStrLn ""
                putStrLn s
                rsError $ "Wrong sort"
              Right _ -> return $ unsafeUnliftTuple fixed

      -- Update the global environment with the found annotations
      let gEnv' = foldr (uncurry insertGlobal) gEnv $ zip (fst <$> methods) fixed'
      -- Save the annotation on the method
      let methods' = map (\((name,Method a b c d e anns f g), ann) -> (name, Method a b c d e (MethodAnnotateRegionSize ann:anns) f g)) $ zip methods fixed'
      
      
      -- Solve the fixpoints
      putStrLn $ "\n# Locals: "
      print $ solveFixpoints dEnv $ eval dEnv $ inlineFixpoints $ analyseMethods 1 gEnv' methods' 
      
      -- Compute the second pass
      let localAnns = (unsafeUnliftTuple 
                    . solveFixpoints dEnv
                    . eval dEnv 
                    $ analyseMethods 1 gEnv' methods')

      let effects = zipWith constrAdd (collectEffects <$> localAnns) (fixHigherOrderApplication <$> localAnns)

      -- Transform the program
      let transformed = uncurry transform <$> zip effects (snd <$> methods')
      let emptyRegs   = collectEmptyRegs <$> transformed
      let cleaned     = uncurry remEmptyRegs <$> zip emptyRegs transformed

      -- Count bounded and unbouned regions
      let finite   = sum $ length <$> filter (not . (== Infty) . snd) <$> filter (not . (== Region RegionGlobal) . fst) <$> M.toList <$> effects
      let infinite = (sum $ length <$> filter (not . (== Region RegionGlobal) . fst) <$> M.toList <$> effects) - finite 

      putStrLn "\n#Effects:"
      print $ effects

      return ((gEnv', finite, infinite), zip (fst <$> methods) cleaned)

{-| When a local region is applied to a higher order function
  we must make said region unbounded. We cannot know the true bound.
  This could also be corrected with a change in region inference.
  TODO: Do not pass c if a \= AApl? May be sound
-}
fixHigherOrderApplication :: Annotation -> Constr
fixHigherOrderApplication = flip go constrBot
  where go (AVar   _  ) c = c
        go (AApl   f x) c = go f . constrJoins $ c : (constrInfty <$> gatherLocals x)
        go (ALam   _ a) c = go a c
        go (ATuple as ) c = constrJoins $ flip go c <$> as
        go (AProj  _ a) c = go a c
        go (AAdd   a b) c = constrJoin (go a c) (go b c)
        go (AJoin  a b) c = constrJoin (go a c) (go b c)
        go (AQuant a  ) c = go a c
        go (AInstn a _) c = go a c
        go (AFix  _ as) c = constrJoins $ flip go c <$> as
        go _ _ = constrBot

----------------------------------------------------------------
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
    moduleDataTypeSorts :: IdMap (Maybe Sort)
    moduleDataTypeSorts = foldl (declDataTypeSort typeEnv) recDSorts (dataTypeBindingGroups $ moduleDataTypes m)
    -- Data type regions
    moduleDataTypeRegions :: IdMap (Maybe Sort)
    moduleDataTypeRegions = foldl (declDataTypeRegions typeEnv) recDSorts (dataTypeBindingGroups $ moduleDataTypes m)
    -- Constructor annotations
    moduleDataTypeConstructors :: IdMap Annotation
    moduleDataTypeConstructors = mapFromList (concat $ declDataTypeConstructors <$> moduleDataTypes m)
    declDataTypeConstructors :: Declaration DataType -> [(Id, Annotation)]
    declDataTypeConstructors dt = makeDataTypeConstructors (declarationName dt `findMap` moduleDataTypeSorts) (declarationValue dt)
    -- Destructor annotations
    moduleDataTypeDestructors :: IdMap [Annotation]
    moduleDataTypeDestructors = mapFromList $ concat $ declDataTypeDestructors <$> moduleDataTypes m
    declDataTypeDestructors :: Declaration DataType -> [(Id, [Annotation])]
    declDataTypeDestructors dt = makeDataTypeDestructors (declarationName dt `findMap` moduleDataTypeSorts) (declarationValue dt)

    -- Environment used for the recursive positions of data types (Unit sort qith quantifications)
    recDSorts :: IdMap (Maybe Sort)
    recDSorts = mapFromList . map makeRecDataTypeSort $ moduleDataTypes m
    makeRecDataTypeSort ::  Declaration DataType -> (Id, Maybe Sort)
    makeRecDataTypeSort decl = (declarationName decl, Just . foldr (const SortQuant) SortUnit . dataTypeQuantors $ declarationValue decl)

----------------------------------------------------------------
-- Check if method can be derived
----------------------------------------------------------------

isDataTypeMethod :: DataTypeEnv -> Type -> Bool  
isDataTypeMethod dEnv (TStrict t)     = isDataTypeMethod dEnv t  
isDataTypeMethod dEnv (TForall _ _ t) = isDataTypeMethod dEnv t  
isDataTypeMethod _    (TVar _)        = False  
isDataTypeMethod dEnv (TAp t1 t2)     = isDataTypeMethod dEnv t1 || isDataTypeMethod dEnv t2    
isDataTypeMethod _    (TCon TConFun)          = False    
isDataTypeMethod _    (TCon (TConTuple _))    = False 
isDataTypeMethod dEnv (TCon (TConDataType name)) = case name `lookupDataType` dEnv of
                                                      Nothing -> True
                                                      Just _  -> False
isDataTypeMethod dEnv (TCon (TConTypeClassDictionary name)) = case (dictionaryDataTypeName name) `lookupDataType` dEnv of
                                                                 Nothing -> True
                                                                 Just _  -> False
