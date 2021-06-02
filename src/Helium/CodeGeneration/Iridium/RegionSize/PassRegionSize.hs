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
import Data.Either (rights)
import qualified Data.Map as M 

-- | Infer the size of regions
passRegionSize :: NameSupply -> Module -> IO Module
passRegionSize _ m = do 
  if  (((stringFromId $ moduleName m) == "LvmLang"      && False)
    || ((stringFromId $ moduleName m) == "HeliumLang"   && False) 
    || ((stringFromId $ moduleName m) == "PreludePrim"  && False)
    || ((stringFromId $ moduleName m) == "Prelude"      && False)
    || ((stringFromId $ moduleName m) == "LvmException" && False))
  then do
    return m
  else do
    let gEnv = initialGEnv m
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

  ((gEnv', finite2, infinite2), transformeds) <- analysis gEnv methods

  let bindings' = map (\(decl, (_,transformed)) -> decl{declarationValue=transformed}) $ zip bindings transformeds
  return ((gEnv', finite+finite2, infinite+infinite2)
         , bindings')
-- Non recursive binding
analyseBindingGroup (gEnv, finite, infinite) (BindingNonRecursive decl@(Declaration methodName _ _ _ method)) = do
  ((gEnv', finite2, infinite2), [(_,transformed)]) <- analysis gEnv [(methodName,method)]

  return ((gEnv', finite+finite2, infinite+infinite2)
         , [decl{ declarationValue = transformed }])


-- | Run the analysis on a group of methods
analysis ::  GlobalEnv -> [(Id,Method)] -> IO ((GlobalEnv, Int, Int), [(Id,Method)])
analysis gEnv methods = do
    let canDerive = foldr (&&) True (not.isDataTypeMethod . typeNormalize (globTypeEnv gEnv) . methodType . snd <$> methods)

    putStrLn $ "\n# Analyse methods:\n" ++ (intercalate "\n" $ map (show.fst) methods)
    putStrLn $ "\n# Can derive: " ++ show canDerive ++ "\n" ++ (show $ typeNormalize (globTypeEnv gEnv) . methodType . snd <$> methods)

    if not canDerive
    then do
      -- | Insert top for bad methods
      -- TODO: Does not transform program
      let gEnv' = foldr (uncurry insertGlobal) gEnv $ zip (fst <$> methods) (flip ATop constrBot . methodSortAssign gEnv . snd <$> methods)
      return ((gEnv', 0, 0), methods)
    else do
      let dEnv = globDataEnv gEnv

      -- Generate the annotations     
      let mAnn  = analyseMethods 0 gEnv methods
      let simpl = inlineFixpoints $ eval dEnv mAnn
      let fixed = solveFixpoints dEnv simpl
      let sorts = sort dEnv fixed

      putStrLn $ "\n# Derived annotation: "
      print mAnn
      
      putStrLn $ "\n# Simplified: "
      print simpl

      -- Solve the fixpoints
      putStrLn $ "\n# Fixpoint: "
      print fixed 

      -- Check if the resulting annotation is well-sroted
      fixed' <- case sorts of
              Left  s -> do
                putStrLn ""
                putStrLn s
                rsError $ "Wrong sort"
              Right _ -> return $ unsafeUnliftTuple fixed
      let zerod = uncurry fixZeroArity <$> zip methods fixed'
      

      -- Update the global environment with the found annotations
      let gEnv' = foldr (uncurry insertGlobal) gEnv $ zip (fst <$> methods) zerod
      -- Save the annotation on the method
      let methods' = map (\((name,Method a b c d e anns f g), ann) -> (name, Method a b c d e (MethodAnnotateRegionSize ann:anns) f g)) $ zip methods zerod
      -- Compute the second pass
      let effects = collectEffects 
                <$> (unsafeUnliftTuple 
                    . eval dEnv
                    . solveFixpoints dEnv
                    $ analyseMethods 1 gEnv' methods')
            
      -- Transform the program
      let transformed = uncurry transform <$> zip effects (snd <$> methods')
      let emptyRegs   = collectEmptyRegs <$> transformed
      let cleaned     = uncurry remEmptyRegs <$> zip emptyRegs transformed

      -- Count bounded and unbouned regions
      let finite   = sum $ length <$> filter (not . (== Infty) . snd) <$> filter (not . (== Region RegionGlobal) . fst) <$> M.toList <$> effects
      let infinite = (sum $ length <$> filter (not . (== Region RegionGlobal) . fst) <$> M.toList <$> effects) - finite 

      -- Fix the annotations of zero arity definitions
      putStrLn $ "\n# Zerod: "
      print zerod 

      putStrLn "\n#Effects:"
      print $ effects

      return ((gEnv', finite, infinite), zip (fst <$> methods) cleaned)

{-| Fix problems arising from zero arity functions
  Assigns the global regions to the additional regions andintroduces
-}
fixZeroArity :: (Id, Method) -> Annotation -> Annotation
fixZeroArity (_, Method _ aRegs args _ _ _ _ _) ann =
  case length $ rights args of
    0 -> ALam SortUnit (eval emptyDEnv $ AApl ann (regionVarsToGlobal aRegs))
    _ -> ann 

-- | Assign a sort to a method  
methodSortAssign :: GlobalEnv -> Method -> Sort  
methodSortAssign (GlobalEnv tEnv _ dEnv) = SortLam SortUnit . sortAssign dEnv . typeNormalize tEnv . methodType   

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
    dataTypeEnv = DataTypeEnv declDataTypeSorts declDataTypeRegions dataTypeConstructors dataTypeDestructors

    -- Data type sorts
    declDataTypeSorts :: IdMap Sort
    -- TODO: map is not really OK, we should foldl to get the sorts of previous dts
    declDataTypeSorts = mapFromList . concat $ map declDataTypeSorts' (dataTypeBindingGroups $ moduleDataTypes m)

    declDataTypeSorts' :: BindingGroup DataType -> [(Id, Sort)]
    declDataTypeSorts' (BindingNonRecursive decl) = [(declarationName decl, dataTypeSort typeEnv recDEnv $ declarationValue decl)]
    declDataTypeSorts' (BindingRecursive decls)   = concat $ declDataTypeSorts' . BindingNonRecursive <$> decls

    -- Data type regions
    declDataTypeRegions :: IdMap Sort
    declDataTypeRegions = mapFromList . concat $ map declDataTypeRegions' (dataTypeBindingGroups $ moduleDataTypes m)

    declDataTypeRegions' :: BindingGroup DataType -> [(Id, Sort)]
    declDataTypeRegions' (BindingNonRecursive decl) = [(declarationName decl, dataTypeRegions typeEnv recDEnv $ declarationValue decl)]
    declDataTypeRegions' (BindingRecursive decls) = concat $ declDataTypeRegions' <$> BindingNonRecursive <$> decls

    -- Constructor annotations
    dataTypeConstructors :: IdMap Annotation
    dataTypeConstructors = mapFromList (concat $ dataTypeConstructors' <$> moduleDataTypes m)
    
    dataTypeConstructors' :: Declaration DataType -> [(Id, Annotation)]
    dataTypeConstructors' dt = makeDataTypeConstructors (declarationName dt `findMap` declDataTypeSorts) (declarationValue dt)
    
    -- Destructor annotations
    dataTypeDestructors :: IdMap [Annotation]
    dataTypeDestructors = mapFromList $ concat $ dataTypeDestructors' <$> moduleDataTypes m
    
    dataTypeDestructors' :: Declaration DataType -> [(Id, [Annotation])]
    dataTypeDestructors' dt = makeDataTypeDestructors (declarationName dt `findMap` declDataTypeSorts) (declarationValue dt)


    -- Environment used for the recursive positions of data types
    recDEnv :: DataTypeEnv
    recDEnv = let recSorts = mapFromList . map makeRecDataTypeSort $ moduleDataTypes m
              in DataTypeEnv recSorts recSorts emptyMap emptyMap

    makeRecDataTypeSort ::  Declaration DataType -> (Id, Sort)
    makeRecDataTypeSort decl = (declarationName decl, foldr (const SortQuant) SortUnit . dataTypeQuantors $ declarationValue decl)

----------------------------------------------------------------
-- Check if method can be derived
----------------------------------------------------------------

isDataTypeMethod :: Type -> Bool  
isDataTypeMethod (TStrict t)     = isDataTypeMethod t  
isDataTypeMethod (TForall _ _ t) = isDataTypeMethod t  
isDataTypeMethod (TVar _)        = False  
isDataTypeMethod (TAp t1 t2)     = isDataTypeMethod t1 || isDataTypeMethod t2    
isDataTypeMethod (TCon TConFun)          = False    
isDataTypeMethod (TCon (TConTuple _))    = False 
isDataTypeMethod (TCon (TConDataType name)) = case stringFromId name of
                                                "Int"  -> False
                                                "Char" -> False
                                                "Bool" -> False
                                                "Either" -> False
                                                "Maybe"  -> False
                                                --"[]"   -> False
                                                _ -> True
isDataTypeMethod (TCon (TConTypeClassDictionary _)) = True
