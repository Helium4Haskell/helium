module Helium.CodeGeneration.Iridium.RegionSize.PassRegionSize
    (passRegionSize)
where

import Helium.CodeGeneration.Core.TypeEnvironment

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data
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
import Helium.CodeGeneration.Iridium.RegionSize.Type

import Data.List (intercalate)
import Data.Either (rights, lefts)
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

    ((_, finite, infinite), methods) <- mapAccumLM (analyseGroup (stringFromId $ moduleName m)) (gEnv,0,0) groups
    putStrLn $ "Finite:   " ++ show finite
    putStrLn $ "Infinite: " ++ show infinite

    return m{moduleMethods = concat methods}


{- Analyses a binding group of a single non-recursive function
   or a group of (mutual) recursive functions.
-} 
analyseGroup :: (GlobalEnv, Int, Int) -> BindingGroup Method -> IO ((GlobalEnv, Int, Int), [Declaration Method])
-- Recurisve bindings
analyseGroup (gEnv, finite, infinite) (BindingRecursive bindings) = do
  let methods = map (\(Declaration methodName _ _ _ method) -> (methodName, method)) bindings

  ((gEnv', finite2, infinite2), transformeds) <- temp gEnv methods

  let bindings' = map (\(decl, (_,transformed)) -> decl{declarationValue=transformed}) $ zip bindings transformeds
  return ((gEnv', finite+finite2, infinite+infinite2)
         , bindings')
-- Non recursive binding
analyseGroup (gEnv, finite, infinite) (BindingNonRecursive decl@(Declaration methodName _ _ _ method)) = do
  ((gEnv', finite2, infinite2), [(_,transformed)]) <- temp gEnv [(methodName,method)]

  return ((gEnv', finite+finite2, infinite+infinite2)
         , [decl{ declarationValue = transformed }])


temp ::  GlobalEnv -> [(Id,Method)] -> IO ((GlobalEnv, Int, Int), [(Id,Method)])
temp gEnv methods = do
    let hasDicts = foldr (||) False (isDataTypeMethod <$> methodType . snd <$> methods)
    if hasDicts
    then do
      let gEnv' = foldr (uncurry insertGlobal) gEnv $ zip (fst <$> methods) (flip ATop constrBot . methodSortAssign gEnv . snd <$> methods)
      return ((gEnv', 0, 0), methods)
    else do
      let dEnv = globDataEnv gEnv

      -- Generate the annotations     
      putStrLn $ "\n# Analyse methods:\n" ++ (intercalate "\n" $ map (show.fst) methods)
      let mAnn  = analyseMethods 0 gEnv methods
      print mAnn

      -- Simplify the generated annotation
      let simpl = inlineFixpoints $ eval dEnv mAnn
      putStrLn $ "\n# Simplified: "
      print simpl'

      -- Solve the fixpoints
      let fixed = solveFixpoints dEnv simpl'
      -- Check if the resulting annotation is well-sroted
      putStrLn $ "\n# Fixpoint: "
      print fixed 
      let sorts = sort dEnv fixed

      fixed' <- case sorts of
              Left  s -> do
                putStrLn ""
                putStrLn s
                rsError $ "Wrong sort"
              Right _ -> return $ unsafeUnliftTuple fixed

      -- Fix the annotations of zero arity definitions
      let zerod = uncurry fixZeroArity <$> zip methods fixed'
      putStrLn $ "\n# Zerod: "
      print zerod 

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

      -- Count regions
      let finite   = sum $ length <$> filter (not . (== Infty) . snd) <$> filter (not . (== Region RegionGlobal) . fst) <$> M.toList <$> effects
      let infinite = (sum $ length <$> filter (not . (== Region RegionGlobal) . fst) <$> M.toList <$> effects) - finite 

      -- Do the program transformation & remove empty regions
      let transformed = uncurry transform <$> zip effects (snd <$> methods')
      let emptyRegs   = collectEmptyRegs <$> transformed
      let cleaned     = uncurry remEmptyRegs <$> zip emptyRegs transformed

      putStrLn "\n#Effects:"
      print $ effects

      return ((gEnv', finite, infinite), zip (fst <$> methods) cleaned)

{-| Fix problems arising from zero arity functions
  Assigns the global regions to the return regions and additional regions.
-}
fixZeroArity :: (Id, Method) -> Annotation -> Annotation
fixZeroArity (_, Method _ aRegs args _ rRegs _ _ _) ann =
  case length $ rights args of
    0 -> let aplARegs = AApl ann $ regionVarsToGlobal aRegs
             newQuantIndexes = reverse $ TVar <$> [0..(length $ lefts args)-1]
             quants a = foldr (const AQuant) a (lefts args)
             aplTypes = foldl AInstn aplARegs newQuantIndexes
             aplRRegs = AApl aplTypes $ regionVarsToGlobal rRegs
         in ALam SortUnit $ eval emptyDEnv $ quants $ AProj 0 aplRRegs
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
    declDataTypeSorts = mapFromList . concat $ map declDataTypeSorts' (dataTypeBindingGroups $ moduleDataTypes m)

    declDataTypeSorts' :: BindingGroup DataType -> [(Id, Sort)]
    declDataTypeSorts' (BindingNonRecursive decl) = [(declarationName decl, dataTypeSort typeEnv recDEnv $ declarationValue decl)]
    declDataTypeSorts' (BindingRecursive decls) = concat $ declDataTypeSorts' <$> BindingNonRecursive <$> decls

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
-- Data type sort discovery
----------------------------------------------------------------

-- | Find sort for datatype
dataTypeSort :: TypeEnvironment -> DataTypeEnv -> DataType -> Sort
dataTypeSort tEnv dEnv dt@(DataType structs) = foldr (const SortQuant) (SortTuple . concat $ dataStructSort tEnv dEnv <$> structs) (dataTypeQuantors dt)

dataStructSort :: TypeEnvironment -> DataTypeEnv -> Declaration DataTypeConstructorDeclaration -> [Sort]
dataStructSort tEnv dEnv (Declaration _ _ _ _ (DataTypeConstructorDeclaration ty _)) =
  let (args, _) = typeExtractFunction $ typeRemoveQuants ty
  in sortAssign dEnv <$> typeNormalize tEnv <$> args -- TODO: We remove the quantifications here?

-- | Find region assignment for datatype
dataTypeRegions :: TypeEnvironment -> DataTypeEnv -> DataType -> Sort
dataTypeRegions tEnv dEnv dt@(DataType structs) = foldr (const SortQuant) (SortTuple . concat $ dataStructRegions tEnv dEnv <$> structs) (dataTypeQuantors dt)

dataStructRegions :: TypeEnvironment -> DataTypeEnv -> Declaration DataTypeConstructorDeclaration -> [Sort]
dataStructRegions tEnv dEnv (Declaration _ _ _ _ (DataTypeConstructorDeclaration ty _)) =
  let (args, _) = typeExtractFunction $ typeRemoveQuants ty
  in regionAssign dEnv <$> typeNormalize tEnv <$> args -- TODO: We remove the quantifications here?

----------------------------------------------------------------
-- Temporary methods
----------------------------------------------------------------

isDataTypeMethod :: Type -> Bool  
isDataTypeMethod (TStrict t)     = isDataTypeMethod t  
isDataTypeMethod (TForall _ _ t) = isDataTypeMethod t  
isDataTypeMethod (TVar _)        = False  
isDataTypeMethod (TAp t1 t2)     = isDataTypeMethod t1 || isDataTypeMethod t2    
isDataTypeMethod (TCon TConFun)          = False    
isDataTypeMethod (TCon (TConTuple _))    = False  
isDataTypeMethod (TCon (TConDataType _)) = True 
isDataTypeMethod (TCon (TConTypeClassDictionary _)) = True
