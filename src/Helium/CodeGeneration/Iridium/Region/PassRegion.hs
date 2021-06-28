module Helium.CodeGeneration.Iridium.Region.PassRegion where

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Data.List

import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.BindingGroup

import Helium.CodeGeneration.Iridium.Region.Env
import Helium.CodeGeneration.Iridium.Region.DataType
import Helium.CodeGeneration.Iridium.Region.Generate
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.Evaluate
import Helium.CodeGeneration.Iridium.Region.RegionVar
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Transform
import Helium.CodeGeneration.Iridium.Region.DeadRegion
import Helium.CodeGeneration.Iridium.Region.Utils

import Debug.Trace

passRegion :: NameSupply -> Module -> IO Module
passRegion supply m = do
  let genv = initialEnv m
  let groups = methodBindingGroups $ moduleMethods m

  (_, methods) <- mapAccumLM transformGroup genv groups

  return m{ moduleMethods = concat methods }

initialEnv :: Module -> GlobalEnv
initialEnv m = GlobalEnv typeEnv dataTypeEnv constructorEnv functionEnv
  where
    -- Environment is only used for type synonyms
    typeEnv = TypeEnvironment (mapFromList synonyms) emptyMap emptyMap

    (dataTypeEnv, constructorEnv) = createDataTypeEnv typeEnv $ moduleDataTypes m

    functionEnv :: IdMap (Int, Annotation)
    functionEnv = mapFromList $ methods ++ abstracts

    abstracts :: [(Id, (Int, Annotation))]
    abstracts = abstract <$> moduleAbstractMethods m

    abstract :: Declaration AbstractMethod -> (Id, (Int, Annotation))
    abstract (Declaration name _ _ _ (AbstractMethod tp regionSort _ annotations)) = (name, (regionSortSize regionSort, regionAnnotation tp annotations))

    methods :: [(Id, (Int, Annotation))]
    methods = method <$> moduleMethods m

    method :: Declaration Method -> (Id, (Int, Annotation))
    method (Declaration name _ _ _ (Method tp _ _ _ _ _ _ _)) = (name, (0, top tp))

    top :: Type -> Annotation
    top = ATop . SortFun SortUnit RegionSortUnit LifetimeContextAny . sortOfType dataTypeEnv . typeNormalize typeEnv

    synonyms :: [(Id, Type)]
    synonyms = [(name, tp) | Declaration name _ _ _ (TypeSynonym _ tp) <- moduleTypeSynonyms m]

    regionAnnotation :: Type -> [MethodAnnotation] -> Annotation
    regionAnnotation tp [] = top tp
    regionAnnotation tp (a:as)
      | MethodAnnotateRegion r <- a = r
      | otherwise = regionAnnotation tp as

-- Analyses and transforms a binding group of a single non-recursive function
-- or a group of (mutual) recursive functions.
transformGroup :: GlobalEnv -> BindingGroup Method -> IO (GlobalEnv, [Declaration Method])
transformGroup genv (BindingRecursive [method]) = transformGroup genv (BindingNonRecursive method)
transformGroup genv@(GlobalEnv typeEnv dataTypeEnv constructorEnv globals) (BindingRecursive methods) = do
  putStrLn $ "# Analyse mutual recursive methods " ++ show (map declarationName methods)

  let
    bindings = map (\(Declaration name _ _ _ method@(Method _ _ args _ _ _ _ _)) -> MethodBinding name (assignRegionVarsCount genv method) args) methods
    (methodEnvs, fixpointFunctions) = unzip $ map (generate genv bindings) methods
    sort' = SortTuple $ map (\(_, s, _) -> s) fixpointFunctions
    correctSort (arity, s, ALam _ rs lc a) = (arity, s, ALam sort' rs lc a)
    correctSort _ = error "transformGroup: BindingRecursive: got invalid fixpoint function"
    fixpointFunctions' = map correctSort fixpointFunctions
    regionSort = methodEnvAdditionalRegionSort $ head methodEnvs
    fixpoint = AFixEscape regionSort fixpointFunctions

    correctArityZero' binding (doesEscape, substituteRegionVar, annotation)
      | methodBindingZeroArity binding = 
        ( doesEscape
        , substituteRegionVar
        , simplify dataTypeEnv $ snd $ correctArityZero regionSort (methodBindingArguments binding) annotation
        )
      | otherwise = (doesEscape, substituteRegionVar, snd $ annotationRestrict doesEscape annotation)
    results = zipWith correctArityZero' bindings $ simplifyFixEscape dataTypeEnv fixpoint

    transform' :: Declaration Method -> MethodEnv -> ([Bool], RegionVar -> RegionVar, Annotation) -> ((Id, (Int, Annotation)), Declaration Method)
    transform' decl methodEnv (doesEscape, substituteRegionVar, annotation) =
      ( ( declarationName decl, (regionCount, restricted))
      , decl{ declarationValue = method }
      )
      where
        (regionCount, method, restricted) = transformDead True annotation $ transform methodEnv (methodEnvIsZeroArity methodEnv) substituteRegionVar annotation bindings $ declarationValue decl

    solved :: [(Id, (Int, Annotation))]
    transformed :: [Declaration Method]
    (solved, transformed) = unzip $ zipWith3 transform' methods methodEnvs results

    globals' = foldl' (\globals'' (name, a) -> updateMap name a globals'') globals solved
    genv' = GlobalEnv typeEnv dataTypeEnv constructorEnv globals'

  return (genv', transformed)

transformGroup genv@(GlobalEnv typeEnv dataTypeEnv constructorEnv globals) (BindingNonRecursive method@(Declaration methodName _ _ _ (Method _ _ arguments _ _ _ _ _))) = do
  -- putStrLn $ "# Analyse method " ++ show methodName

  let (methodEnv, fixpointFunction) = generate genv [] method
  let annotation = AFixEscape (methodEnvAdditionalRegionSort methodEnv) [fixpointFunction]
  -- print annotation

  let
    unwrap [x] = x
    unwrap _ = error "Expected list of 1 element"
    (doesEscape, substituteRegionVar, simplified) = unwrap $ simplifyFixEscape dataTypeEnv annotation
  -- putStrLn "Simplified:"
  -- print simplified

  let (isZeroArity, simplified') = correctArityZero (methodEnvAdditionalRegionSort methodEnv) arguments simplified
  let simplified'' = if isZeroArity then simplify dataTypeEnv simplified' else simplified'

  let (_, restricted) = if isZeroArity then (0, simplified'') else annotationRestrict doesEscape simplified

  -- putStrLn "Restricted:"
  -- print doesEscape
  -- print restricted

  let bindings = [MethodBinding methodName 0 arguments]
  let (regionCount, method', restricted') = transformDead False restricted $ transform methodEnv isZeroArity substituteRegionVar restricted bindings $ declarationValue method

  rnfAnnotation restricted' `seq` return ()

  let globals' = updateMap methodName (regionCount, restricted') globals
  let genv' = GlobalEnv typeEnv dataTypeEnv constructorEnv globals'

  return (genv', [method{ declarationValue = method' }])
