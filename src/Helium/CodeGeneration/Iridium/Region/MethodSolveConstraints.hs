-- Converts the constraints of a method to equations and solves them.

module Helium.CodeGeneration.Iridium.Region.MethodSolveConstraints (methodsSolveConstraints, Solution, MethodStateSolution(..)) where

import Data.Maybe
import Data.List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap
import System.IO

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.AnnotationNormalize
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.MethodInitialize
import Helium.CodeGeneration.Iridium.Region.Utils

data MethodStateSolution = MethodStateSolution !(Argument Annotation) ![Maybe Int] !MethodState
type Solution = IdMap MethodStateSolution

instance Show MethodStateSolution where
  show (MethodStateSolution arg preserved state) = "Annotations: " ++ show arg ++ "\nPreserved arguments: " ++ show preserved ++ "\n" ++ show state

methodsSolveConstraints :: Maybe Handle -> EffectEnvironment -> IdMap MethodState -> IO (EffectEnvironment, Solution)
methodsSolveConstraints log env states = do
  equationsUnsolved <- methodsToEquations log env states

  debugLog log "### Solve interprocedural equations on annotation variables"
  debugLog log $ showIntMap equationsUnsolved

  let equations = solveEquations env equationsUnsolved
  debugLog log "Solved:"
  debugLog log $ showIntMap equations

  let
    solveMethod :: Id -> MethodState -> MethodStateSolution
    solveMethod name state =
      MethodStateSolution arguments mapping state
      where
        EffectGlobal _ _ argumentVars = eeLookupGlobal env name
        (mapping, arguments) =
          annotationArgumentRemoveUnusedRegionArguments
          $ fmap (solve equations 0) argumentVars

  let solution = mapMapWithId solveMethod states

  let
    updateAnnotation :: Id -> MethodStateSolution -> EffectEnvironment -> EffectEnvironment
    updateAnnotation name (MethodStateSolution arg _ _) = eeUpdateGlobal name (\(EffectGlobal arity tp _) -> EffectGlobal arity tp arg)

  let env' = foldMapWithId updateAnnotation env solution

  return (env', solution)

solveEquations :: EffectEnvironment -> Equations -> Equations
solveEquations env initialEquations = IntMap.foldr f initialEquations initialEquations
  where
    f :: Equation -> Equations -> Equations
    f (Equation var fixRegions sort _ annotation) equations = IntMap.insert (indexInArgument var) (Equation var FixRegionsNone sort (not True) annotation') equations
      where
        annotation' = annotationNormalize env $ annotationSaturate env $ solve equations 0 annotation

methodsToEquations :: Maybe Handle -> EffectEnvironment -> IdMap MethodState -> IO Equations
methodsToEquations log env methods = do
  equations <- mapM (uncurry $ methodToInterproceduralEquations log env) $ listFromMap methods
  return $ equationsFromList $ concat equations

methodToInterproceduralEquations :: Maybe Handle -> EffectEnvironment -> Id -> MethodState -> IO [Equation]
methodToInterproceduralEquations log env name state = do
  debugLog log $ "### Solve annotation equations for " ++ show name
  argumentSolved <- methodSolveConstraints log env state
  debugLog log $ "Solution:\n" ++ show argumentSolved
  return $ zipFlattenArgumentWithSort equation sort argumentVars argumentSolved
  where
    sort = typeAnnotationSortArgument env tp []
    sortArgRegions = SortArgumentList $ replicate (msRegionCount state) $ SortArgumentMonomorphic SortArgumentRegion
    equation s (AVar var) annotation = Equation var (FixRegionsEscape arity sortArgRegions) (fmap (SortFun sortArgumentEmpty sortArgRegions) s) False annotation
    EffectGlobal arity tp argumentVars = eeLookupGlobal env name

methodSolveConstraints :: Maybe Handle -> EffectEnvironment -> MethodState -> IO (Argument Annotation)
methodSolveConstraints log env state = do
  debugLog log $ "Equations:\n" ++ show equations
  return $ methodAnnotations env bodyAnnotation returnAnnotations (msAdditionalArgumentScope state - 3) (msType state)
  where
    (returnAnnotationList, constraints) = constraintGatherReturns $ msConstraints state

    solve' = solve equations (msAdditionalArgumentScope state)

    returnAnnotations :: SortArgument Sort -> Argument Annotation
    returnAnnotations sort = case returnAnnotationList of
      [] -> ABottom <$ (sortArgumentToArgument 0 sort :: Argument AnnotationVar)
      _ -> foldr1 (zipArgument AJoin) $ map (fmap solve') returnAnnotationList

    (bodyAnnotationsList, equationsList)
      = unzip $ map (constraintToEquations env) constraints
    equations = equationsFromList $ concat equationsList
    bodyAnnotation = case concat bodyAnnotationsList of
      [] -> ABottom
      list -> foldr1 AJoin $ map solve' list

equationsFromList :: [Equation] -> Equations
equationsFromList = IntMap.fromList . map (\eq@(Equation var _ _ _ _) -> (indexInArgument var, eq))

methodAnnotations :: EffectEnvironment -> Annotation -> (SortArgument Sort -> Argument Annotation) -> Int -> Tp -> Argument Annotation
methodAnnotations env annotationBody f functionLambdaCount functionType
  | functionLambdaCount == 0 = consumeForalls functionType annotationGlobal
  | otherwise = consumeForalls functionType $ annotations functionLambdaCount
  where
    annotations :: Int -> Tp -> Argument Annotation
    annotations lambdas (TpApp (TpApp (TpCon TConFun) tArg) tRet) =
      fmap (ALam sortArgAnnotations sortArgRegions)
        $ ArgumentList 
          [ ArgumentValue
            $ ALam (SortArgumentList []) (SortArgumentMonomorphic SortArgumentRegion)
            $ ALam (SortArgumentList []) (SortArgumentList [SortArgumentMonomorphic SortArgumentRegion])
            $ annotationOwn
          , annotationsRest
          ]
      where
        sortArgAnnotations = typeAnnotationSortArgument env tArg []
        sortArgRegions = typeRegionSort env tArg
        argRegions = argumentFlatten $ sortArgumentToArgument 3 sortArgRegions
        regionThunk = variableFromIndices 1 0

        (annotationOwn, annotationsRest)
          | lambdas == 1 =
            -- Last lambda, get the annotation of the body of the method
            ( annotationBody
            , f $ typeAnnotationSortArgument env tRet []
            )
          | otherwise =
            ( ARelation
              $ Outlives (variableFromIndices 2 0) regionThunk
              : map (`Outlives` regionThunk) argRegions
            , consumeForalls tRet $ annotations (lambdas - 1)
            )
    annotations lambdas tp = error $ "methodAnnotation: Illegal case. lambdas = " ++ show lambdas ++ ", type = " ++ show tp

    annotationGlobal :: Tp -> Argument Annotation
    annotationGlobal tp = f (typeAnnotationSortArgument env tp [])

    consumeForalls :: Tp -> (Tp -> Argument Annotation) -> Argument Annotation
    consumeForalls (TpForall tp) a = AForall <$> consumeForalls tp a
    consumeForalls tp a = a tp

constraintGatherReturns :: [Constraint] -> ([Argument Annotation], [Constraint])
constraintGatherReturns constraints =
  ( map (either id (fmap AVar)) returnArgs
  , filter isNotReturn constraints
  )
  where
    isNotReturn (CReturn _) = False
    isNotReturn _ = True
    returnArgs = [arg | CReturn arg <- constraints]

-- SortArgument cannot be SortArgumentList
data Equation = Equation !AnnotationVar !FixRegions !(SortArgument Sort) !Bool !Annotation

instance Show Equation where
  show (Equation var fixRegions sort solved annotation) =
    show var ++ ": " ++ show sort ++ fixRegionsString ++ " = " ++ show annotation ++ solvedString
    where
      solvedString = if solved then " (solved)" else ""
      fixRegionsString = case fixRegions of
        FixRegionsEscape arity s -> " (fix_regions_escape " ++ show arity ++ " " ++ show s ++ ")"
        _ -> ""

constraintToEquations :: EffectEnvironment -> Constraint -> ([Annotation], [Equation])
constraintToEquations _ (CJoin sort left []) =
  ( []
  , zipFlattenArgumentWithSort (\s var _ -> Equation var FixRegionsNone sort False ABottom) sort left left
  )
constraintToEquations _ (CJoin sort left right) =
  ( []
  , zipFlattenArgumentWithSort (\s var def -> Equation var FixRegionsNone s False def) sort left joined
  )
  where
    right' = fmap (either id (fmap AVar)) right
    joined :: Argument Annotation
    joined = foldr1 (zipArgument AJoin) right'
constraintToEquations env (CCall lhs resultAnnotationSort resultAnnotationNames resultRegion target arity additionalRegions arguments kind) =
  ( baseAnnotations
  , zipFlattenArgumentWithSort (\s var def -> Equation var FixRegionsNone s False def) resultAnnotationSort resultAnnotationNames resultAnnotation
  )
  where
    (baseAnnotations, resultAnnotation) =
      apply env targetAnnotation arguments targetArity
        (targetRegionValue : thunkRegions)
        (map (\r -> ArgumentList [ArgumentValue r, ArgumentList []]) thunkRegions ++ [resultRegion])
    (thunkRegions, targetRegionThunk, targetRegionValue, targetArity, targetAnnotation) = case target of
      Right (annotations, regionThunk, regionValue) ->
        (additionalRegions, regionThunk, regionValue, 0, fmap AVar annotations)
      Left name ->
        let
          EffectGlobal targetArity _ annotations = eeLookupGlobal env name
          valueArgumentCount = length (filter isValueArgument arguments) - arity - 1
          (thunkRegions, additionalCallRegions) = splitAt valueArgumentCount additionalRegions
          regionsArgument = ArgumentList $ map ArgumentValue additionalCallRegions
        in
          (thunkRegions, regionGlobal, regionGlobal, targetArity, fmap (\a -> AApp a (ArgumentList []) regionsArgument) annotations)

apply :: EffectEnvironment -> Argument Annotation -> [CallArgument] -> Int -> [RegionVar] -> [Argument RegionVar] -> ([Annotation], Argument Annotation)
apply env annotations [] _ _ _ = ([], annotations)
apply env annotations (CAType tp : args) targetArity parents resultRegions =
  apply env (fmap (`AInstantiate` tp) annotations) args targetArity parents resultRegions
apply env annotations (arg : args) 0 (parent : parents) (resultRegion : resultRegions) =
  ( AApp (AApp annotation (ArgumentList []) (ArgumentValue parent)) (ArgumentList[]) resultRegion
    : restAnnotations
  , restArguments
  )
  where
    (argAnnotation, argRegion) = case arg of
      CALocal argA argR -> (fmap AVar argA, argR)
      CAGlobal argA argR -> (argA, argR)
    ArgumentList [ArgumentValue annotation, annotations'] = fmap app annotations
    app a = AApp a argAnnotation argRegion
    (restAnnotations, restArguments) = apply env annotations' args 0 parents resultRegions
apply env annotations (arg : args) targetArity parents resultRegions = apply env annotations' args (targetArity - 1) parents resultRegions
  where
    (argAnnotation, argRegion) = case arg of
      CALocal argA argR -> (fmap AVar argA, argR)
      CAGlobal argA argR -> (argA, argR)
    ArgumentList [ArgumentValue _, annotations'] = fmap app annotations
    app a = AApp a argAnnotation argRegion

type Equations = IntMap Equation
solve :: Equations -> Int -> Annotation -> Annotation
solve equations initialEquationScope = solve' [] 0 0
  where
    solve' ::
      [Maybe Int] -- Scope, Justs represent the annotation variables that are already unrolled and can thus be referenced by their fixpoint.
      -> Int -- Number of introduced lambdas. Equal to the length of the scope
      -> Int -- Number of introduced foralls.
      -> Annotation
      -> Annotation
    solve' scope lambdaCount forallCount (AVar var)
      | indexBoundLambda var == equationScope lambdaCount = solveVar scope lambdaCount forallCount $ indexInArgument var
      | otherwise = AVar var
    solve' scope lambdaCount forallCount (AFix fixIdentifier fixRegions a1 a2) =
      AFix fixIdentifier fixRegions (solve' scope lambdaCount forallCount a1) (solve' scope lambdaCount forallCount a2)
    solve' scope lambdaCount forallCount (AForall a) = AForall $ solve' scope lambdaCount (forallCount + 1) a
    solve' scope lambdaCount forallCount (ALam argAnnotation argRegion a) =
      ALam argAnnotation argRegion
        $ solve' (Nothing : scope) (lambdaCount + 1) forallCount a
    solve' scope lambdaCount forallCount (AApp a argAnnotation argRegion)
      = AApp a' argAnnotation' argRegion
      where
        a' = solve' scope lambdaCount forallCount a
        argAnnotation' = fmap (solve' scope lambdaCount forallCount) argAnnotation
    solve' scope lambdaCount forallCount (AInstantiate a tp)
      = AInstantiate (solve' scope lambdaCount forallCount a) tp
    solve' scope lambdaCount forallCount (AJoin a1 a2) = AJoin
      (solve' scope lambdaCount forallCount a1)
      (solve' scope lambdaCount forallCount a2)
    solve' scope lambdaCount forallCount (ARelation constraints) = ARelation constraints
    solve' scope lambdaCount forallCount ABottom = ABottom

    solveVar ::
      [Maybe Int] -- Scope, Justs represent the annotation variables that are already unrolled and can thus be referenced by their fixpoint.
      -> Int -- Number of lambdas
      -> Int -- Number of foralls
      -> Int -- Index of variable in the equations
      -> Annotation
    solveVar scope lambdaCount forallCount var = case elemIndex (Just var) scope of
      Just idx -> AVar $ variableFromIndices idx 0
      _ ->
        let
          Equation _ fixRegions sort solved annotation = equations IntMap.! var
          annotation' = solve' (Just var : scope) (lambdaCount + 1) forallCount $ annotationIncrementScope (lambdaCount + 1) forallCount annotation
          annotation'' = AFix Nothing fixRegions ABottom (ALam sort sortArgumentEmpty annotation')
        in
          case sort of
            _ | solved -> annotationIncrementScope lambdaCount forallCount annotation
            SortArgumentMonomorphic s -> annotationSaturateWithSort s annotation''
            _ -> annotation''

    equationScope :: Int -> Int
    equationScope increment = if initialEquationScope == 0 then 0 else initialEquationScope + increment
