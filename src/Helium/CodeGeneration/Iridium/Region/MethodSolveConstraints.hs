-- Converts the constraints of a method to equations and solves them.

module Helium.CodeGeneration.Iridium.Region.MethodSolveConstraints where

import Data.Maybe
import Data.List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.AnnotationNormalize
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.MethodInitialize

data MethodSolveResult = MethodSolveResult
  { resAnnotation :: !(Argument Annotation)
  , resPreservedArguments :: ![Bool]
  }

methodsSolveConstraints :: EffectEnvironment -> Int -> IdMap MethodState -> (EffectEnvironment, IdMap MethodState)
methodsSolveConstraints = undefined

methodsAnnotationMap :: EffectEnvironment -> Int -> IdMap MethodState -> IntMap Annotation
methodsAnnotationMap env annotationCount methods = IntMap.map (\(Equation _ _ a) -> a) equations'
  where
    equations = methodsToEquations env methods
    equations' = foldl (solveVariable env) equations $ map AnnotationVar [0 .. annotationCount - 1]

solveVariable :: EffectEnvironment -> Equations -> AnnotationVar -> Equations
solveVariable env equations var@(AnnotationVar idx) = equations'
  where
    annotation = annotationNormalize env $ solve equations 0 $ AVar var
    equations' = IntMap.adjust f idx equations
    f (Equation v s _) = Equation v s annotation

methodsToEquations :: EffectEnvironment -> IdMap MethodState -> Equations
methodsToEquations env methods
  = equationsFromList
  $ concat
  $ map (uncurry $ methodToInterproceduralEquations env)
  $ listFromMap methods

methodToInterproceduralEquations :: EffectEnvironment -> Id -> MethodState -> [Equation]
methodToInterproceduralEquations env name state = zipFlattenArgumentWithSort equation sort argumentVars argumentSolved
  where
    sort = typeAnnotationSortArgument env tp []
    equation s (AVar var) annotation = Equation var s annotation
    EffectGlobal _ tp argumentVars = eeLookupGlobal env name
    argumentSolved = methodSolveConstraints env state

methodSolveConstraints :: EffectEnvironment -> MethodState -> Argument Annotation
methodSolveConstraints env state = methodAnnotations env bodyAnnotation returnAnnotations (msAdditionalArgumentScope state) (msType state)
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
equationsFromList = IntMap.fromList . map (\eq@(Equation var _ _) -> (indexInArgument var, eq))

methodAnnotations :: EffectEnvironment -> Annotation -> (SortArgument Sort -> Argument Annotation) -> Int -> Tp -> Argument Annotation
methodAnnotations env annotationBody f functionLambdaCount functionType
  | functionLambdaCount == 0 = consumeForalls functionType annotationGlobal
  | otherwise = consumeForalls functionType $ annotations functionLambdaCount
  where
    annotations :: Int -> Tp -> Argument Annotation
    annotations lambdas (TpForall tp) = fmap AForall $ annotations lambdas tp
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
        sortArgAnnotations@(SortArgumentList [_, sortArgAnnotationsRest]) = typeAnnotationSortArgument env tArg [] 
        sortArgRegions = typeRegionSort env tArg
        argRegions = argumentFlatten $ sortArgumentToArgument 3 sortArgRegions
        regionThunk = variableFromIndices 1 0

        (annotationOwn, annotationsRest)
          | lambdas == 1 =
            -- Last lambda, get the annotation of the body of the method
            ( annotationBody
            , f sortArgAnnotationsRest
            )
          | otherwise =
            ( ARelation
              $ Outlives (variableFromIndices 2 0) regionThunk
              : map (`Outlives` regionThunk) argRegions
            , annotations (lambdas - 1) tRet
            )

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
data Equation = Equation !AnnotationVar !(SortArgument Sort) !Annotation

instance Show Equation where
  show (Equation var sort annotation) = show var ++ ": " ++ show sort ++ " = " ++ show annotation

constraintToEquations :: EffectEnvironment -> Constraint -> ([Annotation], [Equation])
constraintToEquations _ (CJoin sort left []) =
  ( []
  , zipFlattenArgumentWithSort (\s var _ -> Equation var sort ABottom) sort left left
  )
constraintToEquations _ (CJoin sort left right) =
  ( []
  , zipFlattenArgumentWithSort (flip Equation) sort left joined
  )
  where
    right' = fmap (either id (fmap AVar)) right
    joined :: Argument Annotation
    joined = foldr1 (zipArgument AJoin) right'
constraintToEquations env (CCall lhs resultAnnotationSort resultAnnotationNames resultRegion target arity additionalRegions arguments kind) =
  ( baseAnnotations
  , zipFlattenArgumentWithSort (flip Equation) resultAnnotationSort resultAnnotationNames resultAnnotation
  )
  where
    (baseAnnotations, resultAnnotation) =
      apply env targetAnnotation arguments
        (targetRegionValue : thunkRegions)
        (map (\r -> ArgumentList [ArgumentValue r, ArgumentList []]) thunkRegions ++ [resultRegion])
    (thunkRegions, targetRegionThunk, targetRegionValue, targetArity, targetAnnotation) = case target of
      Right (annotations, regionThunk, regionValue) ->
        (additionalRegions, regionThunk, regionValue, 0, fmap AVar annotations)
      Left name ->
        let
          EffectGlobal arity _ annotations = eeLookupGlobal env name
          (thunkRegions, additionalCallRegions) = splitAt arity additionalRegions
          regionsArgument = ArgumentList $ map ArgumentValue additionalCallRegions
        in
          (thunkRegions, regionGlobal, regionGlobal, arity, fmap (\a -> AApp a (ArgumentList []) regionsArgument) annotations)

apply :: EffectEnvironment -> Argument Annotation -> [CallArgument] -> [RegionVar] -> [Argument RegionVar] -> ([Annotation], Argument Annotation)
apply env annotations [] _ _ = ([], annotations)
apply env annotations (CAType tp : args) parents resultRegions =
  apply env (fmap (`AInstantiate` tp) annotations) args parents resultRegions
apply env annotations (arg : args) (parent : parents) (resultRegion : resultRegions) =
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
    (restAnnotations, restArguments) = apply env annotations' args parents resultRegions

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
          Equation _ sort annotation = equations IntMap.! var
          annotation' = solve' (Just var : scope) (lambdaCount + 1) forallCount $ annotationIncrementScope lambdaCount forallCount annotation
        in
          AFix Nothing FixRegionsNone ABottom (ALam sort sortArgumentEmpty annotation')

    equationScope :: Int -> Int
    equationScope increment = if initialEquationScope == 0 then 0 else initialEquationScope + increment
