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
  show (MethodStateSolution arg preserved state) = "  Annotations: " ++ show arg ++ "\n  Preserved arguments: " ++ show preserved ++ "\n" ++ show state

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
        (mapping, arguments) = annotationArgumentRemoveUnusedRegionArguments
          $ argumentVars >>= f
        f (AVar var)
          | indexBoundLambda var == 0 = let Just (Equation _ _ _ True a) = IntMap.lookup (indexInArgument var) equations in a
        f a = ArgumentValue a

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
    f (Equation var fixRegions sort False annotation) equations
      | not $ sortCompare sort $ annotationArgumentCheckSort env [] (replicate 20 []) annotation' = error "Normalized annotation has sort error"
      | otherwise = IntMap.insert (indexInArgument var) (Equation var FixRegionsNone sort True annotation') equations
      where
        annotation'
          | not $ sortCompare sort $ annotationArgumentCheckSort env [] (replicate 20 []) (annotation >>= solve equations 0)
            = error $ "Illegal annotation generated:\n" -- ++ show sort ++ "\n" ++ show (annotationArgumentCheckSort env [] [] (annotation >>= solve equations 0))
          | otherwise = snd <$> annotationArgumentNormalize env [] sort (solve equations 0 $ AVar var)

methodsToEquations :: Maybe Handle -> EffectEnvironment -> IdMap MethodState -> IO Equations
methodsToEquations log env methods = do
  equations <- mapM (uncurry $ methodToInterproceduralEquations log env) $ listFromMap methods
  return $ equationsFromList $ concat equations

methodToInterproceduralEquations :: Maybe Handle -> EffectEnvironment -> Id -> MethodState -> IO [Equation]
methodToInterproceduralEquations log env name state = do
  debugLog log $ "### Solve annotation equations for " ++ show name
  argumentSolved <- methodSolveConstraints log env state
  debugLog log $ "Solution:\n" ++ show argumentSolved
  if msArity state == 0 then
    return
      [Equation methodVar (FixRegionsEscape arity sortArgRegions) (SortFun argumentEmpty sortArgRegions RegionDirectionAny <$> sort) False
        $ (\a -> ALam argumentEmpty sortArgRegions RegionDirectionAny $ AApp (ALam argumentEmpty sortArgRegions RegionDirectionAny a) argumentEmpty (ArgumentList $ replicate regionCount $ ArgumentValue regionGlobal) RegionDirectionAny) <$> argumentSolved]
  else
    return
      [Equation methodVar (FixRegionsEscape arity sortArgRegions) (SortFun argumentEmpty sortArgRegions RegionDirectionAny <$> sort) False $ ALam argumentEmpty sortArgRegions RegionDirectionAny <$> argumentSolved]
  where

    {- removeAdditionalRegionsIfGlobal a
      | msArity state == 0 = ALam argumentEmpty (ArgumentList $ replicate (msRegionCount state) $ ArgumentValue SortArgumentRegionMonomorphic)
          $ AApp a argumentEmpty (ArgumentList $ replicate (msRegionCount state) $ ArgumentValue regionGlobal)
      | otherwise = a -}


    sort = typeAnnotationSortArgument env tp []
    regionCount = msRegionCount state
    sortArgRegions = ArgumentList $ replicate regionCount $ ArgumentValue SortArgumentRegionMonomorphic
    EffectGlobal arity tp (ArgumentValue (AVar methodVar)) = eeLookupGlobal env name

methodSolveConstraints :: Maybe Handle -> EffectEnvironment -> MethodState -> IO (Argument Annotation)
methodSolveConstraints log env state = do
  debugLog log $ "Equations:\n" ++ show equations
  return $ methodAnnotations env bodyAnnotation returnAnnotations (msRegionCount state) (msArity state) (msType state) (msReturnType state)
  where
    (returnAnnotationList, constraints) = constraintGatherReturns $ msConstraints state

    solve' a = {-annotationRemoveUnusedFixpoints <$>-} solve equations (msAdditionalArgumentScope state) a

    returnAnnotations :: Argument Sort -> Argument Annotation
    returnAnnotations sort = case returnAnnotationList of
      [] -> ABottom <$ (sortArgumentToArgument 0 sort :: Argument AnnotationVar)
      _ -> joinArguments $ map (>>= solve') returnAnnotationList

    (bodyAnnotationsList, equationsList)
      = unzip $ map (constraintToEquations env) constraints
    equations = equationsFromList $ concat equationsList
    bodyAnnotation =
      foldr AJoin (ARelation $ relationToConstraints $ msRelation state) [a' | a <- concat bodyAnnotationsList, let ArgumentValue a' = solve' a] 

equationsFromList :: [Equation] -> Equations
equationsFromList = IntMap.fromList . map (\eq@(Equation var _ _ _ _) -> (indexInArgument var, eq))

methodAnnotations :: EffectEnvironment -> Annotation -> (Argument Sort -> Argument Annotation) -> Int -> Int -> Tp -> Tp -> Argument Annotation
methodAnnotations env annotationBody f additionalRegions functionLambdaCount functionType returnType
  | functionLambdaCount == 0 = consumeForalls functionType $ const $ addInstantiations 0 returnType <$> annotationIncrementScope (-2) 0 <$> annotationGlobal
  | otherwise = consumeForalls functionType $ annotations functionLambdaCount
  where
    annotations :: Int -> Tp -> Argument Annotation
    annotations lambdas (TpApp (TpApp (TpCon TConFun) tArg) tRet) =
      fmap (ALam sortArgAnnotations sortArgRegions RegionDirectionAny)
        $ ArgumentList 
          [ ArgumentValue
            $ ALam argumentEmpty (ArgumentValue SortArgumentRegionMonomorphic) RegionDirectionAny
            $ ALam argumentEmpty sortRegionOwn RegionDirectionOutlives
            $ annotationOwn
          , annotationsRest
          ]
      where
        sortArgAnnotations = typeAnnotationSortArgument env tArg []
        sortArgRegions = typeRegionSort env $ tpNotStrict tArg
        argRegions = argumentFlatten $ sortArgumentToArgument 3 sortArgRegions
        regionThunk = variableFromIndices 1 0

        (annotationOwn, sortRegionOwn, annotationsRest)
          | lambdas == 1 =
            -- Last lambda, get the annotation of the body of the method
            ( addInstantiations 0 returnType $ annotationBody
            , typeRegionSort env (tpStrict tRet)
            , addInstantiations 0 returnType <$> annotationIncrementScope (-2) 0 <$> f (typeAnnotationSortArgument env returnType [])
            )
          | otherwise =
            ( ARelation
              $ Outlives (variableFromIndices 2 0) regionThunk
              : map (`Outlives` regionThunk) argRegions
              -- For the first argument, add outlives constraints for the additional region arguments (with scope 4)
              ++ (if functionLambdaCount == lambdas then map ((`Outlives` regionThunk) . variableFromIndices 4) [0 .. additionalRegions - 1] else [])
            , (ArgumentList [ArgumentValue SortArgumentRegionMonomorphic, argumentEmpty])
            , consumeForalls tRet $ annotations (lambdas - 1)
            )
    annotations lambdas tp = error $ "methodAnnotation: Illegal case. lambdas = " ++ show lambdas ++ ", type = " ++ show tp

    annotationGlobal :: Argument Annotation
    annotationGlobal = f (typeAnnotationSortArgument env returnType [])

    consumeForalls :: Tp -> (Tp -> Argument Annotation) -> Argument Annotation
    consumeForalls (TpForall tp) a = AForall <$> consumeForalls tp a
    consumeForalls tp a = a tp

    -- When analyzing a function whose return type starts with a forall quantifier, we will add those forall quantifiers twice:
    -- First in `consumeForalls`, second in the body (as body has sort Psi(returnType)).
    -- This does not occur often luckily. We fix this by adding instantiations to the annotation.
    -- Example:
    -- Return type has two quantifiers. Then we will generate an annotation of the form:
    -- forall. forall. ((forall. forall. body) { a_1 } { a_0 }
    addInstantiations :: Int -> Tp -> Annotation -> Annotation
    addInstantiations forallIndex (TpForall tp) a = AInstantiate (addInstantiations (forallIndex + 1) tp a) (TpVar $ TypeVar forallIndex)
    addInstantiations _ _ a = a

constraintGatherReturns :: [Constraint] -> ([Argument Annotation], [Constraint])
constraintGatherReturns constraints =
  ( returnArgs
  , filter isNotReturn constraints
  )
  where
    isNotReturn (CReturn _) = False
    isNotReturn _ = True
    returnArgs = [arg | CReturn arg <- constraints]

data Equation = Equation !AnnotationVar !FixRegions !(Argument Sort) !Bool !(Argument Annotation)

instance Show Equation where
  show (Equation var fixRegions sort solved annotation) =
    show var ++ fixRegionsString ++ ": " ++ show sort ++ "\n    = " ++ show annotation ++ solvedString
    where
      solvedString = if solved then " (solved)" else ""
      fixRegionsString = case fixRegions of
        FixRegionsEscape arity s -> " (fix_regions_escape " ++ show arity ++ " " ++ show s ++ ")"
        _ -> ""

joinArguments :: [Argument Annotation] -> Argument Annotation
joinArguments [] = ArgumentValue ABottom
joinArguments [a] = a
joinArguments args
  | null lists = ArgumentValue $ foldr1 AJoin values
  | null values = ArgumentList args'
  | otherwise = ArgumentValue $ foldr1 AJoin values `AJoin` ATuple (map argumentToAnnotation args')
  where
    values = [value | ArgumentValue value <- args]
    lists = [list | ArgumentList list <- args]
    args' = fmap joinArguments $ transpose lists

constraintToEquations :: EffectEnvironment -> Constraint -> ([Annotation], [Equation])
constraintToEquations _ (CJoin sort left []) =
  ( []
  , [Equation left FixRegionsNone sort False $ ArgumentValue ABottom]
  )
constraintToEquations _ (CJoin sort left [right]) =
  ( []
  , [Equation left FixRegionsNone sort False right]
  )
constraintToEquations _ (CJoin sort left right) = ([], [Equation left FixRegionsNone sort False $ joinArguments right])
constraintToEquations env c@(CCall lhs resultAnnotationSort resultAnnotationVar resultRegion target arity additionalRegions arguments kind) =
  ( baseAnnotations
  , [Equation resultAnnotationVar FixRegionsNone resultAnnotationSort False resultAnnotation]
  )
  where
    resultRegion' = case resultRegion of
      ArgumentList [_, r1, r2] -> ArgumentList [r1, r2]
      ArgumentList [r1, r2] -> ArgumentList [r1, r2]
    (baseAnnotations, resultAnnotation) =
      apply env targetAnnotation arguments targetArity
        (targetRegionValue : thunkRegions)
        (map (\r -> ArgumentList [ArgumentValue r, ArgumentList []]) thunkRegions ++ [resultRegion'])
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
          (thunkRegions, regionGlobal, regionGlobal, targetArity, fmap (\a -> AApp a (ArgumentList []) regionsArgument RegionDirectionAny) annotations)

apply :: EffectEnvironment -> Argument Annotation -> [CallArgument] -> Int -> [RegionVar] -> [Argument RegionVar] -> ([Annotation], Argument Annotation)
apply env annotations [] _ _ _ = ([], annotations)
apply env annotations (CAType tp : args) targetArity parents resultRegions =
  apply env (fmap (`AInstantiate` tp) annotations) args targetArity parents resultRegions
apply env annotations (arg : args) 0 (parent : parents) (resultRegion : resultRegions) =
  ( AApp (AApp annotation argumentEmpty (ArgumentValue parent) RegionDirectionAny) argumentEmpty resultRegion RegionDirectionOutlives
    : restAnnotations
  , restArguments
  )
  where
    (argAnnotation, argRegion) = case arg of
      CALocal argA argR -> (fmap AVar argA, argR)
      CAGlobal argA argR -> (argA, argR)
    (annotation, annotations') = case fmap app annotations of
      ArgumentList [ArgumentValue a, as] -> (a, as)
      ArgumentValue a -> (AProject a 0, ArgumentValue $ AProject a 1)
    app a = AApp a argAnnotation (regionArgumentWithThunk argRegion) RegionDirectionAny
    (restAnnotations, restArguments) = apply env annotations' args 0 parents resultRegions
apply env annotations (arg : args) targetArity parents resultRegions = apply env annotations' args (targetArity - 1) parents resultRegions
  where
    (argAnnotation, argRegion) = case arg of
      CALocal argA argR -> (fmap AVar argA, argR)
      CAGlobal argA argR -> (argA, argR)
    annotations' = case fmap app annotations of
      ArgumentList [ArgumentValue _, as] -> as
      ArgumentValue a -> ArgumentValue $ AProject a 1
    app a = AApp a argAnnotation (regionArgumentWithThunk argRegion) RegionDirectionAny

regionArgumentWithThunk :: Argument RegionVar -> Argument RegionVar
regionArgumentWithThunk (ArgumentList [r1, r2, r3]) = ArgumentList [r1, r2, r3]
regionArgumentWithThunk (ArgumentList [r2, r3]) = ArgumentList [r2, r2, r3]

type Equations = IntMap Equation

-- Scope, Justs represent the annotation variables that are already unrolled and can thus be referenced by their fixpoint.
-- Argument represents the shape of the argument.
type SolveStack = [Maybe (Int, Argument ())]

solve :: Equations -> Int -> Annotation -> Argument Annotation
solve equations initialEquationScope = solve' [] 0 0
  where
    solve' ::
      SolveStack
      -> Int -- Number of introduced lambdas. Equal to the length of the scope
      -> Int -- Number of introduced foralls.
      -> Annotation
      -> Argument Annotation
    solve' scope lambdaCount forallCount (AVar var)
      | indexBoundLambda var == equationScope lambdaCount = solveVar scope lambdaCount forallCount $ indexInArgument var
      | otherwise = ArgumentValue $ AVar var
    solve' scope lambdaCount forallCount (AFix fixRegions s a) =
      ArgumentValue $ AFix fixRegions s $ a >>= solve' scope lambdaCount forallCount
    solve' scope lambdaCount forallCount (ATuple as) = ArgumentList $ solve' scope lambdaCount forallCount <$> as
    solve' scope lambdaCount forallCount (AProject a idx) = case solve' scope lambdaCount forallCount a of
      ArgumentValue a' -> ArgumentValue $ AProject a' idx
      ArgumentList as -> as !! idx
    solve' scope lambdaCount forallCount (AForall a) = AForall <$> solve' scope lambdaCount (forallCount + 1) a
    solve' scope lambdaCount forallCount (ALam argAnnotation argRegion dir a) =
      ALam argAnnotation argRegion dir
        <$> solve' (Nothing : scope) (lambdaCount + 1) forallCount a
    solve' scope lambdaCount forallCount (AApp a argAnnotation argRegion dir)
      = AApp <$> a' <*> return argAnnotation' <*> return argRegion <*> return dir
      where
        a' = solve' scope lambdaCount forallCount a
        argAnnotation' = argAnnotation >>= solve' scope lambdaCount forallCount
    solve' scope lambdaCount forallCount (AInstantiate a tp)
      = AInstantiate <$> solve' scope lambdaCount forallCount a <*> return tp
    solve' scope lambdaCount forallCount (AJoin a1 a2) = joinArguments
      [ solve' scope lambdaCount forallCount a1
      , solve' scope lambdaCount forallCount a2
      ]
    solve' scope lambdaCount forallCount (ARelation constraints) = ArgumentValue $ ARelation constraints
    solve' scope lambdaCount forallCount ABottom = ArgumentValue $ ABottom

    solveVar ::
      SolveStack
      -> Int -- Number of lambdas
      -> Int -- Number of foralls
      -> Int -- Index of variable in the equations
      -> Argument Annotation
    solveVar scope lambdaCount forallCount var = case lookupVar scope var 1 of
      Just arg -> arg
      _ ->
        let
          Equation _ fixRegions sort solved annotation = equations IntMap.! var
          annotation' = annotationIncrementScope (lambdaCount + 1) forallCount <$> annotation >>= solve' (Just (var, () <$ sort) : scope) (lambdaCount + 1) forallCount
          annotation'' = AFix fixRegions sort (ALam sort argumentEmpty RegionDirectionAny <$> annotation')
        in
          if solved then annotationIncrementScope lambdaCount forallCount <$> annotation else ArgumentValue annotation''

    equationScope :: Int -> Int
    equationScope increment = if initialEquationScope == 0 then 0 else initialEquationScope + increment

    lookupVar :: SolveStack -> Int -> Int -> Maybe (Argument Annotation)
    lookupVar (Just (var', arg) : _) var stackIndex
      | var' == var = Just $ AVar <$> sortArgumentToArgument (stackIndex) arg
    lookupVar (_ : stack) var stackIndex = lookupVar stack var (stackIndex + 1)
    lookupVar [] _ _ = Nothing

