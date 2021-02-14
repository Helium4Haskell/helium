module Helium.CodeGeneration.Iridium.Region.Generate where

import Data.List
import Data.Either
import Data.Maybe

import qualified Data.Map as M

import Lvm.Core.Type
import Lvm.Common.Id
import Lvm.Common.IdMap

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.Region.Env
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.Evaluate
import Helium.CodeGeneration.Iridium.Region.RegionVar
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Containment

data GlobalEnv = GlobalEnv !TypeEnvironment !DataTypeEnv !(IdMap (Int, Annotation))

data MethodEnv = MethodEnv
  { methodEnvQuantificationCount :: Int
  , methodEnvArgumentCount :: Int
  , methodEnvArguments :: [(Either Quantor (Sort, RegionSort))]
  , methodEnvVars :: (IdMap (Either (Int, Annotation) AnnotationVar, RegionVars))
  , methodEnvReturnRegionSort :: RegionSort
  , methodEnvReturnRegions :: RegionVars
  , methodEnvReturnSort :: Sort
  , methodEnvLocalSorts :: [Sort]
  , methodEnvAdditionalRegionSort :: RegionSort
  -- For variables on the left hand side of a let or LetAlloc bind, the additional region argument it may
  -- use for intermediate thunks or as additional region arguments for the caller
  , methodEnvAdditionalFor :: IdMap [RegionVar]
  }

-- TODO: What if last argument of a method is a type argument?

generate :: GlobalEnv -> Declaration Method -> Annotation
generate (GlobalEnv typeEnv dataTypeEnv globals) (Declaration _ _ _ _ method@(Method fnType arguments _ _ _ _))
  = result fixpoint
  where
    methodEnv = assign genv method

    globals' = globals -- TODO: Add annotation for recursive calls
    genv = GlobalEnv typeEnv dataTypeEnv globals'

    annotationMap :: M.Map Key Annotation
    annotationMap = M.fromListWith AJoin $ gatherInMethod genv methodEnv method

    -- Returns bottom if the annotation was not found
    lookupAnnotation :: Key -> Sort -> Annotation
    lookupAnnotation k s = fromMaybe (ABottom s) $ M.lookup k annotationMap

    -- Assumes the annotation is present in the map
    findAnnotation :: Key -> Annotation
    findAnnotation k = lookupAnnotation k (error "generate: key not found")

    fixpoint :: Annotation
    fixpoint
      = AFixEscape (methodEnvArgumentCount methodEnv) fixpointSort (methodEnvAdditionalRegionSort methodEnv)
      $ ALam fixpointSort RegionSortUnit LifetimeContextAny fixpointBody

    -- The fixpoint consists of a tuple of the effect and return annotation of the function and all annotations on local variables
    fixpointSort :: Sort
    fixpointSort = SortTuple
      $ sortAddLambdas sortEffects : sortAddLambdas (methodEnvReturnSort methodEnv) : map sortAddLambdas (methodEnvLocalSorts methodEnv)
      where
        sortEffects 
          = SortFun SortUnit RegionSortMonomorphic LifetimeContextAny
          $ SortFun SortUnit (methodEnvReturnRegionSort methodEnv) LifetimeContextLocalBottom SortRelation

    fixpointBody :: Annotation
    fixpointBody = ATuple
      $ annotationEffects
      : annotationReturn
      : annotationLocals
      where
        annotationEffects
          = ALam SortUnit RegionSortMonomorphic LifetimeContextAny
          $ ALam SortUnit (methodEnvReturnRegionSort methodEnv) LifetimeContextLocalBottom
          $ lookupAnnotation KeyEffect SortRelation
        annotationReturn
          = strengthen' $ lookupAnnotation KeyReturn (methodEnvReturnSort methodEnv)
        annotationLocals
          = zipWith (\_ idx -> strengthen' $ findAnnotation $ KeyLocal idx) (methodEnvLocalSorts methodEnv) [2..]

    sortAddLambdas :: Sort -> Sort
    sortAddLambdas s = foldr add s $ methodEnvArguments methodEnv
      where
        add (Left q) = SortForall q
        add (Right (s, rs)) = SortFun s rs LifetimeContextAny

    addLambdas :: Annotation -> Annotation
    addLambdas a = foldr add a $ methodEnvArguments methodEnv
      where
        add (Left q) = AForall q
        add (Right (s, rs)) = ALam s rs LifetimeContextAny

    -- Converts the tuple from the fixpoint to combined format matching with the sort of the function
    result :: Annotation -> Annotation
    result annotation = ALam SortUnit (methodEnvAdditionalRegionSort methodEnv) LifetimeContextAny $ case go $ methodEnvArguments methodEnv of
      Just a -> a
      Nothing -> ATop $ sortOfType dataTypeEnv $ typeNormalize typeEnv fnType
      where
        -- We cannot analyse functions whose last argument is a quantification
        go :: [Either Quantor (Sort, RegionSort)] -> Maybe Annotation
        go (Left quantor : args) = AForall quantor <$> go args
        go (Right (s, rs) : args) = ALam s rs LifetimeContextAny . ATuple . (annotationEffects :) . return <$> rest
          where
            annotationEffects
              | [] <- args
                = ALam SortUnit RegionSortMonomorphic LifetimeContextAny
                $ ALam SortUnit (methodEnvReturnRegionSort methodEnv) LifetimeContextLocalBottom
                $ AProject annotation 0
              | otherwise
                = ALam SortUnit RegionSortMonomorphic LifetimeContextAny
                $ ALam SortUnit (RegionSortTuple [RegionSortMonomorphic, RegionSortUnit]) LifetimeContextLocalBottom
                $ arelation
                $ relationFromConstraints
                $ map (`Outlives` RegionLocal 0)
                $ RegionLocal 1 : flattenRegionVars (regionSortToVars 2 rs)

            rest 
              | [] <- args = Just $ AProject (strengthen' annotation) 1
              | otherwise = go args

        go [] = Nothing

    -- Removes the annotation and region arguments from the return value and previous-thunk lambda
    -- from the scope
    strengthen' :: Annotation -> Annotation
    strengthen'
      = fromJust (error "generate: Annotation on the return uses a region or annotation variable from the return or previous-thunk, which is not in scope at that place")
      . strengthen 0 2 (regionVarsSize (methodEnvReturnRegions methodEnv) + 1)

assign :: GlobalEnv -> Method -> MethodEnv
assign genv@(GlobalEnv typeEnv dataTypeEnv _) method@(Method _ arguments returnType _ _ _) = methodEnv
  where
    methodEnv = MethodEnv
      quantificationCount
      lambdaCount
      arguments'
      (mapFromList $ argumentAssignment ++ localAssignment)
      returnRegionSort
      (regionSortToVars 0 returnRegionSort)
      returnSort
      localSorts
      additionalRegionSort
      additionalRegionFor

    quantificationCount = length $ lefts arguments
    lambdaCount = length $ rights arguments

    locals = methodLocals False typeEnv method -- locals excluding the function arguments

    arguments' = map f arguments
      where
        f (Left q) = Left q
        f (Right (Local _ tp)) = 
          let tp' = typeNormalize typeEnv tp
          in Right (sortOfType dataTypeEnv tp', regionSortOfType dataTypeEnv tp')

    returnSort = sortOfType dataTypeEnv returnType
    returnRegionSort = regionSortOfType dataTypeEnv (typeToStrict returnType)

    -- 1 region var, between the return regions and the arguments, is used for the previous-thunk region
    ((_, nextRegion1), argumentAssignment) = mapAccumR assignArg (2, regionSortSize returnRegionSort + 1) $ zip (rights arguments) (rights arguments')
    ((_, nextRegion2), localAssignment) = mapAccumR assignLocal (2, nextRegion1) locals
    (nextRegion3, additionalRegionFor) = assignAdditionalRegionVars genv method nextRegion2

    localSorts = map (\(Local _ tp) -> sortOfType dataTypeEnv $ typeNormalize typeEnv tp) locals

    fixpointArgument :: Annotation
    fixpointArgument = AVar $ AnnotationVar $ lambdaCount + 1

    applyLocal :: Annotation -> Annotation
    applyLocal a = a''
      where
        (_, _, a'') =  foldl ap (quantificationCount - 1, map snd argumentAssignment, AApp a (ATuple []) additionalRegionVars LifetimeContextAny) arguments

        ap :: (Int, [(Either t AnnotationVar, RegionVars)], Annotation) -> Either Quantor Local -> (Int, [(Either t AnnotationVar, RegionVars)], Annotation)
        ap (typeVarIdx, localAssignment', a') (Left _) = (typeVarIdx - 1, localAssignment', AInstantiate a' (TVar typeVarIdx))
        ap (typeVarIdx, (Right var, regions) : localAssignment', a') (Right _) =
          ( typeVarIdx
          , localAssignment'
          , AApp a' (AVar var) regions LifetimeContextAny
          )
        ap (_, (Left _, _) : _, _) (Right _) = error "assign: Expected argument variable, got local variable"

    additionalRegionCount = nextRegion3 - nextRegion1
    additionalRegionSort = RegionSortTuple $ replicate additionalRegionCount RegionSortMonomorphic
    additionalRegionVars = regionSortToVars nextRegion1 additionalRegionSort

    assignArg :: (Int, Int) -> (Local, (Sort, RegionSort)) -> ((Int, Int), (Id, (Either t AnnotationVar, RegionVars)))
    assignArg (nextAnnotation, nextRegion) (Local name _, (_, rs))
      = ((nextAnnotation + 1, nextRegion + regionSortSize rs), (name, (Right $ AnnotationVar nextAnnotation, regionSortToVars nextRegion rs)))

    assignLocal :: (Int, Int) -> Local -> ((Int, Int), (Id, (Either (Int, Annotation) t, RegionVars)))
    assignLocal (nextAnnotation, nextRegion) (Local name tp)
      = ( (nextAnnotation + 1, nextRegion + regionSortSize rs),
          ( name
          , ( Left (nextAnnotation, applyLocal (AVar $ AnnotationVar nextAnnotation))
            , regionSortToVars nextRegion rs
            )
          )
        )
      where
        rs = regionSortOfType dataTypeEnv $ typeNormalize typeEnv tp

assignAdditionalRegionVars :: GlobalEnv -> Method -> Int -> (Int, IdMap [RegionVar])
assignAdditionalRegionVars genv method firstRegionVar = (nextRegionVar, mapFromList assignment)
  where
    -- Per variable name, how many region variables its declaration needs
    counts :: [(Id, Int)]
    counts = filter ((> 0) . snd)
      $ map bindRegionCount (methodBinds method)
      ++ map (uncurry expRegionCount) (methodExpressions method)

    assignment :: [(Id, [RegionVar])]
    (nextRegionVar, assignment) = mapAccumR f firstRegionVar counts

    f :: Int -> (Id, Int) -> (Int, (Id, [RegionVar]))
    f next (lhs, count) =
      ( next + count
      , ( lhs
        , map RegionVar [next .. next + count - 1]
        )
      )

    bindRegionCount :: Bind -> (Id, Int)
    bindRegionCount (Bind lhs (BindTargetThunk _) args)
      = (lhs, max 0 (length (rights args) - 1))
    bindRegionCount (Bind lhs (BindTargetFunction (GlobalFunction fn _ _)) args)
      = (lhs, max 0 (length (rights args) - 1) + functionAdditionRegionCount fn)
    
    expRegionCount :: Id -> Expr -> (Id, Int)
    expRegionCount lhs (Call (GlobalFunction fn _ _) args)
      = (lhs, functionAdditionRegionCount fn)
    expRegionCount lhs (Eval (VarGlobal (GlobalVariable var _)))
      = (lhs, functionAdditionRegionCount var)
    expRegionCount lhs (Var (VarGlobal (GlobalVariable var _)))
      = (lhs, functionAdditionRegionCount var)
    expRegionCount lhs _ = (lhs, 0)

    functionAdditionRegionCount :: Id -> Int
    functionAdditionRegionCount = fst . lookupGlobal genv  -- TODO: Find function in environment

gatherContainment :: TypeEnvironment -> DataTypeEnv -> MethodEnv -> Method -> Relation
gatherContainment typeEnv dataTypeEnv methodEnv method@(Method _ _ tp _ _ _)
  = containmentLocals -- <> containmentReturn
  where
    containmentLocals = mconcat
      $ map (\(Local name tp) -> containment' dataTypeEnv (typeNormalize typeEnv tp) $ snd $ lookupLocal methodEnv name)
      $ methodLocals True typeEnv method -- locals including the function arguments
    
    -- containmentReturn = containment' dataTypeEnv (typeToStrict tp) $ methodEnvReturnRegions methodEnv

-- In case of a global variable, it should be a function of arity 0.
lookupSimpleVar :: GlobalEnv -> MethodEnv -> Variable -> (Annotation, RegionVars)
lookupSimpleVar genv@(GlobalEnv typeEnv dataTypeEnv _) _ (VarGlobal (GlobalVariable name tp)) = case lookupGlobal genv name of
  -- Expect an annotation without additional region arguments.
  -- Apply the annotation with an empty list of additional region arguments.
  (0, a) ->
    ( AApp a (ATuple []) (RegionVarsTuple []) LifetimeContextAny
    , mapRegionVars (const RegionGlobal) $ regionSortToVars 0 $ regionSortOfType dataTypeEnv $ typeNormalize typeEnv tp
    )
  _ -> error "lookupSimpleVar: Expected to get a variable without additional region arguments, got a global function with additional region arguments."
lookupSimpleVar _ env (VarLocal (Local name _)) = lookupLocal env name

lookupVar :: GlobalEnv -> MethodEnv -> Id -> Variable -> (Annotation, RegionVars)
lookupVar genv@(GlobalEnv typeEnv dataTypeEnv _) env lhs (VarGlobal (GlobalVariable name tp)) = 
  ( AApp a (ATuple []) (RegionVarsTuple $ map RegionVarsSingle additionalRegions) LifetimeContextAny
  , mapRegionVars (const RegionGlobal) $ regionSortToVars 0 $ regionSortOfType dataTypeEnv $ typeNormalize typeEnv tp
  )
  where
    (count, a) = lookupGlobal genv name
    additionalRegions = case count of
      0 -> [] -- Prevent a lookup
      _ -> fromMaybe (error "lookupVar: additional region arguments not found") $ lookupMap lhs $ methodEnvAdditionalFor env
lookupVar _ env _ (VarLocal (Local name _)) = lookupLocal env name

lookupGlobal :: GlobalEnv -> Id -> (Int, Annotation)
lookupGlobal (GlobalEnv _ _ m) name
  | Just a <- lookupMap name m = a
lookupGlobal _ name = error $ "lookupGlobal: Variable " ++ show name ++ " not found"

lookupLocal :: MethodEnv -> Id -> (Annotation, RegionVars)
lookupLocal env name = case lookupMap name $ methodEnvVars env of
  Nothing -> error $ "lookupLocal: Variable " ++ show name ++ " not found"
  Just (a, regions) ->
    let
      annotation = case a of
        Left (_, a') -> a'
        Right var -> AVar var
    in (annotation, regions)

data Key = KeyEffect | KeyReturn | KeyLocal !Int deriving (Eq, Ord)

type Gather = [(Key, Annotation)]

effect :: Annotation -> Gather
effect a = [(KeyEffect, a)]

returns :: Annotation -> Gather
returns a = [(KeyReturn, a)]

gatherLocal :: Int -> Annotation -> Gather
gatherLocal idx a = [(KeyLocal idx, a)]

gatherInMethod :: GlobalEnv -> MethodEnv -> Method -> Gather
gatherInMethod genv@(GlobalEnv typeEnv dataTypeEnv _) env method@(Method _ _ _ _ block blocks)
  = effect containment ++ gatherBlocks
  where
    gatherBlocks = (block : blocks) >>= (\(Block _ instr) -> gatherInstruction genv env instr)
    containment = arelation $ gatherContainment typeEnv dataTypeEnv env method

gatherInstruction :: GlobalEnv -> MethodEnv -> Instruction -> Gather
gatherInstruction genv env instruction = case instruction of
  Let name expr next -> case lookupMap name $ methodEnvVars env of
    Nothing -> error "Local variable not present in MethodEnv"
    Just (Right _, _) -> error "Found function argument in left hand side of Let instruction"
    Just (Left (idx, _), regions) ->
      let
        (aEffect, aValue) = gatherExpression genv env name expr regions
      in
        effect aEffect ++ gatherLocal idx aValue ++ go next
  LetAlloc binds next -> binds >>= gatherBind genv env
  Jump _ -> []
  Match var target instantiation fields next -> gatherMatch genv env var target instantiation fields ++ go next
  Case _ _ -> []
  Return var ->
    let
      (annotation, regions) = lookupLocal env $ localName var
      constraints = zipFlattenRegionVars Outlives regions $ methodEnvReturnRegions env
    in
      effect (arelation $ relationFromConstraints constraints) ++ returns annotation
  Unreachable _ -> []
  where
    go :: Instruction -> Gather
    go = gatherInstruction genv env

gatherBind :: GlobalEnv -> MethodEnv -> Bind -> Gather
gatherBind genv env bind@(Bind var _ _) = case lookupMap var $ methodEnvVars env of
  Nothing -> error "Local variable of bind not present in MethodEnv"
  Just (Right _, _) -> error "Found function argument in left hand side of Bind"
  Just (Left (idx, _), regions) ->
    let
      (aEffect, aValue) = gatherBind' genv env bind regions
    in
      effect aEffect ++ gatherLocal idx aValue

-- Returns the annotations (effect) caused by evaluating the expression, and the annotation
-- (type) of the resulting value
gatherBind' :: GlobalEnv -> MethodEnv -> Bind -> RegionVars -> (Annotation, Annotation)
gatherBind' genv env (Bind _ (BindTargetTuple _) arguments) (RegionVarsTuple [_, returnRegions]) = (arelation $ relationFromConstraints constraints, annotation)
  where
    arguments' = rights arguments
    argumentsAnalysis = map (lookupLocal env . localName) arguments'

    -- If any argument is strict, transform it to a lazy representation 
    argumentRegion :: (Annotation, RegionVars) -> RegionVars
    argumentRegion (_, RegionVarsTuple [r, rs]) = RegionVarsTuple [RegionVarsSingle RegionBottom, r, rs]
    argumentRegion (_, r@(RegionVarsTuple [r1, r2, rs])) = r
    argumentRegion _ = error "gatherBind': Tuple: argument has wrong region sort"

    constraints = zipFlattenRegionVars Outlives (RegionVarsTuple $ map argumentRegion argumentsAnalysis) returnRegions

    annotation = ATuple $ map fst argumentsAnalysis
gatherBind' genv env (Bind _ (BindTargetConstructor (DataTypeConstructor constructorName _)) arguments) (RegionVarsTuple [_, returnRegions]) = (ABottom SortRelation, ATuple []) -- TODO: Constructors
gatherBind' genv env (Bind lhs target arguments) returnRegions = case foldl apply (targetRegionStrict : intermediateRegions, ABottom SortRelation, targetAnnotation) arguments of
  ([], resultEffect, resultAnnotation) -> 
    ( arelation (relationFromConstraints constraints) `AJoin` resultEffect
    , resultAnnotation
    )
  _ -> error "gatherBind': too many additional region arguments were provided" -- TODO: Will this work with a bind of zero arguments?
  where
    (regionThunk, regionValue, regionNested) = regionsLazy returnRegions

    additionalRegions = fromMaybe [] $ lookupMap lhs $ methodEnvAdditionalFor env 

    (intermediateRegions, targetAnnotation, targetRegionLazy, targetRegionStrict) = case target of
      BindTargetThunk var ->
        let
          (a, rs) = lookupSimpleVar genv env var
          (l, s, _) = regionsLazy rs
        in
          -- All additional regions for this bind are used for the intermediate thunks.
          (additionalRegions, a, l, s)
      BindTargetFunction (GlobalFunction name _ _) ->
        let
          (callAdditionalRegionCount, a) = lookupGlobal genv name
          a' = AApp a (ATuple []) (RegionVarsTuple $ map RegionVarsSingle $ take callAdditionalRegionCount additionalRegions) LifetimeContextAny
        in
          ( drop callAdditionalRegionCount additionalRegions
          , a'
          , RegionGlobal
          , RegionGlobal
          )
      _ -> error "gatherBind': BindTargetTuple and BindTargetThunk should be impossible as they are already handled"

    -- All arguments should outlive the thunk
    constraints = Outlives targetRegionLazy regionThunk : map argumentConstraint (rights arguments)
    argumentConstraint :: Local -> RelationConstraint
    argumentConstraint var = let (r, _, _) = regionsLazy $ snd $ lookupLocal env $ localName var in r `Outlives` regionThunk

    -- Passes the annotation and regions of the argument
    apply :: ([RegionVar], Annotation, Annotation) -> (Either Type Local) -> ([RegionVar], Annotation, Annotation)
    apply (thunkRegions, effect, value) (Left tp) = (thunkRegions, effect, value `AInstantiate` tp)
    apply (thunkRegions, effect, value) (Right var)
      | null thunkRegions = error "gatherBind': not enough region arguments"
      | otherwise = (thunkRegions', effect `AJoin` effect'', value')
      where
        previous : thunkRegions' = thunkRegions
        (argAnnotation, argRegions) = lookupLocal env $ localName var
        (effect', value') = unliftPair $ AApp value argAnnotation (regionsAsLazy argRegions) LifetimeContextAny

        resultRegions = case thunkRegions' of
          current : _ -> RegionVarsTuple [RegionVarsSingle current, RegionVarsTuple []]
          [] -> RegionVarsTuple [RegionVarsSingle regionValue, regionNested]
        effect'' =
          AApp
            (AApp effect' (ATuple []) (RegionVarsSingle previous) LifetimeContextAny)
            (ATuple [])
            resultRegions
            LifetimeContextLocalBottom

gatherMatch :: GlobalEnv -> MethodEnv -> Local -> MatchTarget -> [Type] -> [Maybe Id] -> Gather
gatherMatch genv env (Local obj _) (MatchTargetTuple _) _ fields =
  effect (arelation $ relationFromConstraints $ constraints objRegions fieldAnnotations)
  ++ gatherFields 0 fieldAnnotations
  where
    fieldAnnotations = map (fmap $ \name -> findMap name $ methodEnvVars env) fields

    (objAnnotation, RegionVarsTuple [_, RegionVarsTuple objRegions]) = lookupLocal env obj

    constraints :: [RegionVars] -> [Maybe (a, RegionVars)] -> [RelationConstraint]
    constraints (_  : _  : _  : regions) (Nothing : fields') = constraints regions fields'
    constraints (r1 : r2 : rs : regions) (Just (_, fieldRegions) : fields')
      = zipFlattenRegionVars Outlives rs' fieldRegions -- Unify regions from object and field
      ++ zipFlattenRegionVars Outlives fieldRegions rs'
      ++ constraints regions fields'
      where
        rs' = RegionVarsTuple [r1, r2, rs]
    constraints [] [] = []
    constraints _ _ = error "gatherMatch: Mismatch in region variable counts"

    -- Gather the annotations on the fields
    gatherFields :: Int -> [Maybe (Either (Int, Annotation) AnnotationVar, RegionVars)] -> Gather
    gatherFields i (Nothing : fields') = gatherFields (i+1) fields'
    gatherFields i (Just (Left (idx, _), _) : fields')
      = gatherLocal idx (AProject objAnnotation i)
      ++ gatherFields (i+1) fields'
    gatherFields _ (Just (Right _, _) : _) = error "gatherMatch: Expected a local variable, found an argument"
    gatherFields _ [] = []
gatherMatch genv@(GlobalEnv typeEnv dataTypeEnv _) env (Local obj _) target@(MatchTargetConstructor _) tps fields
  = (fieldLocals >>= f) ++ effect (arelation $ relationFromConstraints $ map (`Outlives` RegionGlobal) $ flattenRegionVars objRegions)
  where
    (objAnnotation, RegionVarsTuple [_, objRegions]) = lookupLocal env obj

    fieldLocals = catMaybes $ matchFieldLocals target tps fields
    f :: Local -> Gather
    f (Local name tp)
      | (Left (idx, _), regions) <- findMap name $ methodEnvVars env
        = effect (arelation $ relationFromConstraints $ map (`Outlives` RegionGlobal) $ flattenRegionVars regions)
        ++ gatherLocal idx (ATop $ sortOfType dataTypeEnv $ typeNormalize typeEnv tp)
    f _ = error "gatherMatch: Expected a local variable, found an argument"

-- Returns the annotations (effect) caused by evaluating the expression, and the annotation
-- (type) of the resulting value
gatherExpression :: GlobalEnv -> MethodEnv -> Id -> Expr -> RegionVars -> (Annotation, Annotation)
gatherExpression genv@(GlobalEnv typeEnv dataTypeEnv _) env lhs expr returnRegions = case expr of
  Literal _ -> bottom
  Call (GlobalFunction name _ _) args ->
    let
      additionalRegions = fromMaybe [] $ lookupMap lhs $ methodEnvAdditionalFor env
      (_, annotation) = lookupGlobal genv name
      annotation' = AApp annotation (ATuple []) (RegionVarsTuple $ map RegionVarsSingle additionalRegions) LifetimeContextAny

      call :: (Annotation, Annotation) -> [Either Type Local] -> (Annotation, Annotation)
      call (aEffect, aReturn) (Left tp' : args') = call (aEffect, AInstantiate aReturn tp') args'
      call (_, aReturn) (Right var : args') = call (unliftPair $ AApp aReturn argAnnotation (regionsAsLazy argRegions) LifetimeContextAny) args'
        where
          (argAnnotation, argRegions) = lookupLocal env $ localName var
      call (aEffect, aReturn) [] = (aEffect, aReturn)

      (annotationEffect, annotationReturn) = call (ABottom SortRelation, annotation') args
    in
      (AApp (AApp annotationEffect (ATuple []) (RegionVarsSingle RegionBottom) LifetimeContextAny) (ATuple []) returnRegions LifetimeContextLocalBottom, annotationReturn)
  Instantiate var tps ->
    let
      (annotation, regions) = lookupLocal env $ localName var
    in
      (arelation $ relationFromConstraints $ zipFlattenRegionVars Outlives regions returnRegions, foldl AInstantiate annotation tps)
  Eval var ->
    let
      (annotation, regions) = lookupVar genv env lhs var
      (_, r2, rs) = regionsLazy regions
      (r2', rs') = regionsStrict returnRegions
      constraints = r2 `Outlives` r2' : zipFlattenRegionVars Outlives rs rs'
    in
      (arelation $ relationFromConstraints constraints, annotation)
  Var var ->
    let
      (annotation, regions) = lookupVar genv env lhs var
    in
      (arelation $ relationFromConstraints $ zipFlattenRegionVars Outlives regions returnRegions, annotation)
  Cast _ _ -> error "Cannot analyse cast"
  CastThunk var ->
    let
      (annotation, regions) = lookupLocal env $ localName var
      (r2, rs) = regionsStrict regions
      (_, r2', rs') = regionsLazy returnRegions
      constraints = r2 `Outlives` r2' : zipFlattenRegionVars Outlives rs rs'
    in
      (arelation $ relationFromConstraints constraints, annotation)
  Phi branches ->
    let
      f (PhiBranch _ var) = (arelation $ relationFromConstraints $ zipFlattenRegionVars Outlives regions returnRegions, annotation)
        where
          (annotation, regions) = lookupLocal env $ localName var
    in
      joins $ map f branches
  PrimitiveExpr _ _ -> bottom
  Undefined _ -> bottom
  Seq _ var -> gatherExpression genv env lhs (Var $ VarLocal var) returnRegions
  where
    bottom = (ABottom SortRelation, ABottom $ sortOfType dataTypeEnv $ typeNormalize typeEnv $ typeOfExpr typeEnv expr)
    join (a, b) (a', b') = (AJoin a a', AJoin b b')
    joins = foldr1 join

regionsStrict :: RegionVars -> (RegionVar, RegionVars)
regionsStrict (RegionVarsTuple [RegionVarsSingle r, rs]) = (r, rs)
regionsStrict rs@(RegionVarsSingle r) = (r, rs) -- We allow a single region to be used at places where multiple region variables are expected.
regionsStrict _ = error "Expected region variables of a lazy value"

regionsLazy :: RegionVars -> (RegionVar, RegionVar, RegionVars)
regionsLazy (RegionVarsTuple [RegionVarsSingle r1, RegionVarsSingle r2, rs]) = (r1, r2, rs)
regionsLazy (RegionVarsTuple [RegionVarsSingle r, rs]) = (r, r, rs)
regionsLazy rs@(RegionVarsSingle r) = (r, r, rs) -- We allow a single region to be used at places where multiple region variables are expected.
regionsLazy _ = error "Expected region variables of a lazy value"

regionsAsLazy :: RegionVars -> RegionVars
regionsAsLazy regions = RegionVarsTuple [RegionVarsSingle r1, RegionVarsSingle r2, rs]
  where
    (r1, r2, rs) = regionsLazy regions

unliftPair :: Annotation -> (Annotation, Annotation)
unliftPair a = (AProject a 0, AProject a 1)
