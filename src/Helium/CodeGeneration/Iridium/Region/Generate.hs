module Helium.CodeGeneration.Iridium.Region.Generate where

import Data.List
import Data.Either
import Data.Maybe

import Lvm.Core.Type
import Lvm.Common.Id
import Lvm.Common.IdMap

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Core.TypeEnvironment

import Helium.CodeGeneration.Iridium.Region.Env
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.RegionVar
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Containment

data GlobalEnv = GlobalEnv !TypeEnvironment !DataTypeEnv !(IdMap (Int, Annotation))

data MethodEnv = MethodEnv
  { methodEnvQuantificationCount :: Int
  , methodEnvArgumentCount :: Int
  , methodEnvVars :: (IdMap (Either Int AnnotationVar, RegionVars))
  , methodEnvReturnRegions :: RegionVars
  , methodEnvReturnSort :: Sort
  , methodEnvAdditionalRegionSort :: RegionSort
  , methodEnvAdditionalRegionVars :: RegionVars
  -- For variables on the left hand side of a let or LetAlloc bind, the additional region argument it may
  -- use for intermediate thunks or as additional region arguments for the caller
  , methodEnvAdditionalFor :: IdMap [RegionVar]
  }

-- TODO: What if last argument of a method is a type argument?

assign :: GlobalEnv -> Method -> MethodEnv
assign genv@(GlobalEnv typeEnv dataTypeEnv _) method@(Method _ arguments returnType _ _ _) = methodEnv
  where
    methodEnv = MethodEnv
      (length $ lefts arguments)
      (length $ rights arguments)
      (mapFromList $ argumentAssignment ++ localAssignment)
      (regionSortToVars 0 returnRegionSort)
      returnSort
      additionalRegionSort
      (regionSortToVars nextRegion1 additionalRegionSort)
      additionalRegionFor

    locals = methodLocals False typeEnv method -- locals excluding the function arguments

    returnSort = sortOfType dataTypeEnv returnType
    returnRegionSort = regionSortOfType dataTypeEnv (typeToStrict returnType)

    ((_, nextRegion1), argumentAssignment) = mapAccumR assignArg (0, regionSortSize returnRegionSort) (rights arguments)
    ((_, nextRegion2), localAssignment) = mapAccumR assignLocal (0, nextRegion1) locals
    (nextRegion3, additionalRegionFor) = assignAdditionalRegionVars genv method nextRegion2

    additionalRegionCount = nextRegion3 - nextRegion1
    additionalRegionSort = RegionSortTuple $ replicate additionalRegionCount RegionSortMonomorphic

    assignArg :: (Int, Int) -> Local -> ((Int, Int), (Id, (Either Int AnnotationVar, RegionVars)))
    assignArg (nextAnnotation, nextRegion) (Local name tp)
      = ((nextAnnotation + 1, nextRegion + regionSortSize rs), (name, (Right $ AnnotationVar nextAnnotation, regionSortToVars nextRegion rs)))
      where
        rs = regionSortOfType dataTypeEnv $ typeNormalize typeEnv tp

    assignLocal :: (Int, Int) -> Local -> ((Int, Int), (Id, (Either Int AnnotationVar, RegionVars)))
    assignLocal (nextAnnotation, nextRegion) (Local name tp)
      = ((nextAnnotation + 1, nextRegion + regionSortSize rs), (name, (Left nextAnnotation, regionSortToVars nextRegion rs)))
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
      = (lhs, length (rights args) - 1)
    bindRegionCount (Bind lhs (BindTargetFunction (GlobalFunction fn _ _)) args)
      = (lhs, length (rights args) - 1 + functionAdditionRegionCount fn)
    
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
  = containmentLocals <> containmentReturn
  where
    containmentLocals = mconcat
      $ map (\(Local name tp) -> containment' dataTypeEnv tp $ snd $ lookupLocal methodEnv name)
      $ methodLocals True typeEnv method -- locals including the function arguments
    
    containmentReturn = containment' dataTypeEnv (typeToStrict tp) $ methodEnvReturnRegions methodEnv

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
        Left idx ->
          let
            var = AVar $ AnnotationVar $ methodEnvArgumentCount env + 1
            app = AApp var (ATuple []) (methodEnvAdditionalRegionVars env) LifetimeContextAny
          in AProject app idx
        Right var -> AVar var
    in (annotation, regions)

data Key = KeyEffect | KeyReturn | KeyLocal !Int
type Gather = [(Key, Annotation)]

effect :: Annotation -> Gather
effect a = [(KeyEffect, a)]

returns :: Annotation -> Gather
returns a = [(KeyReturn, a)]

gatherLocal :: Int -> Annotation -> Gather
gatherLocal idx a = [(KeyLocal idx, a)]

gatherInstruction :: GlobalEnv -> MethodEnv -> Instruction -> Gather
gatherInstruction genv env instruction = case instruction of
  Let name expr next -> case lookupMap name $ methodEnvVars env of
    Nothing -> error "Local variable not present in MethodEnv"
    Just (Right _, _) -> error "Found function argument in left hand side of Let instruction"
    Just (Left idx, regions) ->
      let
        (aEffect, aValue) = gatherExpression genv env name expr regions
      in
        effect aEffect ++ gatherLocal idx aValue ++ go next
  LetAlloc binds next -> binds >>= gatherBind genv env
  Jump _ -> []
  Match var target instantiation fields next -> undefined
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
  Just (Left idx, regions) ->
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
gatherBind' genv env (Bind lhs target arguments) returnRegions = undefined
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

    -- All arguments should outlive the thunk
    constraints = Outlives targetRegionLazy regionThunk : map argumentConstraint (rights arguments)
    argumentConstraint :: Local -> RelationConstraint
    argumentConstraint var = let (r, _, _) = regionsLazy $ snd $ lookupLocal env $ localName var in r `Outlives` regionThunk

    -- Passes the annotation and regions of the argument
    apply :: ([RegionVar], Annotation, Annotation) -> (Either Type Local) -> ([RegionVar], Annotation, Annotation)
    apply (thunkRegions, effect, value) (Left tp) = (thunkRegions, effect, value `AInstantiate` tp)
    apply (thunkRegions, effect, value) (Right var) = (thunkRegions', effect `AJoin` effect'', value')
      where
        previous : thunkRegions' = thunkRegions
        (argAnnotation, argRegions) = lookupLocal env $ localName var
        (effect', value') = unliftPair $ AApp value argAnnotation (regionsAsLazy argRegions) LifetimeContextAny

        resultRegions = case thunkRegions' of
          current : _ -> RegionVarsTuple [RegionVarsSingle current, RegionVarsTuple []]
          _ -> RegionVarsTuple [RegionVarsSingle regionValue, regionNested]
        effect'' =
          AApp
            (AApp effect' (ATuple []) (RegionVarsSingle previous) LifetimeContextAny)
            (ATuple [])
            resultRegions
            LifetimeContextLocalBottom


{-
data Bind = Bind { bindVar :: !Id, bindTarget :: !BindTarget, bindArguments :: ![Either Type Variable] }
  deriving (Eq, Ord)
  -}
{-
data Instruction
  -- * Computes an expression and assigns the value to the given variable name.
  = Let !Id !Expr !Instruction
  -- * Allocates thunks or constructors. Those binds may be recursive.
  | LetAlloc ![Bind] !Instruction
  -- * Uncoditionally jumps to a block
  | Jump !BlockName
  -- * Asserts that the variable matches with the specified MatchTarget. Can be used to match on constructors,
  -- tuples and thunks. Pattern matching on thunks is not possible from Haskell code, but is used to write the
  -- runtime library. If the variable does not match with the specified MatchTarget, the behaviour is undefined.
  -- Extracts fields out of the object.
  | Match !Variable !MatchTarget ![Type] ![Maybe Id] !Instruction
  -- * Conditionally jumps to a block, depending on the value of the variable. Can be used to distinguish
  -- different constructors of a data type, or on integers.
  | Case !Variable Case
  -- * Returns a value from the function. The type of the variable should match with the return type of the
  -- containing method.
  | Return !Variable
  -- * Denotes that the current location is unreachable. Can be used after a call to a diverging function like 'error'.
  -- The control flow or the argument should guarantee that this location is unreachable. In the case of calling 'error',
  -- the argument should be the returned value of 'error'.
  | Unreachable !(Maybe Variable)
  deriving (Eq, Ord)
-}

-- Returns the annotations (effect) caused by evaluating the expression, and the annotation
-- (type) of the resulting value
gatherExpression :: GlobalEnv -> MethodEnv -> Id -> Expr -> RegionVars -> (Annotation, Annotation)
gatherExpression genv@(GlobalEnv typeEnv dataTypeEnv _) env lhs expr returnRegions = case expr of
  Literal _ -> bottom
  Call (GlobalFunction name _ _) args -> -- TODO: Additional region arguments
    let
      additionalRegions = fromMaybe [] $ lookupMap lhs $ methodEnvAdditionalFor env
      (_, annotation) = lookupGlobal genv name
      annotation' = AApp annotation (ATuple []) (RegionVarsTuple $ map RegionVarsSingle additionalRegions) LifetimeContextAny

      call :: (Annotation, Annotation) -> [Either Type Local] -> (Annotation, Annotation)
      call (aEffect, aReturn) (Left tp' : args') = call (aEffect, AInstantiate aReturn tp') args'
      call (_, aReturn) (Right var : args') = call (unliftPair $ AApp aReturn argAnnotation (regionsAsLazy argRegions) LifetimeContextAny) args'
        where
          (argAnnotation, argRegions) = lookupLocal env $ localName var -- TODO: Convert argRegions to thunk representation
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
  Var var -> -- TODO: Additional region arguments
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

  {-
  data Expr
  -- A literal value. Note that strings are allocated, integers and floats not.
  = Literal !Literal
  -- Calls a function. The number of arguments should be equal to the number of parameters of the specified function.
  | Call !GlobalFunction ![Either Type Variable]
  | Instantiate !Variable ![Type]
  -- Evaluates a value to WHNF or returns the value if it is already in WHNF.
  | Eval !Variable
  -- Gets the value of a variable. Does not evaluate the variable.
  | Var !Variable
  -- Casts a variable to a (possibly) different type.
  | Cast !Variable !Type
  -- Casts type `!a` to `a`
  | CastThunk !Variable
  -- Represents a phi node in the control flow of the method. Gets a value, based on the previous block.
  | Phi ![PhiBranch]
  -- Calls a primitive instruction, like integer addition. The number of arguments should be equal to the number of parameters
  -- that the primitive expects.
  | PrimitiveExpr !Id ![Either Type Variable]
  -- Denotes an undefined value, not the Haskell function 'undefined'. This expression does not throw, but just has some unknown value.
  -- This can be used for a value which is not used.
  | Undefined !Type
  -- `%c = seq %a %b` marks a dependency between variables %a and %b. Assigns %b to %c and ignores the value of %a. 
  -- Prevents that variable %a is removed by dead code removal. Can be used to compile the Haskell functions `seq` and `pseq`.
  | Seq !Variable !Variable
  deriving (Eq, Ord)-}

unliftPair :: Annotation -> (Annotation, Annotation)
unliftPair a = (AProject a 0, AProject a 1)
