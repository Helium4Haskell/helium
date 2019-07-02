module Helium.CodeGeneration.Iridium.Region.MethodInitialize
  ( methodInitialize
  , MethodState(..), msAdditionalArgumentScope
  , Constraint(..)
  , CallArgument(..)
  , VariableInfo(..)
  , assignAdditionalRegionVariables
  , isValueArgument
  ) where

import Data.List
import Data.Either
import Data.Maybe
import Data.IntMap.Strict (IntMap)
import qualified Data.IntMap.Strict as IntMap
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Show
import Helium.CodeGeneration.Iridium.Type
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.Containment
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Utils

import Debug.Trace

data MethodState = MethodState 
  { msType :: !Tp
  , msArity :: !Int
  , msQuantors :: ![Int]
  , msVariables :: !VariablesMap
  , msShapeRegions :: ![RegionVar] -- Regions for the arguments and return values
  , msReturnRegion :: !(Argument RegionVar)
  , msRegionCount :: !Int
  -- , msRegionExposed :: ![Bool]

  , msRelation :: !Relation -- Relation derived from instructions (lower order)
  , msConstraints :: ![Constraint] -- Constraints derived from calls and thunk allocations (higher order)
  }

{-
Argument scopes:
0 - special scope. Used for the global region, and annotation variables in a binding group before solving the constraints.
1 - return regions
2 - the region variable pointing at the previous thunk. Used for annotations of partially applied functions
3 - the last argument of the method
4 - ...
arity + 2 - the first argument of the method
arity + 3 - the additional region argument and the annotation variables in a method before solving the constraints
-}

msAdditionalArgumentScope :: MethodState -> Int
msAdditionalArgumentScope = (3 +) . msArity

instance Show MethodState where
  show (MethodState _ lambdaCount _ vars exposedRegions retRegion regionCount relation constraints) = unlines $ map ("  " ++)
    [ "Lambda count: " ++ show lambdaCount
    , "Variable mapping:\n" ++ showVariablesMap vars
    , "Exposed regions: " ++ show exposedRegions
    , "Inner regions: [1.." ++ show regionCount ++ "]"
    , "Return regions: " ++ show retRegion
    , "Relation: " ++ show relation
    , "Constraints:" ++ (constraints >>= (("\n    " ++) . show))
    ]

data CallKind = CKCall | CKAllocThunk | CKInstantiate deriving Eq

data Constraint
  = CCall
    { cCallIdentifier :: !Id -- The variable on the left hand side of the call expression or bind. Uniquely identifies the constraint.
    , cCallResultAnnotationSort :: !(Argument Sort)
    , cCallResultAnnotation :: !(Argument AnnotationVar)
    , cCallResultRegion :: !(Argument RegionVar)
    , cCallTarget :: !(Either Id (Argument AnnotationVar, RegionVar, RegionVar)) -- Left for a call to a global function, right for a higher order call
    , cCallTargetArity :: !Int -- Arity of the target function. Zero for a higher order call
    , cCallAdditionalRegions :: ![RegionVar]
    , cCallArguments :: ![CallArgument]
    , cCallKind :: !CallKind
    }
  -- Note that CJoin and CReturn may not contain regions from the arguments, return type or additional regions of a method.
  | CJoin !(Argument Sort) !(Argument AnnotationVar) ![Argument Annotation]
  | CReturn !(Argument Annotation)

data CallArgument
  = CAType !Tp
  | CALocal !(Argument AnnotationVar) !(Argument RegionVar)
  | CAGlobal !(Argument Annotation) !(Argument RegionVar)

instance Show CallKind where
  show CKCall = "call"
  show CKAllocThunk = "alloc_thunk"
  show CKInstantiate = "instantiate"

instance Show Constraint where
  show (CJoin aSort a as) = show a ++ ": " ++ show aSort ++ " := join(" ++ intercalate ", " (map show as) ++ ")"
  show (CCall name resASort resA resR target arity additionalRegions args kind) = showId name "[" ++ show resA ++ ": " ++ show resASort ++ "; " ++ show resR ++ "] := " ++ show kind ++ " " ++ targetString ++ "[" ++ show arity ++ "]" ++ argsString
    where
      targetString = case target of
        Left name -> "@" ++ showId name "" ++ ": " ++ show resASort
        Right (annotations, rThunk, rValue) -> "[" ++ show annotations ++ ": " ++ show resASort ++ "; (" ++ show rThunk ++ ", " ++ show rValue ++ ");"
      argsString = "(" ++ intercalate ", " (map show additionalRegions) ++ "; " ++ intercalate ", " (map show args) ++ ")"
  show (CReturn annotations) = "return " ++ show annotations

instance Show CallArgument where
  show (CAType tp) = "{ " ++ show tp ++ " }"
  show (CALocal annotations regions) = "local [" ++ show annotations ++ "; " ++ show regions ++ "]"
  show (CAGlobal annotations regions) = "global [" ++ show annotations ++ "; " ++ show regions ++ "]"

data VariableInfo = VariableInfo !Tp !(Argument AnnotationVar) !(Argument RegionVar)
type VariablesMap = IdMap VariableInfo

showVariablesMap :: VariablesMap -> String
showVariablesMap vars = intercalate "\n" $ map (\(var, info) -> "    %" ++ showId var (": " ++ show info)) $ listFromMap vars

instance Show VariableInfo where
  show (VariableInfo tp annotation region) = show tp ++ " [" ++ show annotation ++ "; " ++ show region ++ "]"

showAnnotationsMap :: IntMap Annotation -> String
showAnnotationsMap m = IntMap.toList m >>= showAnnotation
  where
    showAnnotation (idx, annotation) = "\n    " ++ show (AnnotationVar idx) ++ " = " ++ show annotation

methodInitialize :: TypeEnvironment -> EffectEnvironment -> NameSupply -> Method -> (Method, MethodState)
methodInitialize typeEnv effectEnv supply method@(Method methodType _ _ _ _ _) =
  (method', assignIntermediateThunkRegions $ methodApplyRelationConstraints relationConstraints stateWithConstraints)
  where
    methodTp = tpFromType [] $ typeNormalize typeEnv methodType

    method' = hoistGlobalVariables effectEnv supply method
    (arity, quantors, variables, initialReturnRegions, initialExposedRegions, regionCount) = assignVariables typeEnv effectEnv method'

    initialState = MethodState methodTp arity quantors variables initialExposedRegions initialReturnRegions regionCount emptyRelation []

    relationConstraints = gather effectEnv initialState method'
    annotationConstraints = constraints effectEnv initialState method'

    annotationUnification = constraintSimpleUnificationsMap annotationConstraints

    substitute :: AnnotationVar -> AnnotationVar
    substitute (AnnotationVar a) = case IntMap.lookup a annotationUnification of
      Nothing -> AnnotationVar a
      Just a' -> AnnotationVar a'
  
    substituteAnnotation :: Int -> Annotation -> Annotation
    substituteAnnotation lambdas (AFix identifier fixRegions a1 a2) = AFix identifier fixRegions a1' a2'
      where
        a1' = substituteAnnotation lambdas a1
        a2' = substituteAnnotation lambdas a2
    substituteAnnotation lambdas (AForall a) = AForall $ substituteAnnotation lambdas a
    substituteAnnotation lambdas (ALam argA argR a) = ALam argA argR $ substituteAnnotation (lambdas + 1) a
    substituteAnnotation lambdas (AApp a argA argR) = AApp a' argA' argR
      where
        a' = substituteAnnotation lambdas a
        argA' = fmap (substituteAnnotation lambdas) argA
    substituteAnnotation lambdas (AInstantiate a tp) = AInstantiate (substituteAnnotation lambdas a) tp
    substituteAnnotation lambdas (AVar var)
      | indexBoundLambda var >= lambdas = AVar $ variableIncrementLambdaBound 0 lambdas $ substitute $ variableIncrementLambdaBound 0 (-lambdas) var
      | otherwise = AVar var
    substituteAnnotation lambdas (AJoin a1 a2) = AJoin a1' a2'
      where
        a1' = substituteAnnotation lambdas a1
        a2' = substituteAnnotation lambdas a2
    substituteAnnotation lambdas a = a
    {-
    
data Annotation
  = AFix !(Maybe Int) !FixRegions !Annotation !Annotation

  | AForall !Annotation
  | ALam !(Argument Sort) !(Argument SortArgumentRegion) !Annotation

  | AApp !Annotation !(Argument Annotation) !(Argument RegionVar)
  | AInstantiate !Annotation !Tp

  -- Leaf
  | AVar !AnnotationVar
  | ARelation ![RelationConstraint]
  | ABottom

  | AJoin !Annotation !Annotation
  deriving (Eq, Ord)-}
    variables' = mapMap substituteVariableInfo variables
    annotationConstraints' = mapMaybe substituteConstraint annotationConstraints

    substituteVariableInfo :: VariableInfo -> VariableInfo
    substituteVariableInfo (VariableInfo tp annotations regions) = VariableInfo tp (fmap substitute annotations) regions

    substituteConstraint :: Constraint -> Maybe Constraint
    substituteConstraint (CJoin _ _ [arg])
      | all isVar $ argumentFlatten arg = Nothing
      where
        isVar (AVar _) = True
        isVar _ = False
    substituteConstraint (CCall lhs resASort resA resR target arity additionalRegions args kind) = Just $ CCall lhs resASort (fmap substitute resA) resR target' arity additionalRegions (map substituteCallArgument args) kind
      where
        target' = case target of
          Left global -> Left global
          Right (annotation, rThunk, rValue) -> Right (fmap substitute annotation, rThunk, rValue) 
    substituteConstraint (CJoin aSort a as) = Just $ CJoin aSort (fmap substitute a) (map (fmap $ substituteAnnotation 0) as)
    substituteConstraint (CReturn annotations) = Just $ CReturn $ fmap (substituteAnnotation 0) annotations

    substituteCallArgument :: CallArgument -> CallArgument
    substituteCallArgument (CALocal annotations regions) = CALocal (fmap substitute annotations) regions
    substituteCallArgument ca = ca

    stateWithConstraints = MethodState methodTp arity quantors variables' initialExposedRegions initialReturnRegions regionCount emptyRelation annotationConstraints'

lookupLocal :: MethodState -> Id -> VariableInfo
lookupLocal state name = case lookupMap name $ msVariables state of
  Nothing -> error "lookupLocal: Local variable not found"
  Just v -> v

-- Assumes that the variable does not have additional region arguments
lookupVariableAnnotation :: EffectEnvironment -> MethodState -> Variable -> Argument Annotation
lookupVariableAnnotation _ state (VarLocal (Local name _)) = AVar <$> annotation
  where
    VariableInfo _ annotation _ = lookupLocal state name
lookupVariableAnnotation env _ (VarGlobal (GlobalVariable name _)) = annotation'
  where
    EffectGlobal arity tp annotation = eeLookupGlobal env name
    annotation' = fmap stripFirstArgument annotation
    stripFirstArgument (ALam (ArgumentList []) (ArgumentList []) a) = a
    stripFirstArgument _ = error "lookupVariableAnnotation: variable has additional region arguments"
    regionSort = typeRegionSort env (if arity == 0 then tp else tpStrict tp)
    region :: Argument RegionVar
    region = fmap (const regionGlobal) $ (sortArgumentToArgument 1 regionSort :: Argument RegionVar)

lookupVariableRegion :: EffectEnvironment -> MethodState -> Variable -> Argument RegionVar
lookupVariableRegion _ state (VarLocal (Local name _)) = region
  where
    VariableInfo _ _ region = lookupLocal state name
lookupVariableRegion env _ (VarGlobal (GlobalVariable name _)) = region
  where
    EffectGlobal arity tp _ = eeLookupGlobal env name
    regionSort = typeRegionSort env (if arity == 0 then tp else tpStrict tp)
    region :: Argument RegionVar
    region = fmap (const regionGlobal) $ (sortArgumentToArgument 1 regionSort :: Argument RegionVar)

-- Per method:
-- Assign region variables to each variable, store the mapping in a VariablesMap
-- Gather constraints between the variables

-- Per method, per iteration of the fixpoint iteration:
-- Solve the constraints
-- Apply the unifications
-- Remove constraints of the form rho_global >= rho_1

assignVariables :: TypeEnvironment -> EffectEnvironment -> Method -> (Int, [Int], VariablesMap, Argument RegionVar, [RegionVar], Int)
assignVariables typeEnv effectEnv method@(Method _ args' retType _ _ _) =
  ( arity
  , quantors
  , mapFromList (assignment ++ assignmentArguments)
  , returnRegions
  , regionGlobal : argumentFlatten returnRegions ++ (assignmentArguments >>= (\(_, VariableInfo _ _ r) -> argumentFlatten r))
  , freshRegion
  )
  where
    quantors = reverse [ idx | Left (Quantor idx _) <- args']
    args = rights args'

    retType' = tpStrict $ tpFromType quantors $ typeNormalize typeEnv retType

    arity = length args
    lambdaBound = arity + 3

    returnRegions = sortArgumentToArgument 1 $ typeRegionSort effectEnv retType'

    locals = methodLocals False typeEnv method

    ((_, freshRegion), assignment) = mapAccumL assign (0, 0) locals
    assignmentArguments = zipWith assignArgument (enumFromThen (lambdaBound-1) (lambdaBound-2)) args

    assign :: (Int, Int) -> Local -> ((Int, Int), (Id, VariableInfo))
    assign (freshAnnotation, freshRegion) (Local name tp)
      = ((freshAnnotation', freshRegion'), (name, VariableInfo tp' annotation region))
      where
        tp' = tpFromType quantors $ typeNormalize typeEnv tp
        sortAnnotation = typeAnnotationSortArgument effectEnv tp' []
        sortRegion = typeRegionSort effectEnv tp'
        (freshAnnotation', annotation) = sortArgumentToArgument' lambdaBound freshAnnotation sortAnnotation
        (freshRegion', region) = sortArgumentToArgument' lambdaBound freshRegion sortRegion

    assignArgument :: Int -> Local -> (Id, VariableInfo)
    assignArgument lambdaBound' (Local name tp)
      = (name, VariableInfo tp' annotation region)
      where
        tp' = tpFromType quantors $ typeNormalize typeEnv tp
        sortAnnotation = typeAnnotationSortArgument effectEnv tp' []
        sortRegion = typeRegionSort effectEnv tp'
        annotation = sortArgumentToArgument lambdaBound' sortAnnotation
        region = sortArgumentToArgument lambdaBound' sortRegion

gather :: EffectEnvironment -> MethodState -> Method -> [RelationConstraint]
gather env state (Method _ _ _ _ block blocks)
  = gatherInBlock block ++ (blocks >>= gatherInBlock)
  where
    gatherInBlock :: Block -> [RelationConstraint]
    gatherInBlock (Block _ instruction) = gatherInInstruction instruction

    gatherInInstruction :: Instruction -> [RelationConstraint]
    gatherInInstruction (Let name expr next)
      = containment env tp regions
      ++ gatherInExpression regions expr
      ++ gatherInInstruction next
      where
        (VariableInfo tp annotations regions) = lookupLocal state name
    gatherInInstruction (LetAlloc binds next) = (binds >>= gatherInBind) ++ gatherInInstruction next
    gatherInInstruction (Jump _) = []
    gatherInInstruction (Return var)
      = zipWith Outlives (argumentFlatten regions) (argumentFlatten regions')
      where
        regions = lookupVariableRegion env state var
        regions' = msReturnRegion state
    gatherInInstruction (Match var (MatchTargetTuple arity) tps fields next) = gatherInFields regions fields ++ gatherInInstruction next
      where
        (ArgumentList [_, ArgumentList regions]) = lookupVariableRegion env state var
        gatherInFields :: [Argument RegionVar] -> [Maybe Id] -> [RelationConstraint]
        gatherInFields [] [] = []
        gatherInFields (_:_:_:rRest) (Nothing : rest) = gatherInFields rRest rest
        gatherInFields (ArgumentValue rThunk : ArgumentValue rValue : rChild : rRest) (Just field : rest)
          = [rThunk `Outlives` fieldThunk, fieldThunk `Outlives` rThunk, rValue `Outlives` fieldValue, fieldValue `Outlives` rValue]
          ++ zipWith Outlives (argumentFlatten fieldChild) (argumentFlatten rChild)
          ++ zipWith Outlives (argumentFlatten rChild) (argumentFlatten fieldChild)
          ++ gatherInFields rRest rest
          where
            VariableInfo _ _ (ArgumentList fieldRegions) = lookupLocal state field
            (fieldThunk, fieldValue, fieldChild) = case fieldRegions of
              [ArgumentValue fieldThunk, ArgumentValue fieldValue, fieldChild] -> (fieldThunk, fieldValue, fieldChild)
              [ArgumentValue fieldValue, fieldChild] -> (fieldValue, fieldValue, fieldChild)
    gatherInInstruction (Match var (MatchTargetConstructor (DataTypeConstructor name _)) tps fields next) =
      (conSubstitution >>= argumentConstraints) ++ gatherInInstruction next
      where
        (ArgumentList [_, ArgumentList regions]) = lookupVariableRegion env state var

        EffectConstructor _ _ conRegions = eeLookupConstructor env name

        conSubstitution = concat $ zipWith conArgSubstition conRegions fields
        conArgSubstition :: Argument RegionVar -> Maybe Id -> [(RegionVar, Argument RegionVar)]
        conArgSubstition conRegion (Just arg) = findArgumentSubstitution conRegion argRegions
          where
            VariableInfo _ _ argRegions = lookupLocal state arg
        conArgSubstition _ Nothing = []

        argumentConstraints :: (RegionVar, Argument RegionVar) -> [RelationConstraint]
        argumentConstraints (var, conRegion)
          = zipWith Outlives (argumentFlatten conRegion) (argumentFlatten dataRegion)
          ++ zipWith Outlives (argumentFlatten dataRegion) (argumentFlatten conRegion)
          where
            dataRegion = regions !!! indexInArgument var
    gatherInInstruction (Case _ _) = []
    gatherInInstruction (Unreachable _) = []
    gatherInInstruction (RegionRelease _) = []

    gatherInBind :: Bind -> [RelationConstraint]
    gatherInBind (Bind name target args _) =
      containment env tp regions ++ gatherInBindTarget regions target args
      where
        (VariableInfo tp _ regions) = lookupLocal state name

    gatherInBindTarget :: Argument RegionVar -> BindTarget -> [Either Type Variable] -> [RelationConstraint]
    gatherInBindTarget (ArgumentList [_, ArgumentList regions]) (BindTargetTuple arity) args = gatherInElements regions args
      where
        gatherInElements :: [Argument RegionVar] -> [Either Type Variable] -> [RelationConstraint]
        gatherInElements [] [] = []
        gatherInElements rRest (Left tp : rest) = gatherInElements rRest rest
        gatherInElements (ArgumentValue rThunk : ArgumentValue rValue : rFields : rRest) (Right var : rest)
          = [rThunk' `Outlives` rThunk, rValue' `Outlives` rValue, rThunk `Outlives` rThunk', rValue `Outlives` rValue']
          ++ zipWith Outlives (argumentFlatten rFields') (argumentFlatten rFields)
          ++ zipWith Outlives (argumentFlatten rFields) (argumentFlatten rFields')
          ++ gatherInElements rRest rest
          where
            (rThunk', rValue', rFields') = case varRegions of
              ArgumentList [ArgumentValue rThunk', ArgumentValue rValue', rFields'] ->
                (rThunk', rValue', rFields')
              ArgumentList [ArgumentValue rValue', rFields'] ->
                (rValue', rValue', rFields')
            varRegions = lookupVariableRegion env state var
        gatherInElements as bs = error ("gatherInBindTarget: Invalid arguments: " ++ show as ++ "; " ++ show bs)
    gatherInBindTarget (ArgumentList [_, ArgumentList regions]) (BindTargetConstructor (DataTypeConstructor name _)) args =
      conSubstitution >>= argumentConstraints
      where
        EffectConstructor _ _ conRegions = eeLookupConstructor env name
        conSubstitution = concat $ zipWith conArgSubstition conRegions (rights args)
        conArgSubstition :: Argument RegionVar -> Variable -> [(RegionVar, Argument RegionVar)]
        conArgSubstition conRegion arg = findArgumentSubstitution conRegion argRegions
          where
            argRegions = lookupVariableRegion env state arg
        argumentConstraints :: (RegionVar, Argument RegionVar) -> [RelationConstraint]
        argumentConstraints (var, conRegion) = zipWith Outlives (argumentFlatten conRegion) (argumentFlatten dataRegion)
          where
            dataRegion = regions !!! indexInArgument var
    -- BindTargetFunction or BindTargetThunk
    gatherInBindTarget (ArgumentList (ArgumentValue rThunk : _)) target args
      = targetConstraint ++ argumentConstraints
      where
        targetConstraint = case target of
          BindTargetThunk (VarLocal (Local name _)) ->
            let VariableInfo _ _ (ArgumentList (ArgumentValue r : _)) = lookupLocal state name
            in [r `Outlives` rThunk]
          _ -> []
        argumentConstraints = args >>= argConstraint
        argConstraint :: Either Type Variable -> [RelationConstraint]
        argConstraint (Right (VarLocal (Local name _))) = [r `Outlives` rThunk]
          where
            VariableInfo _ _ (ArgumentList (ArgumentValue r : _)) = lookupLocal state name
        argConstraint _ = []

    gatherInExpression :: Argument RegionVar -> Expr -> [RelationConstraint]
    gatherInExpression regions (Literal _) = []
    gatherInExpression regions (Call _ _) = []
    gatherInExpression regions (Instantiate var _) = substitution >>= constraints
      where
        substitution = findArgumentSubstitution (lookupVariableRegion env state var) regions
        constraints (r1, rs) = map (`Outlives` r1) $ argumentFlatten rs
    gatherInExpression (ArgumentList [ArgumentValue regionValue, regions]) (Eval var)
      = Outlives regionValue regionValue' : Outlives regionValue' regionValue : concat (zipWith (\r1 r2 -> [Outlives r1 r2, Outlives r2 r1]) (argumentFlatten regions) (argumentFlatten regions'))
      where
        ArgumentList [_, ArgumentValue regionValue', regions'] = lookupVariableRegion env state var
    gatherInExpression (ArgumentList [_, ArgumentValue regionValue, regions]) (CastThunk var)
      = Outlives regionValue regionValue' : Outlives regionValue' regionValue : concat (zipWith (\r1 r2 -> [Outlives r1 r2, Outlives r2 r1]) (argumentFlatten regions) (argumentFlatten regions'))
      where
        ArgumentList [ArgumentValue regionValue', regions'] = lookupVariableRegion env state var
    gatherInExpression regions (Var var)
      = concat (zipWith (\r1 r2 -> [Outlives r1 r2, Outlives r2 r1]) (argumentFlatten regions) (argumentFlatten regions'))
      where
        regions' = lookupVariableRegion env state var
    gatherInExpression regions (Seq _ var) = gatherInExpression regions (Var var)
    gatherInExpression regions (Phi branches)
      = branches >>= gatherInBranch
      where
        gatherInBranch :: PhiBranch -> [RelationConstraint]
        gatherInBranch (PhiBranch _ var) = zipWith Outlives (argumentFlatten regions') (argumentFlatten regions)
          where
            regions' = lookupVariableRegion env state var
    gatherInExpression regions (Cast _ _) = error "gather: Cast expression is not supported"
    gatherInExpression regions (PrimitiveExpr _ _) = [] -- Assumes that primitives do not operate on objects
    gatherInExpression regions (Undefined _) = []
    gatherInExpression regions RegionAllocate = error "methodInitialize: method was already region-annnotated"

constraints :: EffectEnvironment -> MethodState -> Method -> [Constraint]
constraints env state (Method _ _ _ _ block blocks)
  = constraintsInBlock block ++ (blocks >>= constraintsInBlock)
  where
    constraintsInBlock :: Block -> [Constraint]
    constraintsInBlock (Block _ instruction) = constraintsInInstruction instruction

    constraintsInInstruction :: Instruction -> [Constraint]
    constraintsInInstruction (Let name expr next) = constraintsInExpression name result expr ++ constraintsInInstruction next
      where
        result = lookupLocal state name

    constraintsInInstruction (LetAlloc binds next) = (binds >>= constraintsInBind) ++ constraintsInInstruction next
    constraintsInInstruction (Jump _) = []
    constraintsInInstruction (Match (VarLocal (Local var _)) (MatchTargetTuple arity) _ args next)
      = concat (zipWith fieldConstraints objectAnnotations args) ++ constraintsInInstruction next
      where
        VariableInfo _ (ArgumentList objectAnnotations) _ = lookupLocal state var
        fieldConstraints _ Nothing = []
        fieldConstraints objectAnnotation (Just name) = [CJoin annotationSort annotations [AVar <$> objectAnnotation]]
          where
            VariableInfo tp annotations _ = lookupLocal state name
            annotationSort = typeAnnotationSortArgument env tp []
    constraintsInInstruction (Match (VarLocal (Local var _)) (MatchTargetConstructor (DataTypeConstructor name _)) _ args next)
      = {- constructorConstraints constructor objectAnnotations argAnnotations (\(AnnotationVar i) -> i) constraintField (\_ _ -> [])
      ++ constraintsInInstruction next -}
      [] -- TODO: constraints for constructor match
      where
        {- VariableInfo _ objectAnnotations _ = lookupLocal state var
        EffectConstructor constructor _ _ = eeLookupConstructor env name
        argAnnotations = map argAnnotation args
        argAnnotation (Just name) = Right $ (typeAnnotationSortArgument env tp [], annotation)
          where
            VariableInfo tp annotation _ = lookupLocal state name
        argAnnotation Nothing = Left ()

        constraintField fieldSort fieldVar localVar = [CJoin (ArgumentValue fieldSort) (ArgumentValue fieldVar) [ArgumentValue localVar]] -}
    constraintsInInstruction (Case _ _) = []
    constraintsInInstruction (Return var) = [CReturn $ lookupVariableAnnotation env state var]
    constraintsInInstruction (Unreachable _) = []
    constraintsInInstruction (RegionRelease _) = []

    constraintsInBind :: Bind -> [Constraint]
    constraintsInBind bind@(Bind name target args _) = constraintsInBindTarget name result target args
      where
        result = lookupLocal state name

    constraintsInBindTarget :: Id -> VariableInfo -> BindTarget -> [Either Type Variable] -> [Constraint]
    constraintsInBindTarget lhs result (BindTargetFunction fn) args = call lhs result (Left fn) args CKAllocThunk
    constraintsInBindTarget lhs result (BindTargetThunk var) args = call lhs result (Right var) args CKAllocThunk
    constraintsInBindTarget _ (VariableInfo _ resultAnnotations _) (BindTargetConstructor (DataTypeConstructor name _)) args = [] -- TODO: constructor constraints
      {-constructorConstraints constructor resultAnnotations argAnnotations (\(AnnotationVar i) -> i) constraintVar (\_ _ -> [])
      where
        EffectConstructor _ constructorToData _ = eeLookupConstructor env name
        argAnnotations :: [Either Id (Argument Sort, Argument AnnotationVar)]
        argAnnotations = fmap argAnnotation $ rights args
        argAnnotation (VarLocal (Local name _)) = Right (typeAnnotationSortArgument env tp [], annotation)
          where
            VariableInfo tp annotation _ = lookupLocal state name
        argAnnotation (VarGlobal (GlobalVariable name _)) = Left name
        constraintVar sort resultVar fieldVar = [CJoin (ArgumentValue sort) (ArgumentValue resultVar) [ArgumentValue fieldVar]] -}
    constraintsInBindTarget _ (VariableInfo tp (ArgumentList resultAnnotations) _) (BindTargetTuple arity) args
      = concat $ zipWith3 fieldConstraint (rights args) resultAnnotationSorts resultAnnotations
      where
        ArgumentList resultAnnotationSorts = typeAnnotationSortArgument env tp []
        fieldConstraint var resultAnnotationSort resultAnnotation = [CJoin resultAnnotationSort resultAnnotation [lookupVariableAnnotation env state var]]

    constraintsInExpression :: Id -> VariableInfo -> Expr -> [Constraint]
    constraintsInExpression lhs result (Var var) = call lhs result (Right var) [] CKInstantiate
    constraintsInExpression lhs result (Seq _ var) = call lhs result (Right var) [] CKInstantiate
    constraintsInExpression lhs result (Eval var) = call lhs result (Right var) [] CKInstantiate
    constraintsInExpression lhs result (CastThunk var) = call lhs result (Right var) [] CKInstantiate
    constraintsInExpression lhs result (Instantiate var tps) = call lhs result (Right var) (map Left tps) CKInstantiate
    constraintsInExpression lhs result (Call fn args) = call lhs result (Left fn) args CKCall
    constraintsInExpression lhs (VariableInfo tp resultAnnotations _) (Phi branches) =
      [CJoin resultSort resultAnnotations $ map branchAnnotations branches]
      where
        resultSort = typeAnnotationSortArgument env tp []
        branchAnnotations (PhiBranch _ var) = lookupVariableAnnotation env state var
    constraintsInExpression _ _ _ = []

    call :: Id -> VariableInfo -> Either GlobalFunction Variable -> [Either Type Variable] -> CallKind -> [Constraint]
    call lhs (VariableInfo tp resultAnnotation resultRegion) target args callKind
      = case callTarget of
          Right (annotations, _, _)
            | null args && callKind == CKInstantiate -> [CJoin resultAnnotationSort resultAnnotation [fmap AVar annotations]]
          _ -> [CCall lhs resultAnnotationSort resultAnnotation resultRegion callTarget callTargetArity [] args' callKind]
      where
        resultAnnotationSort = typeAnnotationSortArgument env tp []
        (callTarget, callTargetArity) = case target of
          Left (GlobalFunction name arity _) -> (Left name, arity)
          Right (VarGlobal (GlobalVariable name _)) -> (Left name, 0)
          Right (VarLocal (Local name _)) ->
            let
              VariableInfo _ annotation (ArgumentList regions) = lookupLocal state name
              (rThunk, rValue) = case regions of
                [ArgumentValue r, _] -> (r, r)
                [ArgumentValue r1, ArgumentValue r2, _] -> (r1, r2)
            in (Right (annotation, rThunk, rValue), 0)
        args' = map argumentAnnotationRegion args
        argumentAnnotationRegion :: Either Type Variable -> CallArgument
        argumentAnnotationRegion (Left tp) = CAType $ tpFromType (msQuantors state) tp
        argumentAnnotationRegion (Right (VarLocal (Local name _))) = CALocal annotation region
          where
            VariableInfo _ annotation region = lookupLocal state name
        argumentAnnotationRegion (Right var) = CAGlobal annotation $ lookupVariableRegion env state var
          where
            annotation = lookupVariableAnnotation env state var

constructorConstraints :: (Show a, Show c, Show s) => [Argument a] -> Argument a -> [Either c (Argument s, Argument a)] -> (a -> Int) -> (s -> a -> a -> [b]) -> (c -> Argument a -> [b]) -> [b]
constructorConstraints constructor (ArgumentList dataType) fields index f g = concat $ zipWith handleField constructor fields
  where
    handleField arg (Left c) = g c arg
    handleField arg (Right (sort, arg')) = fieldConstraints arg sort arg'
    fieldConstraints (ArgumentValue var) sort field = concat $ zipFlattenArgumentWithSort f sort (dataType !!! index var) field
    fieldConstraints (ArgumentList as) (ArgumentList sorts) (ArgumentList bs) = concat $ zipWith3 fieldConstraints as sorts bs

methodApplyRelationConstraints :: [RelationConstraint] -> MethodState -> MethodState
methodApplyRelationConstraints relationConstraints state@(MethodState methodType arity quantors varMap exposedRegions returnRegion regionCount _ constraints) =
  MethodState methodType arity quantors (mapMap substituteVariableInfo varMap) exposedRegions returnRegion regionCount' relation (map substituteConstraint constraints)
  where
    (substitution, relation, regionCount') = relationFromConstraints (msAdditionalArgumentScope state) regionCount exposedRegions relationConstraints

    substitute :: RegionVar -> RegionVar
    substitute (RegionVar idx) = case IntMap.lookup idx substitution of
      Just idx' -> idx'
      Nothing -> RegionVar idx

    substituteVariableInfo :: VariableInfo -> VariableInfo
    substituteVariableInfo (VariableInfo tp annotation region) = VariableInfo tp annotation (fmap substitute region)

    substituteConstraint :: Constraint -> Constraint
    substituteConstraint (CCall result resultAnnotationSort resultAnnotation resultRegion target arity additionalRegions arguments kind)
      = CCall result resultAnnotationSort resultAnnotation resultRegion' target' arity (map substitute additionalRegions) arguments' kind
      where
        resultRegion' = fmap substitute resultRegion
        arguments' = map substituteCallArgument arguments
        target' = case target of
          Left global -> Left global
          Right (annotation, rThunk, rValue) -> Right (annotation, substitute rThunk, substitute rValue)
    substituteConstraint (CJoin aSort a as) = CJoin aSort a as
    substituteConstraint c = c -- CReturn

    substituteCallArgument :: CallArgument -> CallArgument
    substituteCallArgument (CALocal argAnnotation argRegion) = CALocal argAnnotation $ fmap substitute argRegion
    substituteCallArgument ca = ca

constraintSimpleUnifications :: [Constraint] -> [(Int, Int)]
constraintSimpleUnifications (CJoin _ argLeft [argRight] : cs) = unifications ++ constraintSimpleUnifications cs
  where
    unifications = zipFlattenArgument (\(AnnotationVar a) (AVar (AnnotationVar b)) -> if a < b then (a, b) else (b, a)) argLeft argRight
constraintSimpleUnifications (_ : cs) = constraintSimpleUnifications cs
constraintSimpleUnifications [] = []

constraintSimpleUnificationsMap :: [Constraint] -> IntMap Int
constraintSimpleUnificationsMap cs = insertUnifications list IntMap.empty
  where
    insertUnifications :: [(Int, Int)] -> IntMap Int -> IntMap Int
    insertUnifications ((a, b) : us) m = insertUnifications rest $! m'
      where
        m' = foldr (\b' -> IntMap.insert b' a') m bs
        a' = fromMaybe a $ IntMap.lookup a m
        bs = b : map snd groupUnifications
        (groupUnifications, rest) = span (\(a'', _) -> a == a'') us
    insertUnifications [] m = m
    list = sort $ constraintSimpleUnifications cs

type BlockInstructions = [(Id, Instruction -> Instruction)]

hoistGlobalVariables :: EffectEnvironment -> NameSupply -> Method -> Method
hoistGlobalVariables env nameSupply (Method tp args ret annotations b bs) = Method tp args ret annotations b'' bs''
  where
    (nameSupply1, nameSupply2) = splitNameSupply nameSupply

    (blockInstructions1, b') = hoistInBlock nameSupply1 b
    (blockInstructions2, bs') = unzip $ mapWithSupply hoistInBlock nameSupply2 bs
    blockInstructions = blockInstructions1 ++ concat blockInstructions2

    b'' = blockAddInstructions b'
    bs'' = map blockAddInstructions bs'

    blockAddInstructions (Block name instruction) = Block name $ foldr id instruction instrs
      where
        instrs = map snd $ filter ((name ==) . fst) blockInstructions

    hoistInBlock :: NameSupply -> Block -> (BlockInstructions, Block)
    hoistInBlock supply (Block name instr) = Block name <$> hoist supply instr

    hoist :: NameSupply -> Instruction -> (BlockInstructions, Instruction)
    hoist supply (Let name expr next) = (blockInstr ++ nextBlockInstr, instr $ Let name expr' next')
      where
        (supplyExpr, supplyNext) = splitNameSupply supply
        (blockInstr, instr, expr') = hoistInExpr supplyExpr expr
        (nextBlockInstr, next') = hoist supplyNext next
    hoist supply (LetAlloc binds next) = foldr fmap (LetAlloc binds' <$> hoist supplyNext next) instrs
      where
        (supplyBinds, supplyNext) = splitNameSupply supply
        (instrs, binds') = unzip $ mapWithSupply hoistInBind supplyBinds binds
    hoist supply (Match var target instantiation fields next) = instr . Match var' target instantiation fields <$> hoist supply next
      where
        (supplyVar, supplyNext) = splitNameSupply supply
        (instr, var') = hoistVariableForced supplyVar var
    hoist supply (Case var alts) = ([], instr $ Case var' alts)
      where
        (instr, var') = hoistVariable supply var
    hoist supply (Return var) = ([], instr $ Return var')
      where
        (instr, var') = hoistVariable supply var
    hoist supply (Unreachable (Just var)) = ([], instr $ Unreachable $ Just var')
      where
        (instr, var') = hoistVariable supply var
    hoist supply instr = ([], instr) -- Jump _, Unreachable Nothing

    hoistInExpr :: NameSupply -> Expr -> (BlockInstructions, Instruction -> Instruction, Expr)
    hoistInExpr supply (Call fn arguments) = ([], flip (foldr id) instrs, Call fn arguments')
      where
        (instrs, arguments') = unzip $ mapWithSupply hoistArgument supply arguments
    hoistInExpr supply (Eval var) = ([], instr, Eval var')
      where
        (instr, var') = hoistVariable supply var
    hoistInExpr supply (CastThunk var) = ([], instr, CastThunk var')
      where
        (instr, var') = hoistVariable supply var
    hoistInExpr supply (Phi branches) = (concat branchInstructions, id, Phi branches')
      where
        (branchInstructions, branches') = unzip $ mapWithSupply hoistPhiBranch supply branches
    hoistInExpr supply (PrimitiveExpr name arguments) = ([], flip (foldr id) instrs, PrimitiveExpr name arguments')
      where
        (instrs, arguments') = unzip $ mapWithSupply hoistArgument supply arguments
    hoistInExpr supply expr = ([], id, expr) -- Literal, Undefined, Var, Instantiate

    hoistInBind :: NameSupply -> Bind -> (Instruction -> Instruction, Bind)
    hoistInBind supply (Bind local target arguments region) = (instrTarget . flip (foldr id) instrsArguments, Bind local target' arguments' region)
      where
        (supplyTarget, supplyArguments) = splitNameSupply supply
        (instrTarget, target') = case target of
          BindTargetThunk var -> BindTargetThunk <$> hoistVariable supplyTarget var
          _ -> (id, target)
        (instrsArguments, arguments') = unzip $ mapWithSupply hoistArgument supplyArguments arguments

    hoistArgument :: NameSupply -> Either Type Variable -> (Instruction -> Instruction, Either Type Variable)
    hoistArgument supply (Left tp) = (id, Left tp)
    hoistArgument supply (Right var) = Right <$> hoistVariable supply var

    hoistVariable :: NameSupply -> Variable -> (Instruction -> Instruction, Variable)
    hoistVariable supply var = fromMaybe (id, var) $ hoistVariable' supply var

    hoistVariable' :: NameSupply -> Variable -> Maybe (Instruction -> Instruction, Variable)
    hoistVariable' supply var@(VarGlobal (GlobalVariable name tp))
      | globalHasAdditionalRegions (eeLookupGlobal env name)
        = Just (Let local $ Var var, VarLocal $ Local local tp)
      where
        (local, _) = freshIdFromId name supply
    hoistVariable' _ _ = Nothing

    hoistVariableForced :: NameSupply -> Variable -> (Instruction -> Instruction, Variable)
    hoistVariableForced supply var@(VarGlobal (GlobalVariable name tp))
      = (Let local $ Var var, VarLocal $ Local local tp)
      where
        (local, _) = freshIdFromId name supply
    hoistVariableForced supply var = (id, var)

    hoistPhiBranch :: NameSupply -> PhiBranch -> (BlockInstructions, PhiBranch)
    hoistPhiBranch supply branch@(PhiBranch name var) = case hoistVariable' supply var of
      Nothing -> ([], branch)
      Just (instr, var') -> ([(name, instr)], PhiBranch name var')

-- Assigns additional region variables to CCall constraints
-- The 'count' function is only applied with CCall constraints
assignAdditionalRegionVariables :: (Constraint -> Int) -> (Constraint -> [RegionVar] -> [RegionVar]) -> MethodState -> MethodState
assignAdditionalRegionVariables count f state
  = state{msConstraints = constraints, msRegionCount = regionCount}
  where
    (regionCount, constraints) = mapAccumL assign (msRegionCount state) (msConstraints state)
    assign :: Int -> Constraint -> (Int, Constraint)
    assign fresh constraint@CCall{} =
      ( fresh + regionCount
      , constraint{ cCallAdditionalRegions = cCallAdditionalRegions constraint ++ f constraint regions }
      )
      where
        regionCount = count constraint
        regions = map (variableFromIndices (msAdditionalArgumentScope state)) $ take regionCount [fresh..]
    assign fresh constraint = (fresh, constraint)

assignIntermediateThunkRegions :: MethodState -> MethodState
assignIntermediateThunkRegions = assignAdditionalRegionVariables count (const id)
  where
    count call = max 0 $ values - arity - 1
      where
        values = length (filter isValueArgument $ cCallArguments call)
        arity = cCallTargetArity call

isValueArgument :: CallArgument -> Bool
isValueArgument (CAGlobal _ _) = True
isValueArgument (CALocal _ _) = True
isValueArgument _ = False
