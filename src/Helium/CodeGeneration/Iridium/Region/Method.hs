module Helium.CodeGeneration.Iridium.Region.Method where

import Data.List
import Data.Either
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

data MethodState = MethodState 
  { msGlobalRegion :: !RegionVar
  , msVariables :: !VariablesMap
  , msReturn :: !(Argument RegionVar)
  , msRegions :: !IntSet
  , msRelation :: !Relation -- Relation derived from instructions (lower order)
  , msConstraints :: ![Constraint] -- Constraints derived from calls and thunk allocations (higher order)
  , msAnnotations :: IntMap Annotation
  }

instance Show MethodState where
  show (MethodState global vars ret _ relation constraints annotations) = unlines $ map ("  " ++)
    [ "ρ_global = " ++ show global
    , "variable mapping:\n" ++ showVariablesMap vars
    , "Return region: " ++ show ret
    , "Relation: " ++ show relation
    , "Constraints:" ++ (constraints >>= (("\n    " ++) . show))
    , "Annotations:" ++ showAnnotationsMap annotations
    ]

data CallKind = CKCall | CKAllocThunk | CKInstantiate deriving Eq

data Constraint
  = CCall
    { cCallResultAnnotation :: !(Argument AnnotationVar)
    , cCallResultRegion :: !(Argument RegionVar)
    , cCallTarget :: !(Either Id (Argument AnnotationVar)) -- Left for a call to a global function, right for a higher order call
    , cCallArguments :: ![CallArgument]
    , cCallKind :: !CallKind
    }
  | CJoin !AnnotationVar ![AnnotationVar] 

data CallArgument
  = CAType !Type
  | CALocal !(Argument AnnotationVar) !(Argument RegionVar)
  | CAGlobal !Id

instance Show CallKind where
  show CKCall = "call"
  show CKAllocThunk = "alloc_thunk"
  show CKInstantiate = "instantiate"

instance Show Constraint where
  show (CJoin a as) = show a ++ " := join(" ++ intercalate ", " (map show as) ++ ")"
  show (CCall resA resR target args kind) = "[" ++ show resA ++ "; " ++ show resR ++ "] := " ++ show kind ++ " " ++ targetString ++ argsString
    where
      targetString = case target of
        Left name -> "@" ++ showId name ""
        Right annotations -> show annotations
      argsString = "(" ++ intercalate ", " (map show args) ++ ")"
      showArg (Left tp) = "{ " ++ showType [] tp ++ " }"
      showArg (Right (annotations, regions)) = "[" ++ show annotations ++ ";" ++ show regions ++ "]"

instance Show CallArgument where
  show (CAType tp) = "{ " ++ showType [] tp ++ " }"
  show (CALocal annotations regions) = "[" ++ show annotations ++ "; " ++ show regions ++ "]"
  show (CAGlobal name) = "@" ++ showId name ""

data VariableInfo = VariableInfo !Type !(Argument AnnotationVar) !(Argument RegionVar)
type VariablesMap = IdMap VariableInfo

showVariablesMap :: VariablesMap -> String
showVariablesMap vars = intercalate "\n" $ map (\(var, info) -> "    %" ++ showId var (": " ++ show info)) $ listFromMap vars

instance Show VariableInfo where
  show (VariableInfo tp annotation region) = showType [] tp ++ " [" ++ show annotation ++ "; " ++ show region ++ "]"

showAnnotationsMap :: IntMap Annotation -> String
showAnnotationsMap m = IntMap.toList m >>= showAnnotation
  where
    showAnnotation (idx, annotation) = "\n    " ++ show (AnnotationVar idx) ++ " = " ++ show annotation

methodInitialize :: TypeEnvironment -> EffectEnvironment -> Method -> MethodState
methodInitialize typeEnv effectEnv method@(Method _ _ returnType _ _ _) = undefined
  where
    (variables, freshAnnotation, freshRegion, annotations) = assignVariables typeEnv effectEnv method
    (initialGlobalRegion : freshRegion'@(RegionVar nextRegion: _), returnRegions) = sortArgumentToParameter freshRegion $ typeRegionSort effectEnv returnType
    allRegions = IntSet.fromDistinctAscList [0 .. nextRegion - 1]

    initialState = MethodState initialGlobalRegion variables (parameterToArgument returnRegions) allRegions emptyRelation [] $ IntMap.fromList annotations

    relationConstraint = gather effectEnv initialState method 
    annotationConstraints = constraints effectEnv initialState method

lookupLocal :: MethodState -> Id -> VariableInfo
lookupLocal state name = case lookupMap name $ msVariables state of
  Nothing -> error "lookupLocal: Local variable not found"
  Just v -> v

lookupVariableRegion :: EffectEnvironment -> MethodState -> Variable -> Argument RegionVar
lookupVariableRegion env state (VarLocal (Local name _)) = region
  where
    VariableInfo _ _ region = lookupLocal state name
lookupVariableRegion env state (VarGlobal (GlobalVariable name tp)) = region
  where
    regionSort = typeRegionSort env tp
    region :: Argument RegionVar
    region = fmap (const $ msGlobalRegion state) $ parameterToArgument $ snd $ sortArgumentToParameter [0..] regionSort

-- Per method:
-- Assign region variables to each variable, store the mapping in a VariablesMap
-- Gather constraints between the variables

-- Per method, per iteration of the fixpoint iteration:
-- Solve the constraints
-- Apply the unifications
-- Remove constraints of the form rho_global >= rho_1

assignVariables :: TypeEnvironment -> EffectEnvironment -> Method -> (VariablesMap, [AnnotationVar], [RegionVar], [(Int, Annotation)])
assignVariables typeEnv effectEnv method = (mapFromList assignment, freshAnnotationFinal, freshRegionFinal, annotationsFinal)
  where
    locals = methodLocals typeEnv method
    ((freshAnnotationFinal, freshRegionFinal, annotationsFinal), assignment) = mapAccumL assign (map AnnotationVar [0..], map RegionVar [0..], []) locals
    assign :: ([AnnotationVar], [RegionVar], [(Int, Annotation)]) -> Local -> (([AnnotationVar], [RegionVar], [(Int, Annotation)]), (Id, VariableInfo))
    assign (freshAnnotation, freshRegion, annotations) (Local name tp)
      = ((freshAnnotation', freshRegion', annotations' ++ annotations), (name, VariableInfo tp argAnnotation (parameterToArgument region)))
      where
        tp' = typeNormalize typeEnv tp
        sortAnnotation = typeAnnotationSortArgument effectEnv tp' []
        sortRegion = typeRegionSort effectEnv tp'
        argAnnotation = parameterToArgument annotation
        annotations' = map (\(AnnotationVar idx) -> (idx, ABottom)) $ argumentFlatten argAnnotation
        (freshAnnotation', annotation) = sortArgumentToParameter freshAnnotation sortAnnotation
        (freshRegion', region) = sortArgumentToParameter freshRegion sortRegion


gather :: EffectEnvironment -> MethodState -> Method -> [RelationConstraint]
gather env state (Method _ _ _ _ block blocks)
  = gatherInBlock block ++ (blocks >>= gatherInBlock)
  where
    gatherInBlock :: Block -> [RelationConstraint]
    gatherInBlock (Block _ instruction) = gatherInInstruction instruction

    gatherInInstruction :: Instruction -> [RelationConstraint]
    gatherInInstruction (Let name expr next)
      = containment env tp regions
      ++ gatherInExpression tp regions expr
      ++ gatherInInstruction next
      where
        (VariableInfo tp annotations regions) = lookupLocal state name
    gatherInInstruction (LetAlloc binds next) = (binds >>= gatherInBind) ++ gatherInInstruction next
    gatherInInstruction (Jump _) = []
    gatherInInstruction (Return var)
      = zipWith Outlives (argumentFlatten regions) (argumentFlatten regions')
      where
        regions = lookupVariableRegion env state var
        regions' = msReturn state
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
              [ArgumentValue fieldThunk, ArgumentValue fieldValue, fieldChildren] -> (fieldThunk, fieldValue, fieldChild)
              [ArgumentValue fieldValue, fieldChildren] -> (fieldValue, fieldValue, fieldChild)
    gatherInInstruction (Match var (MatchTargetConstructor (DataTypeConstructor name _)) tps fields next) =
      (conSubstitution >>= argumentConstraints) ++ gatherInInstruction next
      where
        (ArgumentList [_, ArgumentList regions]) = lookupVariableRegion env state var

        EffectConstructor _ conRegions = eeLookupConstructor env name

        conSubstitution = concat $ zipWith conArgSubstition conRegions fields
        conArgSubstition :: Argument RegionVar -> Maybe Id -> [(RegionVar, Argument RegionVar)]
        conArgSubstition conRegion (Just arg) = findArgumentSubstitution conRegion argRegions
          where
            VariableInfo _ _ argRegions = lookupLocal state arg
        argumentConstraints :: (RegionVar, Argument RegionVar) -> [RelationConstraint]
        argumentConstraints (RegionVar index, conRegion)
          = zipWith Outlives (argumentFlatten conRegion) (argumentFlatten dataRegion)
          ++ zipWith Outlives (argumentFlatten dataRegion) (argumentFlatten conRegion)
          where
            dataRegion = regions !! index
    gatherInInstruction (Case _ _) = []
    gatherInInstruction (Unreachable _) = []

    gatherInBind :: Bind -> [RelationConstraint]
    gatherInBind (Bind name target args) =
      containment env tp regions ++ gatherInBindTarget regions target args
      where
        (VariableInfo tp _ regions) = lookupLocal state name

    gatherInBindTarget :: Argument RegionVar -> BindTarget -> [Either Type Variable] -> [RelationConstraint]
    gatherInBindTarget (ArgumentList regions) (BindTargetTuple arity) args = gatherInElements regions args
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
    gatherInBindTarget (ArgumentList [_, ArgumentList regions]) (BindTargetConstructor (DataTypeConstructor name _)) args =
      conSubstitution >>= argumentConstraints
      where
        EffectConstructor _ conRegions = eeLookupConstructor env name
        conSubstitution = concat $ zipWith conArgSubstition conRegions (rights args)
        conArgSubstition :: Argument RegionVar -> Variable -> [(RegionVar, Argument RegionVar)]
        conArgSubstition conRegion arg = findArgumentSubstitution conRegion argRegions
          where
            argRegions = lookupVariableRegion env state arg
        argumentConstraints :: (RegionVar, Argument RegionVar) -> [RelationConstraint]
        argumentConstraints (RegionVar index, conRegion) = zipWith Outlives (argumentFlatten conRegion) (argumentFlatten dataRegion)
          where
            dataRegion = regions !! index
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

    gatherInExpression :: Type -> Argument RegionVar -> Expr -> [RelationConstraint]
    gatherInExpression tp regions (Literal _) = []
    gatherInExpression tp regions (Call _ _) = []
    gatherInExpression tp regions (Instantiate var tps) = [] -- TODO
    gatherInExpression tp (ArgumentList [ArgumentValue regionValue, regions]) (Eval var)
      = Outlives regionValue regionValue' : Outlives regionValue' regionValue : concat (zipWith (\r1 r2 -> [Outlives r1 r2, Outlives r2 r1]) (argumentFlatten regions) (argumentFlatten regions'))
      where
        ArgumentList [_, ArgumentValue regionValue', regions'] = lookupVariableRegion env state var
    gatherInExpression tp (ArgumentList [_, ArgumentValue regionValue, regions]) (CastThunk var)
      = Outlives regionValue regionValue' : Outlives regionValue' regionValue : concat (zipWith (\r1 r2 -> [Outlives r1 r2, Outlives r2 r1]) (argumentFlatten regions) (argumentFlatten regions'))
      where
        ArgumentList [ArgumentValue regionValue', regions'] = lookupVariableRegion env state var
    gatherInExpression tp regions (Var var)
      = concat (zipWith (\r1 r2 -> [Outlives r1 r2, Outlives r2 r1]) (argumentFlatten regions) (argumentFlatten regions'))
      where
        regions' = lookupVariableRegion env state var
    gatherInExpression tp regions (Seq _ var) = gatherInExpression tp regions (Var var)
    gatherInExpression tp regions (Phi branches)
      = branches >>= gatherInBranch
      where
        gatherInBranch :: PhiBranch -> [RelationConstraint]
        gatherInBranch (PhiBranch _ var) = zipWith Outlives (argumentFlatten regions') (argumentFlatten regions)
          where
            regions' = lookupVariableRegion env state var
    gatherInExpression tp regions (Cast _ _) = error "gather: Cast expression is not supported"
    gatherInExpression tp regions (PrimitiveExpr _ _) = [] -- Assumes that primitives do not operate on objects
    gatherInExpression tp regions (Undefined _) = []

constraints :: EffectEnvironment -> MethodState -> Method -> [Constraint]
constraints env state (Method _ _ _ _ block blocks)
  = constraintsInBlock block ++ (blocks >>= constraintsInBlock)
  where
    constraintsInBlock :: Block -> [Constraint]
    constraintsInBlock (Block _ instruction) = constraintsInInstruction instruction

    constraintsInInstruction :: Instruction -> [Constraint]
    constraintsInInstruction (Let name expr next) = constraintsInExpression result expr ++ constraintsInInstruction next
      where
        result = lookupLocal state name

    constraintsInInstruction (LetAlloc binds next) = (binds >>= constraintsInBind) ++ constraintsInInstruction next
    constraintsInInstruction (Jump _) = []
    constraintsInInstruction (Match (VarGlobal _) _ _ _ _) = error "Region inference does not yet support global variables as scrutinee of Match instruction"
    constraintsInInstruction (Match (VarLocal (Local var _)) (MatchTargetTuple arity) _ args next)
      = concat (zipWith fieldConstraints objectAnnotations args) ++ constraintsInInstruction next
      where
        VariableInfo _ (ArgumentList objectAnnotations) _ = lookupLocal state var
        fieldConstraints _ Nothing = []
        fieldConstraints objectAnnotation (Just name) = zipFlattenArgument (\a b -> CJoin a [b]) annotations objectAnnotation
          where
            VariableInfo _ annotations _ = lookupLocal state name
    constraintsInInstruction (Match (VarLocal (Local var _)) (MatchTargetConstructor (DataTypeConstructor name _)) _ args next)
      = constructorConstraints constructor objectAnnotations argAnnotations (\(AnnotationVar i) -> i) constraintField (\_ _ -> [])
      ++ constraintsInInstruction next
      where
        VariableInfo _ objectAnnotations _ = lookupLocal state var
        EffectConstructor constructor _ = eeLookupConstructor env name
        argAnnotations = map argAnnotation args
        argAnnotation (Just name) = Right annotation
          where
            VariableInfo _ annotation _ = lookupLocal state name
        argAnnotation Nothing = Left ()

        constraintField fieldVar localVar = [CJoin fieldVar [localVar]]
    constraintsInInstruction (Case _ _) = []
    constraintsInInstruction (Return _) = []
    constraintsInInstruction (Unreachable _) = []

    constraintsInBind :: Bind -> [Constraint]
    constraintsInBind (Bind name target args) = constraintsInBindTarget result target args
      where
        result = lookupLocal state name

    constraintsInBindTarget :: VariableInfo -> BindTarget -> [Either Type Variable] -> [Constraint]
    constraintsInBindTarget result (BindTargetFunction fn) args = call result (Left fn) args CKAllocThunk
    constraintsInBindTarget result (BindTargetThunk var) args = call result (Right var) args CKAllocThunk
    constraintsInBindTarget (VariableInfo _ resultAnnotations _) (BindTargetConstructor (DataTypeConstructor name _)) args = constructorConstraints constructor resultAnnotations argAnnotations (\(AnnotationVar i) -> i) constraintLocal constraintGlobal
      where
        EffectConstructor constructor _ = eeLookupConstructor env name
        argAnnotations = [ argAnnotation arg | Right arg <- args ]
        argAnnotation (VarLocal (Local name _)) = Right annotation
          where
            VariableInfo _ annotation _ = lookupLocal state name
        argAnnotation (VarGlobal (GlobalVariable name _)) = Left name

        constraintGlobal :: Id -> Argument AnnotationVar -> [Constraint]
        constraintGlobal name resultArg = [CCall resultArg (ArgumentList []) (Left name) [] CKInstantiate]
        constraintLocal resultVar fieldVar = [CJoin resultVar [fieldVar]]
    constraintsInBindTarget (VariableInfo _ (ArgumentList resultAnnotations) _) (BindTargetTuple arity) args
      = concat $ zipWith fieldConstraint (rights args) resultAnnotations
      where
        fieldConstraint (VarGlobal (GlobalVariable name _)) resultAnnotation = [CCall resultAnnotation (ArgumentList []) (Left name) [] CKInstantiate]
        fieldConstraint (VarLocal (Local name _)) resultAnnotation = zipFlattenArgument (\res field -> CJoin res [field]) resultAnnotation fieldAnnotation
          where
            (VariableInfo _ fieldAnnotation _) = lookupLocal state name
    constraintsInExpression :: VariableInfo -> Expr -> [Constraint]
    constraintsInExpression result (Var var) = call result (Right var) [] CKInstantiate
    constraintsInExpression result (Seq _ var) = call result (Right var) [] CKInstantiate
    constraintsInExpression result (Eval var) = call result (Right var) [] CKInstantiate
    constraintsInExpression result (CastThunk var) = call result (Right var) [] CKInstantiate
    constraintsInExpression result (Instantiate var tps) = call result (Right var) (map Left tps) CKInstantiate
    constraintsInExpression result (Call fn args) = call result (Left fn) args CKCall
    constraintsInExpression result _ = []

    call :: VariableInfo -> Either GlobalFunction Variable -> [Either Type Variable] -> CallKind -> [Constraint]
    call (VariableInfo _ resultAnnotation resultRegion) target args callKind
      = case callTarget of
          Right annotations
            | null args && callKind == CKInstantiate -> zipWith (\a b -> CJoin a [b]) (argumentFlatten resultAnnotation) (argumentFlatten annotations)
          _ -> [CCall resultAnnotation resultRegion callTarget args' callKind]
      where
        callTarget = case target of
          Left (GlobalFunction name _ _) -> Left name
          Right (VarGlobal (GlobalVariable name _)) -> Left name
          Right (VarLocal (Local name _)) ->
            let
              VariableInfo _ annotations _ = lookupLocal state name
            in
              Right annotations
        args' = map argumentAnnotationRegion args
        argumentAnnotationRegion :: Either Type Variable -> CallArgument
        argumentAnnotationRegion (Left tp) = CAType tp
        argumentAnnotationRegion (Right (VarGlobal (GlobalVariable name _))) = CAGlobal name
        argumentAnnotationRegion (Right (VarLocal (Local name _))) = CALocal annotation region
          where
            VariableInfo _ annotation region = lookupLocal state name

constructorConstraints :: [Argument a] -> Argument a -> [Either c (Argument a)] -> (a -> Int) -> (a -> a -> [b]) -> (c -> Argument a -> [b]) -> [b]
constructorConstraints constructor (ArgumentList dataType) fields index f g = concat $ zipWith handleField constructor fields
  where
    handleField arg (Left c) = g c arg
    handleField arg (Right arg') = fieldConstraints arg arg'
    fieldConstraints (ArgumentValue var) field = concat $ zipFlattenArgument f (dataType !! index var) field
    fieldConstraints (ArgumentList as) (ArgumentList bs) = concat $ zipWith fieldConstraints as bs

methodApplyRelationConstraints :: [RelationConstraint] -> MethodState -> MethodState
methodApplyRelationConstraints relationConstraints (MethodState global varMap returnRegion regions _ constraints annotations) =
  MethodState (substitute global) (mapMap substituteVariableInfo varMap) returnRegion regions relation constraints annotations
  where
    (substitution, relation) = relationFromConstraints regions relationConstraints
    substitute :: RegionVar -> RegionVar
    substitute (RegionVar idx) = case IntMap.lookup idx substitution of
      Just idx' -> RegionVar idx'
      Nothing -> error "methodApplyRelationConstraints: region variable not found"
    substituteVariableInfo :: VariableInfo -> VariableInfo
    substituteVariableInfo (VariableInfo )
    
