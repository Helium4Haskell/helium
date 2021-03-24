-- Removes dead (unused) regions
-- Those regions may occur in the program after region inference,
-- when the region variables were assigned for local variables,
-- which were defined with non-allocating expressions.

module Helium.CodeGeneration.Iridium.Region.DeadRegion (transformDead) where

import Data.List
import Data.IntSet (IntSet)
import qualified Data.IntSet as IntSet

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Region.RegionVar
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.Evaluate

import Debug.Trace

transformDead :: Annotation -> Method -> (Int, Method, Annotation)
transformDead annotation (Method tp additionalRegions arguments returnType returnRegions annotations entry blocks)
  = ( regionVarsSize additionalRegions'
    , Method tp additionalRegions' arguments returnType returnRegions (MethodAnnotateRegion annotation' : annotations) entry' blocks'
    , annotation'
    )
  where
    used = foldl' (flip analyseBlock) IntSet.empty (entry : blocks)

    entry' = transformBlock used entry
    blocks' = transformBlock used <$> blocks

    annotation' = snd $ annotationRestrict (map preserve $ flattenRegionVars additionalRegions) annotation

    additionalRegions' = RegionVarsTuple [RegionVarsSingle r | r <- flattenRegionVars additionalRegions, preserve r]

    preserve (RegionLocal idx) = idx `IntSet.member` used
    preserve _ = False

analyseBlock :: Block -> IntSet -> IntSet
analyseBlock (Block _ instr) = analyseInstruction instr

analyseInstruction :: Instruction -> IntSet -> IntSet
analyseInstruction instruction accum = case instruction of
  Let _ (Call _ additional _ return) next -> analyseInstruction next $! add additional $ add return accum
  Let _ _ next -> go next
  LetAlloc binds next ->
    let
      accum' = foldl' (flip analyseBind) accum binds
    in
      analyseInstruction next $! accum'
  NewRegion _ _ next -> go next
  ReleaseRegion _ next -> go next
  Jump _ -> accum
  Match _ _ _ _ next -> go next
  Case _ _ -> accum
  Return _ -> accum
  Unreachable _ -> accum
  where
    go next = analyseInstruction next accum

analyseBind :: Bind -> IntSet -> IntSet
analyseBind (Bind _ target _ at) = case target of
  BindTargetFunction _ vars1 (BindThunkRegions vars2 vars3) -> add vars1 . add vars2 . add vars3 . add (RegionVarsSingle at)
  BindTargetThunk _ (BindThunkRegions vars1 vars2) -> add vars1 . add vars2 . add (RegionVarsSingle at)
  _ -> add (RegionVarsSingle at)

add :: RegionVars -> IntSet -> IntSet
add (RegionVarsTuple vars) accum = foldl' (flip add) accum vars
add (RegionVarsSingle (RegionLocal idx)) accum = IntSet.insert idx accum
add _ accum = accum

transformBlock :: IntSet -> Block -> Block
transformBlock used (Block name instr) = Block name $ transformInstruction used instr

transformInstruction :: IntSet -> Instruction -> Instruction
transformInstruction used instruction = case instruction of
  Let lhs expr next -> Let lhs expr $ go next
  LetAlloc binds next -> LetAlloc binds $ go next
  NewRegion r s next
    | RegionLocal idx <- r
    , idx `IntSet.member` used -> NewRegion r s $ go next
    | otherwise -> go next
  ReleaseRegion r next
    | RegionLocal idx <- r
    , idx `IntSet.member` used -> ReleaseRegion r $ go next
    | otherwise -> go next
  Match var target inst args next -> Match var target inst args $ go next
  _ -> instruction
  where
    go = transformInstruction used
