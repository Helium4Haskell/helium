-- Takes the solved annotations and transforms the method based on these annotations.
-- Adds the resulting annotations, allocates new regions in the method, adds region arguments
-- to the method signature and calls, and marks each allocating bind with a region.
module Helium.CodeGeneration.Iridium.Region.MethodTransform (methodTransform) where

import Data.Maybe
import Data.List
import Data.IntMap (IntMap)
import qualified Data.IntMap as IntMap

import Lvm.Common.Id
import Lvm.Common.IdMap
import Lvm.Core.Type

import Helium.CodeGeneration.Iridium.Data
import Helium.CodeGeneration.Iridium.Region.Sort
import Helium.CodeGeneration.Iridium.Region.Relation
import Helium.CodeGeneration.Iridium.Region.Annotation
import Helium.CodeGeneration.Iridium.Region.AnnotationNormalize
import Helium.CodeGeneration.Iridium.Region.EffectEnvironment
import Helium.CodeGeneration.Iridium.Region.MethodInitialize
import Helium.CodeGeneration.Iridium.Region.MethodSolveConstraints

methodTransform :: Solution -> Declaration Method -> Declaration Method
methodTransform solution (Declaration name visibility mod custom (Method methodType arguments returnType methodAnnotations entryBlock blocks)) =
  Declaration name visibility mod custom (Method methodType arguments returnType methodAnnotations' entryBlock' blocks')
  where
    MethodStateSolution annotations mapping state = findMap name solution

    methodAnnotations' = MethodAnnotateRegion annotations : methodAnnotations
    entryBlock' = entryBlock -- TODO
    blocks' = blocks -- TODO
