module Helium.CodeGeneration.Core.Strictness.Data where

import qualified Data.Set as S

import Lvm.Common.IdMap
import Lvm.Core.Type

-- Keys are annotation variables, values are the equality/join/meet
type AnnotationEnvironment = IdMap SAnn

-- Constraint set, l < r
type Constraints = S.Set Constraint
data Constraint = Constraint SAnn SAnn deriving (Eq, Ord, Show)
type SolvedConstraints = IdMap SAnn

-- Join and meet
join, meet :: SAnn -> SAnn -> SAnn
join L _ = L
join _ L = L
join S x = x
join x S = x
join l r | l == r    = l
         | otherwise = Join l r

meet S _ = S
meet _ S = S
meet L x = x
meet x L = x
meet l r | l == r    = l
         | otherwise = Meet l r

joinAll, meetAll :: Ann -> Ann -> Ann
joinAll (a1, r, a2) (a1', r', a2') = (join a1 a1', join r r', join a2 a2')
meetAll (a1, r, a2) (a1', r', a2') = (meet a1 a1', meet r r', meet a2 a2')

isAnn :: SAnn -> Bool
isAnn (AnnVar _) = True
isAnn _          = False

fromAnn :: SAnn -> Id
fromAnn (AnnVar x) = x
fromAnn _          = error "fromAnn"

annEnvToConstraints :: AnnotationEnvironment -> Constraints
annEnvToConstraints = S.fromList . map snd . listFromMap . mapMapWithId (\x y -> Constraint y (AnnVar x))

-- Get all variables in a join or meet
getVariables :: SAnn -> [Id]
getVariables (AnnVar x) = [x]
getVariables (Join x y) = getVariables x ++ getVariables y
getVariables (Meet x y) = getVariables x ++ getVariables y
getVariables _          = []
