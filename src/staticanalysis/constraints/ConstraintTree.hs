module ConstraintTree where

import LiftedConstraints
import TypeConstraints
import Types
import Tree

---------------------------------------------
-- extension for constraint trees

type ConstraintTrees a = Trees (TypeConstraint a)
type ConstraintTree  a = Tree  (TypeConstraint a)

infixr 8 .>. , .>>. , .<. , .<<.

(.>.), (.<.) :: TypeConstraints a -> ConstraintTree a -> ConstraintTree a
(.>.)  = AddList Down
(.<.)  = AddList Up

(.>>.), (.<<.) :: TypeConstraints info -> ConstraintTree info -> ConstraintTree info
(.>>.) = Spread variableInConstraint Down
(.<<.) = Spread variableInConstraint Up
