-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- EnvironmentSynonyms.hs : Type synonyms that are used by the type inferencer.
--
-------------------------------------------------------------------------------

module EnvironmentSynonyms where

import TypeRepresentation
import UHA_Syntax
import SortedAssocList

type TypeEnvironment            = AssocList Name TpScheme
type ConstructorEnvironment     = AssocList Name TpScheme
type TypeConstructorEnvironment = AssocList Name Int
type TypeSynonymEnvironment     = [(Name, Int, Tps -> Tp)]
type Assumptions        = AssocList Name Tp
type PatternAssumptions = AssocList Name Tp
