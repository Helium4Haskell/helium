-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- SolverOptions.hs : Options for solving the type constraints.
--
-------------------------------------------------------------------------------

module SolverOptions where

import Types

type SolverOptions = [SolverOption]
data SolverOption  = SolveWithTypeSynonyms      OrderedTypeSynonyms
                   | SolveWithTypeSignatures    [(String, TpScheme)]

getTypeSynonyms :: SolverOptions -> OrderedTypeSynonyms
getTypeSynonyms options = 
   case [ s | SolveWithTypeSynonyms s <- options ] of
      x:_ -> x
      _   -> noOrderedTypeSynonyms

getTypeSignatures :: SolverOptions -> [(String, TpScheme)]
getTypeSignatures options = concat [ xs | SolveWithTypeSignatures xs <- options ]
