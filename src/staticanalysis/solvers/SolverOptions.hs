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
getTypeSynonyms options = concat [ s | SolveWithTypeSynonyms s <- options ]

getTypeSignatures :: SolverOptions -> [(String, TpScheme)]
getTypeSignatures options = concat [ xs | SolveWithTypeSignatures xs <- options ]
