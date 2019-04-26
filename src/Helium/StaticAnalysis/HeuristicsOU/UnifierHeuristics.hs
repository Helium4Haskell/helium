{-# LANGUAGE FlexibleContexts #-}

{-| Module      :  UnifierHeuristics
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

	A heuristic that tries to blaim two program locations that both contribute 
	to the type error, instead of preferring (or choosing) one location over the
	other. The type error messages will be more "symmetric".
-}

module Helium.StaticAnalysis.HeuristicsOU.UnifierHeuristics where
