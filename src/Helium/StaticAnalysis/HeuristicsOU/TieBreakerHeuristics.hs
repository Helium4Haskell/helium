{-# LANGUAGE FlexibleContexts #-}

{-| Module      :  TieBreakerHeuristics
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    A tie-breaker heuristic will be used if all other heuristics cannot decide on
    which error to report. 
-}

module Helium.StaticAnalysis.HeuristicsOU.TieBreakerHeuristics where

-----------------------------------------------------------------------------

class HasTrustFactor a where
   trustFactor :: a -> Float

-----------------------------------------------------------------------------

class HasDirection a where
   isTopDown :: a -> Bool

   
