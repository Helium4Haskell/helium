{-# LANGUAGE FlexibleContexts #-}

{-| Module      :  OnlyResultHeuristics
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

	Two (filter) heuristics that prevent an application or a negation to be 
	reported as incorrect if only the result type is reponsible for non-unifiability.
-}

module Helium.StaticAnalysis.HeuristicsOU.OnlyResultHeuristics where

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes
import Helium.StaticAnalysis.Miscellaneous.UHA_Source
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU

import Data.Maybe

      
-----------------------------------------------------------------------------

class MaybeApplication a where
   maybeNumberOfArguments :: a -> Maybe Int
   maybeApplicationEdge   :: a -> Maybe (Bool, [(UHA_Source, MonoType)])

instance MaybeApplication ConstraintInfo where
   maybeNumberOfArguments = 
      fmap (length . snd) . maybeApplicationEdge
      
   maybeApplicationEdge cinfo = 
      let list = [ (b, zip (map self infoTrees) (map (var . fromJust) tps))
                  | ApplicationEdge b infoTrees <- properties cinfo
                  , let tps = map assignedType infoTrees
                  , all isJust tps
                  ]
      in case list of 
            []      -> Nothing
            tuple:_ -> Just tuple

class IsPattern a where
   isPattern :: a -> Bool
   
-----------------------------------------------------------------------------

class MaybeNegation a where
   maybeNegation :: a -> Maybe Bool

-----------------------------------------------------------------------------
