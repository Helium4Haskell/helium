{-| Module      :  TieBreakerHeuristics
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    A tie-breaker heuristic will be used if all other heuristics cannot decide on
	which error to report. 
-}

module TieBreakerHeuristics where

import Top.Types
import Top.States.TIState (getTypeSynonyms)
import Top.TypeGraph.Heuristics

-----------------------------------------------------------------------------

class HasTrustFactor a where
   trustFactor :: a -> Float

trustFactorOfConstraint :: HasTrustFactor info => Heuristic info
trustFactorOfConstraint = 
   Heuristic (
      let f (_, info) = return (trustFactor info)
      in minimalEdgeFilter "Trust factor of edge" f)

-----------------------------------------------------------------------------

class HasDirection a where
   isTopDown :: a -> Bool

-- note: because True > False, we use the minimal edge filter to keep
--       all the top down edges
isTopDownEdge :: HasDirection info => Heuristic info
isTopDownEdge = 
   Heuristic (
      let f (_, info) = return (isTopDown info)
      in minimalEdgeFilter "Is a top down edge" f)

-----------------------------------------------------------------------------

-- no "unification-around-a-corner-type-error"
typeVariableInvolved :: HasTwoTypes info => Heuristic info
typeVariableInvolved = 
   let f pair@(edgeID, info) = 
          doWithoutEdge pair $
	     do typeTuple <- getSubstitutedTypes info
	        synonyms  <- getTypeSynonyms
	        case typeTuple of
		   (Just t1, Just t2) ->
		      let i = nextFTV (t1, t2)
		          (i1, t1') = changeTypeVariables i  t1
			  (_ , t2') = changeTypeVariables i1 t2
		      in return (not (unifiable synonyms t1' t2'))
		   _ -> return True
   in Heuristic (edgeFilter "type variable involved" f)
   
changeTypeVariables :: Int -> Tp -> (Int, Tp)
changeTypeVariables i tp = 
   case tp of
      TVar _   -> (i+1, TVar i)
      TCon s   -> (i, TCon s)
      TApp l r -> let (i1, l') = changeTypeVariables i  l
                      (i2, r') = changeTypeVariables i1 r
		  in (i2, TApp l' r')
