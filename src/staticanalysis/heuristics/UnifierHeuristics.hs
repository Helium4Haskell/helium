{-| Module      :  UnifierHeuristics
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable

	A heuristic that tries to blaim two program locations that both contribute 
	to the type error, instead of preferring (or choosing) one location over the
	other. The type error messages will be more "symmetric".
-}

module UnifierHeuristics where

import Top.Types
import Top.States.TIState
import Top.TypeGraph.Basics
import Top.TypeGraph.TypeGraphState
import Top.TypeGraph.Heuristics
import RepairHeuristics
import ConstraintInfo
import Data.List (partition, sortBy)
import Data.Maybe (isNothing, fromJust)

class IsUnifier a where
   typeErrorForUnifier :: (Tp, Tp) -> (a, a) -> a
   isUnifier :: a -> Maybe (Int, (String, LocalInfo, String))

unifierVertex :: (HasTypeGraph m info, WithHints info, IsUnifier info) => Selector m info
unifierVertex =
   Selector ("Unification vertex", f) where

 f (_, _, info) =
    case isUnifier info of
       Nothing -> return Nothing
       Just (unifier, _) -> 
          do neighbours <- edgesFrom unifier
	     let (unifiersUnsorted, contexts) = partition p (map f neighbours)
	         f (EdgeID v1 v2, _, info)
		    | v1 == unifier = (v2, info)
		    | otherwise     = (v1, info)
	         p (_, info) = 
	            case isUnifier info of
		       Nothing    -> False
	               Just (u,_) -> u == unifier
		 -- sort this list by the ordering in which the type variables were assigned
		 -- to prevent undeterministic type error messages.
		 unifiers = sortBy (\x y -> fst x `compare` fst y) unifiersUnsorted
             doWithoutEdges [ (e,i) | (e,_,i) <- neighbours ] $ 
	     
	        do synonyms      <- getTypeSynonyms
		   unifierMTypes <- mapM safeApplySubst (map (TVar . fst) unifiers) 
		   contextMTypes <- mapM safeApplySubst (map (TVar . fst) contexts)
		   if any isNothing (unifierMTypes ++ contextMTypes) then return Nothing else 
		      do let unifierTypes = map fromJust unifierMTypes 
		             contextTypes = map fromJust contextMTypes
		             indices =
			        let p i = unifiableList synonyms (deleteIndex i unifierTypes ++ contextTypes)
				in filter p [0..length unifierTypes - 1]
			 case indices of
			    -- if there are exactly two branches that cause the problem, then report
			    -- these two in a type error
			    [index1, index2] ->
			       let (v1, info1) = unifiers !! index1
			           (v2, info2) = unifiers !! index2
			           edges   = [EdgeID unifier v1, EdgeID unifier v2]
				   newInfo = typeErrorForUnifier (TVar v1, TVar v2) (info1, info2) 
			       in return $ Just 
			             (7, "two inconsistent branches", edges, [newInfo])
			       
			    _ -> return Nothing
