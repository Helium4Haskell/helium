module FilterHeuristics (filterHeuristics) where

import IsTypeGraph
import SolveState
import TypeGraphConstraintInfo
import Heuristics
import Types

type FilterHeuristics m info = [FilterHeuristic m info]
type FilterHeuristic  m info = EdgeID -> info -> m (Maybe String)

filterHeuristics :: (IsTypeGraph m info, MonadState (SolveState m info a) m) => FilterHeuristics m info
filterHeuristics = 
   [ edgeIsPartOfCycle
   , onlyApplicationResult   
   , onlyNegationResult
   ]

edgeIsPartOfCycle :: IsTypeGraph m info => FilterHeuristic m info
edgeIsPartOfCycle edge@(EdgeID v1 v2) info = 
   doWithoutEdge (edge, info) $ 
      do paths <- allPaths v1 v2
         if null paths 
           then return Nothing
           else return (Just "part of a cycle")

onlyApplicationResult :: (IsTypeGraph m info, MonadState (SolveState m info a) m) => FilterHeuristic m info
onlyApplicationResult edge@(EdgeID v1 v2) info =
   case maybeApplicationEdge info of
      Nothing                            -> return Nothing
      Just (_, args) ->
       doWithoutEdge (edge,info) $

          do synonyms <- getTypeSynonyms                 
             (maybeFunctionType, maybeExpectedType) <- getSubstitutedTypes info  
             case (maybeFunctionType,maybeExpectedType) of    
                (Just functionType,Just expectedType) | onlyResult ->
                   return (Just "only result type of application is incorrect")
                   
                  where 
                    nrArgs     = length args
                    onlyResult = length xs == nrArgs &&
                                 length ys == nrArgs &&           
                                 unifiable synonyms (tupleType xs) (tupleType ys)                    
                    xs         = fst (functionSpineOfLength nrArgs functionType)
                    ys         = fst (functionSpineOfLength nrArgs expectedType)  
                _ -> return Nothing

onlyNegationResult :: (IsTypeGraph m info, MonadState (SolveState m info a) m) => FilterHeuristic m info
onlyNegationResult edge@(EdgeID v1 v2) info = 
   case maybeNegation info of
      Nothing            -> return Nothing
      Just isIntNegation -> doWithoutEdge (edge,info) $  
            do synonyms <- getTypeSynonyms
               (_, mtp) <- getSubstitutedTypes info
               case mtp of 
                  Nothing -> return Nothing
                  Just tp -> 
                     let newtvar = TVar (nextFTV tp)
                         testtp = (if isIntNegation then intType else floatType) .->. newtvar
                     in if unifiable synonyms tp testtp
                          then return (Just "only result type of negation is incorrect")
                          else return Nothing
