{-| Module      :  ContributingSites
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    Based on the pair of types that is stored with each constraint info, two areas are
	computed that contain all the sites that contribute to the types as they are in the
	type graph. 
-}

module ContributingSites (contributingSites) where

import Top.Types
import Top.TypeGraph.TypeGraphState
import Top.TypeGraph.Basics
import Top.TypeGraph.Paths
import UHA_Source
import ConstraintInfo
import HighLightArea
import DoublyLinkedTree
import Data.List

--
import Top.States.BasicState 

contributingSites :: HasTypeGraph m ConstraintInfo => ConstraintInfo -> m ConstraintInfo
contributingSites info =
   do areaTuple <- areasFromError info
      return (addProperty (HighlightAreas areaTuple) info)

areasFromError :: HasTypeGraph m ConstraintInfo => ConstraintInfo -> m (Area, Area)
areasFromError info =
   do let (t1, t2) = originalTypePair info
      printMessage ("Area from pair " ++ show (t1, t2))
      area1 <- areaFromType t1
      area2 <- areaFromType t2
      return (area1, area2)
      
areaFromType :: HasTypeGraph m ConstraintInfo => Tp -> m Area
areaFromType tp = 
   do printMessage ("Area from type " ++ show tp)
      areas <- mapM areaFromTypeVariable (ftv tp)
      return (plus areas) where

areaFromTypeVariable :: HasTypeGraph m ConstraintInfo => Int -> m Area
areaFromTypeVariable i = 
   do printMessage ("Area from type variable " ++ show i)
      vertices <- verticesInGroupOf i
      let constants    = [ (i, []    ) | (i, (VCon _  , _)) <- vertices ] 
          applications = [ (i, [l, r]) | (i, (VApp l r, _)) <- vertices ]
          (targets, childrenList) = unzip (constants ++ applications)
      paths  <- allPathsList i targets
      let edges = map snd (nubBy (\x y -> fst x == fst y) (steps paths))
      areas1 <- mapM areaFromEdge edges
      areas2 <- mapM areaFromTypeVariable (concat childrenList)
      return (plus (areas1 ++ areas2))
        
areaFromEdge :: HasTypeGraph m ConstraintInfo => PathStep ConstraintInfo -> m Area
areaFromEdge edgeInfo =
   case edgeInfo of
      Initial _ info -> 
         do printMessage "Initial edge ***********************"
	    return (areaFromInfo info)
      Implied _ v1 v2 -> 
         do printMessage "Implied edge **************************"
	    paths <- allPaths v1 v2
            let edges = map snd (nubBy (\x y -> fst x == fst y) (steps paths))
            areas <- mapM areaFromEdge edges
            return (plus areas)
      Child _ -> 
         return empty

areaFromInfo :: ConstraintInfo -> Area
areaFromInfo info =
   let infoTree      = localInfo info
       myArea        = rangeToArea (rangeOfSource (self (attribute infoTree)))
       childrenAreas = map (rangeToArea . rangeOfSource . self . attribute) (children infoTree) 
   in myArea .-. plus childrenAreas
