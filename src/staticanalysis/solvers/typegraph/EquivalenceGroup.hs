-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- EquivalenceGroup.hs : A datatype for an equivalence group.
--
------------------------------------------------------------------------------

module EquivalenceGroup where

import IsTypeGraph
import List               ( partition, union, nub, sort )
import Utils              ( internalError               )
import Debug.Trace

debugMode = False -- enable/disable tracing

emptyGroup        ::                                                    EquivalenceGroup info
insertVertex      :: VertexID -> VertexInfo -> EquivalenceGroup info -> EquivalenceGroup info 
insertEdge        :: EdgeID -> info ->         EquivalenceGroup info -> EquivalenceGroup info 
combineCliques    :: Cliques ->                EquivalenceGroup info -> EquivalenceGroup info 
combineGroups     :: EquivalenceGroup info ->  EquivalenceGroup info -> EquivalenceGroup info
splitGroup        :: EquivalenceGroup info ->                         [ EquivalenceGroup info ]

removeEdge        :: EdgeID  -> EquivalenceGroup info -> EquivalenceGroup info
removeClique      :: Cliques -> EquivalenceGroup info -> EquivalenceGroup info

vertices          :: EquivalenceGroup info -> [(VertexID,VertexInfo)]
edges             :: EquivalenceGroup info -> [(EdgeID,info)]
cliques           :: EquivalenceGroup info -> [Clique]
constants         :: EquivalenceGroup info -> [String]
representative    :: EquivalenceGroup info -> VertexID

pathsFrom         :: VertexID -> [VertexID] -> EquivalenceGroup info -> Paths info

----------------------------------------------------------------------
-- Representation of an equivalence group

newtype EquivalenceGroup info = 
   EQGroup ( [(VertexID,VertexInfo)]        -- variables
           , [String]                       -- constants
           , [(EdgeID,info)]                -- (initial) edges
           , [(Int,[(VertexID,VertexID)])]  -- (implied) cliques
           )

-- first sort the items of an equivalence group for the Eq instance
instance Show (EquivalenceGroup info) where
   show (EQGroup (vs1,ss1,es1,cs1)) = 
      unlines [ "[Vertices ]: "++show (sort vs1)
              , "[Constants]: "++show (sort ss1)
              , "[Edges    ]: "++show (sort (map fst es1))
              , "[Cliques  ]: "++show (sort (map f cs1))
              ]
         where f (i,xs) = (i,sort xs) 
         
instance Eq (EquivalenceGroup info) where
   a == x = show a == show x         
     

----------------------------------------------------------------------
-- Functions to construct an equivalence group

emptyGroup = EQGroup ([],[],[],[])

insertVertex i info (EQGroup (vs,ss,es,cs)) = (EQGroup ((i,info):vs,ss',es,cs))
   where ss' = case info of 
                  (Just s,_,_) -> [s] `union` ss
                  _            -> ss
   
insertEdge i info (EQGroup (vs,ss,es,cs)) = (EQGroup (vs,ss,(i,info):es,cs))  
 
 {- updated 3 december 2002: improvement in combining cliques -}
combineCliques (i,lists) (EQGroup (vs,ss,es,cs)) = 
   (if debugMode then trace msg else id) (EQGroup (vs,ss,es,new))

      where new = filter ((>1) . length . snd) (newclass : cs1)
            (cs1,cs2) = let p (j,list) = i /= j || all (`notElem` concat lists) list
                        in partition p cs
            newclass  = (i,(nub . concat) (lists++map snd cs2))
            
            msg = unlines ["------------------combine clique -------------------------"
                          ,"status: "++ show (null [ x | (i,list) <- cs, (x,_) <- list, x `notElem` map fst vs ])
                          ,"vertices: "++show (map fst vs)                                    
                          ,"first: "++show cs
                          ,"clique: "++show (i,lists) 
                          ,"result: "++show new
                          ]

combineGroups (EQGroup (vs1,ss1,es1,cs1)) (EQGroup (vs2,ss2,es2,cs2)) = 
   EQGroup (vs1++vs2,ss1 `union` ss2,es1++es2,cs1++cs2)

splitGroup eqc = let (vs,es,cs) = (vertices eqc,edges eqc,cliques eqc)
                     eqcs = map (\(a,b) -> insertVertex a b emptyGroup) vs

                     addClique (cnr,list) cs 
                        | length list < 2 = cs
                        | null cs1        = internalError "EquivalenceGroup.hs" "splitGroup" ("empty list (1) \n"++show eqc)
                        | otherwise       = combineCliques (cnr,[list]) (foldr combineGroups emptyGroup cs1) : cs2
                      
                       where (cs1,cs2) = partition p cs 
                             p c       = any ((`elem` is) . fst) (vertices c)
                             is        = map fst list
 
                     addEdge (EdgeID v1 v2,info) cs 
                        | null cs1  = internalError "EquivalenceGroup.hs" "splitGroup" "empty list (2)"
                        | otherwise = insertEdge (EdgeID v1 v2) info (foldr combineGroups emptyGroup cs1) : cs2
                        
                       where (cs1,cs2) = partition p cs
                             p c       = any ((`elem` [v1,v2]) . fst) (vertices c)

                 in foldr addEdge (foldr addClique eqcs cs) es

----------------------------------------------------------------------
-- Functions to remove parts of an equivalence group

removeEdge edge (EQGroup (vs1,ss1,es1,cs1)) = EQGroup (vs1,ss1,filter ((edge /=) . fst) es1,cs1)

removeClique (i,lists) (EQGroup (vs,ss,es,cs)) = 
   (if debugMode then trace msg else id) (EQGroup (vs,ss,es,new))
   
      where new = zip (repeat i) (filter ((>1) . length) lists) ++ filter p cs
            p (j,list) = (i /= j || any (`notElem` concat lists) list) && length list > 1  
            
            msg = unlines ["------------------remove clique -------------------------"
                          ,"status: "++ show (null [ x | (i,list) <- cs, (x,_) <- list, x `notElem` map fst vs ])
                          ,"vertices: "++show (map fst vs)                  
                          ,"first: "++show cs
                          ,"clique: "++show (i,lists) 
                          ,"result: "++show new
                          ] 
                      
----------------------------------------------------------------------
-- Functions to get the contents of an equivalence group

vertices   (EQGroup (vs1,ss1,es1,cs1)) = vs1
edges      (EQGroup (vs1,ss1,es1,cs1)) = es1
cliques    (EQGroup (vs1,ss1,es1,cs1)) = cs1
constants  (EQGroup (vs1,ss1,es1,cs1)) = ss1

representative (EQGroup (vs1,ss1,es1,cs1)) = case vs1 of
   (vid,_) : _ -> vid
   _           -> internalError "EquivalenceGroup.hs" "representative" "no vertices in group"
   
----------------------------------------------------------------------
-- All paths between two vertices in a group 

pathsFrom v1 vs eqgroup = rec v1 vs (edges eqgroup,cliques eqgroup) where
   
      rec :: Int -> [Int] -> ([(EdgeID,info)],[Clique]) -> Paths info
      rec v1 targets (es,cs) 
        | v1 `elem` targets  = [ [] ]
        | otherwise = let (edges1,es' ) = partition (\(EdgeID a _,_) -> v1 == a) es
                          (edges2,es'') = partition (\(EdgeID _ a,_) -> v1 == a) es'
                          (cliques,cs') = partition (elem v1 . map fst . snd) cs
                          rest = (es'',cs')
                      in [ (EdgeID v1 neighbour,Initial info) : p 
                         | (EdgeID _ neighbour,info) <- edges1
                         , p <- rec neighbour targets rest 
                         ] 
                      ++ [ (EdgeID v1 neighbour,Initial info) : p 
                         | (EdgeID neighbour _,info) <- edges2
                         , p <- rec neighbour targets rest 
                         ]
                      ++ [ (EdgeID v1 neighbour,Implied cnr v1p parent) : p 
                         | (cnr,list) <- cliques
                         , let Just v1p = lookup v1 list
                         , (neighbour,parent) <- list
                         , neighbour /= v1
                         , p <- rec neighbour targets rest 
                         ]
