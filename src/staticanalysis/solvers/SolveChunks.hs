module SolveChunks where

import Constraints
import IsTypeGraph
import List              (partition)
import Utils             (internalError)
import SolveCombination
import SolveGreedy
import SolveTypeGraph
import Tree
import Types
import Data.FiniteMap

type ChunkConstraints constraint = (Chunks constraint, Dependencies constraint)
type Chunks           constraint = [Chunk constraint]
type Chunk            constraint = (ChunkID, Tree constraint)
type Dependency       constraint = (ChunkID, ChunkID, FixpointSubstitution -> Predicates -> constraint)
type Dependencies     constraint = [Dependency constraint]
type ChunkID                     = Int

singletonChunk :: [constraint] -> ChunkConstraints constraint
singletonChunk cs = ([(0, listTree cs)], [])

solveChunkConstraints :: ( Show constraint                                     
                         , SolvableConstraint constraint (Greedy info)
                         , SolvableConstraint constraint (TypeGraph info)
                         , IsTypeGraph (TypeGraph info) info        
                         ) => (Tree constraint -> [constraint], OrderedTypeSynonyms, [[(String, TpScheme)]]) -> 
                              Int -> ChunkConstraints constraint -> Result info
solveChunkConstraints (flattening, synonyms, siblings) unique =  
   rec unique . insertDependencies (< 0) (FixpointSubstitution emptyFM) []

   where 
      options = (synonyms, siblings)
      
      rec unique (chunks, dependencies) =
         case chunks of 
            [] -> noResult unique
            (chunkID, constraintTree) : otherChunks -> 
               let constraintList = flattening constraintTree
                   result@(unique', sub, preds, _, _)
                      | null constraintList = noResult unique
                      | otherwise           = solveCombination options unique constraintList
                   nextChunkConstraints     = insertDependencies (==chunkID) sub preds (otherChunks, dependencies)
               in combineResults ("finished solving chunk "++show chunkID++"\nchunks to go = "++show (length (fst nextChunkConstraints))) result (rec unique' nextChunkConstraints)
    
      insertDependencies :: (ChunkID -> Bool) -> FixpointSubstitution -> Predicates -> ChunkConstraints constraint -> ChunkConstraints constraint
      insertDependencies condition substitution predicates (chunks, dependencies) = 
         let (toInsert, otherDependencies) = partition (\(x,_,_) -> condition x) dependencies
             insertOne (_, cid, cfun) = 
                let rec [] = [(cid, unitTree (cfun substitution predicates))]
                    rec (tuple@(cid', cs):rest)
                       | cid == cid' = (cid, [cfun substitution predicates] .>>. cs) : rest
                       | otherwise   = tuple : rec rest
                in rec 
         in (foldr insertOne chunks toInsert, otherDependencies)
      
type Result info = (Int, FixpointSubstitution, Predicates, [info], IO ())

noResult :: Int -> Result info
noResult i = (i, FixpointSubstitution emptyFM, [], [], return ())

combineResults :: String -> Result info -> Result info -> Result info
combineResults extra (_, FixpointSubstitution s1, ps1, er1, io1) (unique, FixpointSubstitution s2, ps2, er2, io2) = 
   ( unique
   , FixpointSubstitution (plusFM_C notDisjoint s1 s2)
   , ps1++ps2
   , er1++er2
   , io1 >> putStrLn extra >> io2
   )
  where notDisjoint _ _ = internalError "SolveChunks.hs" "combineResults" "substitutions from chunks are not disjoint"
