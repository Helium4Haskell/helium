module Tree where

import Data.FiniteMap
import qualified Set
import TreeWalk 
import Types
import List (partition)

type Trees a = [Tree a]
data Tree  a = Node (Trees a)             
             | AddList Direction [a] (Tree a)
             | StrictOrder (Tree a) (Tree a)
             | Spread Direction [a] (Tree a)
             | Receive Int
             | Phase Int [a]         
             | Chunk Int (Tree a) [(Int, a)] [(Int, a)] (Tree a)
   deriving Show             
                                                                    
emptyTree ::                     Tree a
unitTree  :: a ->                Tree a 
listTree  :: [a] ->              Tree a
binTree   :: Tree a -> Tree a -> Tree a

emptyTree   = Node [] 
unitTree c  = listTree [c]
listTree cs = cs .>. emptyTree
binTree a b = Node [a, b]

infixr 8 .>. , .>>. , .<. , .<<.

(.>.), (.>>.), (.<.), (.<<.) :: [a] -> Tree a -> Tree a
((.>.), (.>>.), (.<.), (.<<.)) = 
   let -- prevents adding an empty list
       f constructor direction as tree
          | null as   = tree 
          | otherwise = constructor direction as tree
   in (f AddList Down, f Spread Down, f AddList Up, f Spread Up)


------------------------------------------------------------------------

data Direction   = Up | Down deriving (Eq, Show)
type Spreaded a  = FiniteMap Int [a]
type Phased a    = FiniteMap Int (List a)

flattenTree :: TreeWalk -> Tree a -> [a]
flattenTree (TreeWalk treewalk) tree = 
   strictRec tree []
    
    where    
     rec :: List a ->             -- downward constraints
            Tree a ->             -- the tree to flatten
            ( List a              -- the result
            , List a              -- upward constraints
            )
     rec down tree = 
        case tree of
        
           Node trees ->
              let tuples = map (rec id) trees
              in (treewalk down tuples, id)
           
           Chunk cnr left as bs right -> 
              rec down (StrictOrder (map snd bs .>>. left) (map snd as .>>. right))
                 
           AddList Up as tree ->
              let (result, up) = rec down tree
              in (result, (as++) . up)

           AddList Down as tree ->
              rec ((as++) . down) tree
              
           StrictOrder left right ->
              let left_result  = strictRec left
                  right_result = strictRec right
              in (treewalk down [(left_result . right_result, id)], id) 
              
           Spread direction as tree -> 
              rec down (AddList direction as tree)
              
           Receive i -> 
              rec down emptyTree
              
           Phase i as ->
              rec down (listTree as)                  

     strictRec :: Tree a ->             -- the tree to flatten
                  List a                -- the result
     strictRec tree = 
        let (result, up) = rec id tree
        in treewalk id [(result, up)]

spreadTree :: (a -> Maybe Int) -> Tree a -> Tree a
spreadTree spreadFunction = fst . rec emptyFM
   where
    rec fm tree = 
       case tree of   

          Node trees -> 
             let (trees', sets) = unzip (map (rec fm) trees)
             in (Node trees', Set.unions sets)
          
          -- also spread the constraints that are stored as
          -- a dependency in this chunk.
          Chunk cnr left as bs right -> 
             rec fm (StrictOrder (map snd bs .>>. left) (map snd as .>>. right))
          
          AddList direction as tree -> 
             let (tree', set) = rec fm tree
             in (AddList direction as tree', set)

          StrictOrder left right -> 
             let (left' , set1) = rec fm left
                 (right', set2) = rec fm right
             in (StrictOrder left' right', Set.union set1 set2)
          
          Spread direction as tree -> 
             let (tree', set) = rec fmNew tree
                 fmNew = addListToFM_C (++) fm [ (i, [x]) | x <- doSpread, let Just i = spreadFunction x ]
                 (doSpread, noSpread) = 
                    partition (maybe False (`Set.member` set) . spreadFunction) as
             in (Spread direction noSpread tree', set)
          
          Receive i -> 
             let tree = case lookupFM fm i of
                           Nothing -> emptyTree
                           Just as -> listTree as
             in (tree, Set.single i)
             
          Phase i as ->
             (tree, Set.empty)
             
          _ -> (tree, Set.empty)


phaseTree :: Tree a -> Tree a
phaseTree = strictRec
   
   where
    rec tree = 
       case tree of
          Node trees -> 
             let (trees', phasesList) = unzip (map rec trees)
                 phases = foldr (plusFM_C (.)) emptyFM phasesList
             in (Node trees', phases)
          Chunk cnr left as bs right ->
             let (left' , phases1) = rec left
                 (right', phases2) = rec right
             in (Chunk cnr left' as bs right', plusFM_C (.) phases1 phases2)
          AddList dir as tree ->
             let (tree', phases) = rec tree
             in (AddList dir as tree', phases)
          StrictOrder left right -> 
             let left'  = strictRec left
                 right' = strictRec right
             in (StrictOrder left' right', emptyFM)             
          Spread dir as tree -> 
             let (tree', phases) = rec tree
             in (Spread dir as tree', phases)
          Receive _  -> (tree, emptyFM)
          Phase i as -> (emptyTree, unitFM i (as++))
          
    strictRec tree = 
       let (tree', phases) = rec tree
           f i list = listTree (list [])
       in foldr1 StrictOrder (eltsFM (addToFM_C binTree (mapFM f phases) 5 tree'))
        
          
chunkTree :: Substitution substitution => 
             (a -> substitution -> Predicates -> a) -> Tree a -> 
             ([(Int, Tree a)], [(Int, Int, substitution -> Predicates -> a)])
chunkTree afun tree = 
   let (ts, chunks, deps) = rec tree 
   in ( ((-1), ts) : chunks, deps)
  
  where   
   rec tree =
     case tree of
   
        Node trees -> 
           let (ts, chunks, ds) = unzip3 (map rec trees)
           in (Node ts, concat chunks, concat ds)
             
        Chunk cnr left as bs right -> 
           let (ts1, chunks1, ds1) = rec left
               (ts2, chunks2, ds2) = rec right
               dependencies        = [ ((-1), i, afun x) | (i,x) <- bs ] ++
                                     [ (cnr , i, afun x) | (i,x) <- as ]                                     
           in (ts2, chunks1 ++ [(cnr, ts1)] ++ chunks2, dependencies ++ ds1 ++ ds2)
  
        AddList direction as tree ->
           let (ts, chunks, ds) = rec tree
           in (AddList direction as ts, chunks, ds)

        StrictOrder left right -> 
           let (ts1, chunks1, ds1) = rec left
               (ts2, chunks2, ds2) = rec right
           in (StrictOrder ts1 ts2, chunks1 ++ chunks2, ds1 ++ ds2)

        Spread direction as tree ->
           let (ts, chunks, ds) = rec tree
           in (Spread direction as ts, chunks, ds)

        _ -> (tree, [], [])
