module Tree where

import FiniteMap
import TreeWalk 

type Trees a = [Tree a]
data Tree  a = Node (Trees a)
             | Chunk (a -> Maybe Int) Int (Tree a) [(Int, a)] [(Int,a)] (Tree a)
             | AddList Direction [a] (Tree a)
             | StrictOrder (Tree a) (Tree a)
             | Spread (a -> Maybe Int) Direction [a] (Tree a)
             | Receive Int
             | Phase Int [a]                      
                                                                    
emptyTree ::        Tree a
unitTree  :: a ->   Tree a 
listTree  :: [a] -> Tree a

emptyTree   = Node [] 
unitTree c  = listTree [c]
listTree cs = AddList Down cs emptyTree

------------------------------------------------------------------------

type Flattening = ( Bool      -- spreading yes or no 
                  , TreeWalk  -- treewalk
                  )

flattenW, flattenM, flattenBU, flattenRev :: Flattening
flattenW   = (True, inorderTopLastPostTreeWalk)
flattenM   = (True, inorderTopFirstPreTreeWalk)
flattenBU  = (False, bottomUpTreeWalk)
flattenRev = (True, reverseTreeWalk inorderTopLastPostTreeWalk)
                  
data Direction   = Up | Down
type Spreaded a  = FiniteMap Int [a]
type Phased a    = FiniteMap Int (List a)

flatten :: Flattening -> Tree a -> [a]
flatten (spreading, TreeWalk treewalk) tree = 
   strictRec emptyFM tree []
    
    where    
     rec :: List a ->             -- downward constraints
            Spreaded a ->         -- the spreaded constraints
            Tree a ->             -- the tree to flatten
            ( List a              -- the result
            , List a              -- upward constraints
            , Phased a            -- the phased constraints
            )
     rec down spreaded tree = 
        case tree of
        
           Node trees ->
              let (tuples, phasedList) = 
                     unzip [ ((result, up), phased) 
                           | tree <- trees
                           , let (result, up, phased) = rec id spreaded tree
                           ]
                  phased = foldr (plusFM_C (.)) emptyFM phasedList
              in (treewalk down tuples, id, phased)
           
           Chunk fun cnr left as bs right -> 
              let (.>.) = AddList Down
              in rec down spreaded (map snd as .>. (StrictOrder (map snd bs .>. left) right))
                 
           AddList Up as tree ->
              let (result, up, phased) = rec down spreaded tree
              in (result, (as++) . up, phased)

           AddList Down as tree ->
              rec ((as++) . down) spreaded tree
              
           StrictOrder left right ->
              let left_result  = strictRec spreaded left
                  right_result = strictRec spreaded right
              in (treewalk down [(left_result . right_result, id)], id, emptyFM) 
              
           Spread fun direction as tree -> 
              let (xs, ys) | spreading = foldr op ([], []) as 
                           | otherwise = ([], as)
                  op a (xs, ys) = case fun a of
                                     Just i  -> ((i,[a]):xs, ys)
                                     Nothing -> (xs, a:ys)
              in rec down  (addListToFM_C (++) spreaded xs) (AddList direction ys tree)
              
           Receive i -> 
              let as     = lookupWithDefaultFM spreaded [] i 
                  result | spreading = (as++) . down
                         | otherwise = down
              in (result, id, emptyFM)
              
           Phase i as ->
              (down, id, unitFM i (as++))                        

     strictRec :: Spreaded a ->         -- the spreaded constraints
                  Tree a ->             -- the tree to flatten
                  List a                -- the result
     strictRec spreaded tree = 
        let (result, up, phased) = rec id spreaded tree
            list      = treewalk id [(result, up)]
            allPhased = plusFM_C (.) (unitFM 5 list) phased
        in concatList (eltsFM allPhased)

chunkTree :: Tree a -> ([(Int, Tree a)], [(Int, Int, [a])])
chunkTree tree = 
   let (ts, chunks, deps) = rec tree 
   in (((-1), ts) : chunks, deps) 
  
  where   
   rec tree =
     case tree of
   
        Node trees -> 
           let (ts, chunks, ds) = unzip3 (map rec trees)
           in (Node ts, concat chunks, concat ds)
             
        Chunk fun cnr left as bs right -> 
           let (ts1, chunks1, ds1) = rec left
               (ts2, chunks2, ds2) = rec (map snd bs .>. right)
               (.>.)              = AddList Down
           in (ts2, (cnr, ts1) : chunks1 ++ chunks2, [ (cnr, i, [a]) | (i,a) <- as ] ++ ds1 ++ ds2)
  
        AddList direction as tree ->
           let (ts, chunks, ds) = rec tree
           in (AddList direction as ts, chunks, ds)

        StrictOrder left right -> 
           let (ts1, chunks1, ds1) = rec left
               (ts2, chunks2, ds2) = rec right
           in (StrictOrder ts1 ts2, chunks1 ++ chunks2, ds1 ++ ds2)

        Spread fun direction as tree ->
           let (ts, chunks, ds) = rec tree
           in (Spread fun direction as ts, chunks, ds)

        _ -> (tree, [], [])
        
chunkAndFlattenTree :: Flattening -> Tree a -> ([(Int, [a])], [(Int, Int, [a])])
chunkAndFlattenTree flattening tree =        
   let (chunks, dependencies) = chunkTree tree
   in ( [ (i, list) | (i, tree) <- chunks, let list = flatten flattening tree, not (null list) ]
      , filter (\(_, _, list) -> not (null list)) dependencies
      )
