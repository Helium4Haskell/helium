module Tree where

import FiniteMap
import TreeWalk 

type Trees a = [Tree a]
data Tree  a = Node (Trees a)
             | AddList Direction [a] (Tree a)
             | StrictOrder (Tree a) (Tree a)
             | Spread (a -> Maybe Int) Direction [a] (Tree a)
             | Receive Int
             | Phase Int [a]                      
             | Maf [a] (Tree a)
                                                                    
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
           
           Maf as tree -> 
              let (result, up, phased) = rec down spreaded tree 
              in ((as++) . result, up, phased)
              

     strictRec :: Spreaded a ->         -- the spreaded constraints
                  Tree a ->             -- the tree to flatten
                  List a                -- the result
     strictRec spreaded tree = 
        let (result, up, phased) = rec id spreaded tree
            list      = treewalk id [(result, up)]
            allPhased = plusFM_C (.) (unitFM 5 list) phased
        in concatList (eltsFM allPhased)
