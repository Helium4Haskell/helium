module OneLiner(Tree(..), showOneLine) where

import List

data Tree 
    = Node [Tree]
    | Text String

collapseString = "..."
collapseWidth  = length collapseString

showOneLine :: Int -> Tree -> String
showOneLine width tree = 
    case tree of
        Text s -> s
        Node ts -> oneLine True width ts
        
oneLine toplevel width trees
    | not toplevel &&  -- do not collapse at toplevel
        thisLevel > width -- collapse if not even texts can be displayed
          = collapseString
    | not toplevel &&
        minSize trees > collapseWidth && 
            minSize trees > width -- only collapse if that makes things better
          = collapseString
    | otherwise = concatMap processTree (zip childWidths trees)
    where
        thisLevel = countThisLevel trees
        nrOfChildren = length [ 1 | Node _ <- trees ]
        childSizes = map (\t -> case t of { Text _ -> 0; Node _ -> maxSize [t]} ) trees
        numberedChildren = zip [0..] childSizes
        childWidths = map snd (sort (distribute (width - thisLevel) numberedChildren))
        
        processTree (childWidth, Text s) = s
        processTree (childWidth, Node ts) = oneLine False childWidth ts

maxSize :: [Tree] -> Int
maxSize ts =
    let
        sizeOne :: Tree -> Int
        sizeOne (Text s) = length s
        sizeOne (Node ts) = maxSize ts
    in
        sum (map sizeOne ts)

minSize :: [Tree] -> Int
minSize ts =
    let
        sizeOne :: Tree -> Int
        sizeOne (Text s) = length s
        sizeOne (Node ts) = min (minSize ts) collapseWidth
    in
        sum (map sizeOne ts)

countThisLevel ts = 
    sum [ length s | Text s <- ts ]


distribute :: Int -> [(Int, Int)] -> [(Int, Int)]
distribute width children 
    | null smallChildren = [ (nr, widthPerChild) | (nr, _) <- children ]
    | otherwise =
        smallChildren ++ distribute leftOvers bigChildren
    where
        widthPerChild = width `div` length children
        (smallChildren, bigChildren) =
            partition (\(nr, need) -> need <= widthPerChild) children
        leftOvers = width - sum (map snd smallChildren)
        
