-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- Strategy.hs : Define how to flatten a constraint tree. 
--
-------------------------------------------------------------------------------

module Strategy where

type Strategy    = ( TreeWalk   -- volgorde van constraints verzamelen
                   , Bool       -- constraints mappen op variabelen?
                   , Bool       -- explicit type definitions first?
                   )
newtype TreeWalk = TreeWalk (forall a . ListCont a -> [(ListCont a,ListCont a)] -> ListCont a)

type ListCont a = [a] -> [a]

concatListCont :: [ListCont a] -> ListCont a
concatListCont = foldr (.) id

topDownTreeWalk :: TreeWalk
topDownTreeWalk = TreeWalk (\top cs -> top . children (unzip cs))
   where children (fs,gs) = concatListCont gs . concatListCont fs

bottomUpTreeWalk :: TreeWalk
bottomUpTreeWalk = TreeWalk (\top cs -> children (unzip cs) . top)
   where children (gs,fs) = concatListCont gs . concatListCont fs

inorderTopFirstPreTreeWalk :: TreeWalk
inorderTopFirstPreTreeWalk = TreeWalk (\top cs -> top . children cs)
   where children = concatListCont . map (\(f,g) -> g . f)

inorderTopLastPreTreeWalk :: TreeWalk
inorderTopLastPreTreeWalk = TreeWalk (\top cs -> children cs . top)
   where children = concatListCont . map (\(f,g) -> g . f)

inorderTopFirstPostTreeWalk :: TreeWalk
inorderTopFirstPostTreeWalk = TreeWalk (\top cs -> top . children cs)
   where children = concatListCont . map (\(f,g) -> f . g)

inorderTopLastPostTreeWalk :: TreeWalk
inorderTopLastPostTreeWalk = TreeWalk (\top cs -> children cs . top)
   where children = concatListCont . map (\(f,g) -> f . g)

reverseTreeWalk :: TreeWalk -> TreeWalk
reverseTreeWalk (TreeWalk f) = TreeWalk (\top cs -> f top (reverse cs))

algW           = (inorderTopLastPostTreeWalk,True,True)
algM           = (inorderTopFirstPreTreeWalk,True,True)
algBU          = (bottomUpTreeWalk,False,True)
algRev         = (reverseTreeWalk inorderTopLastPostTreeWalk,True,True)

allStrategies :: [Strategy]
allStrategies = [ (reversed treewalk,mapOnVar,explicitsFirst)
                | treewalk <- [ topDownTreeWalk, bottomUpTreeWalk
                              , inorderTopFirstPreTreeWalk, inorderTopLastPreTreeWalk
                              , inorderTopFirstPostTreeWalk, inorderTopLastPostTreeWalk
                              ]
                , mapOnVar       <- [True,False]
                , explicitsFirst <- [True,False]
                , reversed <- [id,reverseTreeWalk]
                ]
