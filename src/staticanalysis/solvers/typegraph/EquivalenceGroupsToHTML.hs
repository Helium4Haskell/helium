-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- EquivalenceGroupsToHTML.hs : write each equivalence group to a HTML 
--    document, and make links to other groups.
--
------------------------------------------------------------------------------

module EquivalenceGroupsToHTML ( equivalenceGroupsToHTML, equivalenceGroupsToHTML_And_Stop ) where

import Types
import SolveState
import SolveTypeGraph
import EquivalenceGroup
import SolveEquivalenceGroups
import Monad
import ConstraintInfo
import TypeGraphConstraintInfo
import SolveConstraints

equivalenceGroupsToHTML_And_Stop :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => SolveState EquivalenceGroups info ()
equivalenceGroupsToHTML_And_Stop = do equivalenceGroupsToHTML
                                      io <- getDebug
                                      error (show (unsafePerformIO io))

equivalenceGroupsToHTML :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => SolveState EquivalenceGroups info ()
equivalenceGroupsToHTML = do unique <- getUnique
                             let op is i = do xs <- getVerticesInGroup i
                                              let i' = fst (head xs)
                                              if i' `elem` is 
                                                then return is
                                                else do showOneGroup i'
                                                        return (i':is)
                             allGroups <- foldM op [] [0..unique-1]
                             return ()

showOneGroup :: (TypeGraph EquivalenceGroups info,TypeGraphConstraintInfo info) => Int -> SolveState EquivalenceGroups info ()
showOneGroup i = 
   do -- stp <- findSubstForVar i
      msg <- useSolver (\groups -> 
      
       do eqc <- equivalenceGroupOf i groups
   
          let showTV i = do eqcI <- equivalenceGroupOf i groups
                            let j = fst (head (vertices eqcI))                                      
                            return ("<a href="++show ("group"++show j++".html")++">v"++show i++"</a>")
              showTV' i = return ("v"++show i)
          
          let unlines' = concatMap (++"<br>\n")

{-          -- type
          subs <- let f i = do s <- showTV i  
                               return (singleSubstitution i (TCon s))
                  in mapM f (ftv stp)         
          let sub = foldr (@@@) emptySubst subs
                                
          let msgType = "<h3>Type</h3>\n" ++ show (sub |-> stp)
-}          
          -- vertices
          let f (vid,(ms,ch,mts)) = do a <- showTV' vid
                                       b <- case ms of 
                                               Just s  -> do ch' <- mapM showTV ch                                                             
                                                             let tp = foldl TApp (TCon s) (map TCon ch')
                                                             return (" = "++show tp)
                                               Nothing -> return ""
                                       c <- case mts of 
                                               Just (s,cs) -> do cs' <- mapM showTV cs
                                                                 let tp = foldl TApp (TCon s) (map TCon cs')
                                                                 return (" which is <b>"++show tp++"</b>")
                                               Nothing     -> return""
                                       return (a++b++c)  
          list <- mapM f (vertices eqc)          
          let msgVertices = "<h3>Vertices</h3>\n" ++ unlines' list
          
          -- edges
          let f (EdgeID v1 v2,info) = do a <- showTV' v1 
                                         b <- showTV' v2
                                         return (a++" - "++b++" ["++show (getInfoSource info)++"]")
          list <- mapM f (edges eqc)
          let msgEdges = "<h3>Edges</h3>\n" ++ unlines' list
                                                                   
          -- cliques   
          let g (v1,v2) = do a <- showTV' v1
                             b <- showTV  v2
                             return ("   "++a++" <- "++b)
              f (cnr,xs) = do ys <- mapM g xs
                              return (unlines' $ ("Child #"++show cnr) : ys)
                                 
              
          list <- mapM f (cliques eqc)
          let msgCliques = "<h3>Cliques</h3>\n" ++ unlines' list
                                                      
          return (unlines [ "<html>"
                          ,"<body text=\"#000000\" bgcolor=\"#FFFFF0\" link=\"#3333FF\" vlink=\"#3333FF\" alink=\"#3333FF\">"
--                          , msgType
                          , msgVertices
                          , msgEdges
                          , msgCliques
                          , "</body>"
                          , "</html>"
                          ]))
          
      addDebug (writeFile ("group"++show i++".html") msg)
     
{-     
makeHTMLindex :: Substitution substitution => Environment -> substitution -> IO ()
makeHTMLindex gamma substitution = writeFile "debug/index.html" $ 
   unlines [ "<html>"
           , "<body text=\"#000000\" bgcolor=\"#FFFFF0\" link=\"#3333FF\" vlink=\"#3333FF\" alink=\"#3333FF\">"
           , "<h3>Inferred Types</h3>"
           , inferredTypes
           , "</body>"
           , "</html>"
           ]
   where inferredTypes = concatMap ((++"<br>\n") . f) (toList gamma)
         f (n,tp) = let i = head (ftv tp)
                    in show n++" :: "++"<a href="++show ("group"++show i++".html")++">"++show tp++"</a>"
                                  
-}
