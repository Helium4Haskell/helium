module IsTypeGraph where

import Types
import List 
import IsSolver
import SolveState
import Utils (internalError)
import TypeGraphConstraintInfo
                     
class (TypeGraphConstraintInfo info, Monad m) => IsTypeGraph m info | m -> info where

   -- functions to construct a typegraph
   initializeTypeGraph        ::                            m ()
   addEdge                    :: EdgeID -> EdgeInfo info -> m ()
   addVertexWithChildren      :: VertexID -> VertexInfo ->  m ()
   addImpliedClique           :: Cliques                 -> m ()
   getVerticesInGroup         :: VertexID ->                m [(VertexID,VertexInfo)]
   getChildrenInGroup         :: VertexID ->                m [(VertexID,[VertexID])]

   -- functions to detect/remove inconsistencies
   getPathsFrom               :: VertexID -> [VertexID] -> m [Path info]
   getConflicts               ::                           m [(UnificationError,Int) ]
   deleteEdge                 :: EdgeID ->                 m ()
   getHeuristics              ::                           m ([EdgeID], [info])
   getConstantsInGroup        :: VertexID ->               m [String]
      
   -- additional functions
                     
isConsistent :: IsTypeGraph m info => m Bool
isConsistent = do conflicts <- getConflicts
                  return (null conflicts)

makeTermGraph :: (IsTypeGraph m info, MonadState (SolveState m info a) m) => Tp -> m Int
makeTermGraph tp = case leftSpine tp of
                     (TVar i,[]) -> do return i
                     (TCon s,ts) -> do synonyms <- getTypeSynonyms
                                       unique   <- getUnique
                                       setUnique (unique+1)
                                       is <- mapM makeTermGraph ts
                                       let tp' = foldl TApp (TCon s) $ map TVar is
                                       case leftSpine (expandTypeConstructor (snd synonyms) tp') of
                                          (TVar i,[])   -> do return i
                                          (TCon s',ts') -> do is' <- mapM makeTermGraph ts'
                                                              let expand | s == s'   = Nothing
                                                                         | otherwise = Just (s,is) 
                                                              addVertexWithChildren unique (Just s',is',expand)
                                                              return unique                                                                                                                                                                    
                     _           -> internalError "SolveTypeGraph.hs" "makeTermGraph" "error in leftSpine(1)"

checkErrors :: (IsTypeGraph m info, MonadState (SolveState m info a) m, IsSolver m info) => m ()
checkErrors =
   do errors   <- getErrors
      synonyms <- getTypeSynonyms
      let isValidError info | isReductionErrorInfo info = return True
          isValidError info = 
             let (t1,t2) = getTwoTypes info
             in do t1' <- applySubst t1
                   t2' <- applySubst t2
                   case mguWithTypeSynonyms synonyms t1' t2' of
                      Left  _ -> return True
                      Right _ -> do addDebug $ "Re-inserted edge ("++show t1++"-"++show t2++")"
                                    unifyTerms info t1 t2
                                    return False
      validErrors <- filterM isValidError errors
      setErrors validErrors
         
{- history necessary to avoid non-termination? -}                          
propagateEquality :: IsTypeGraph m info => [Int] -> m ()
propagateEquality = rec [] where

   rec history is
     | length list < 2     = return ()
     | list `elem` history = return ()
     | otherwise           = do cliques <- lookForCliques (nub is)
                                let addClique c = do rec (list : history) (map (fst . head) (snd c))
                                                     addImpliedClique c
                                mapM_ addClique cliques
    
    where list = sort (nub is)
                     
{- rewrite this function as soon as possible! -}
lookForCliques :: IsTypeGraph m info => [Int] -> m [Cliques]
lookForCliques is = do let f i = do children <- getChildrenInGroup i
                                    let sameNumberOfChildren (_,as) (_,bs) = length as == length bs
                                        {- bug fix 3 dece;mber 2002: first sort, then group! -}
                                        sameOrd (_,as) (_,bs) = compare (length as) (length bs)
                                        lengthOfList ((_,as) : _) = length as
                                    return ((map (\z -> (lengthOfList z,z)) . groupBy sameNumberOfChildren . sortBy sameOrd . sortBy (\x y -> compare (snd x) (snd y))) children)

                       lists <- mapM f is

                       let makeCliques xs = case xs of
                              []                 -> []
                              []:rest            -> makeCliques rest
                              ((len,xs):ys):rest -> let (same,rest') = unzip (map (partition (\x -> len == fst x)) rest)
                                                        this = zip [0..] $ transpose $ map transpose $ map (map (\(p,cs) -> zip cs (repeat p))) (xs : map snd (concat same))
                                                    in if null (concat same)
                                                         then makeCliques (ys:rest)
                                                         else this ++ makeCliques (ys:rest)
                       return (makeCliques lists)

infinitePaths :: IsTypeGraph m info => Int -> m [[(Int,Int)]]
infinitePaths i = do xs <- rec [] i 
                     mapM cutLastPart xs where

   rec :: IsTypeGraph m info => [(Int,Int)] -> Int -> m [[(Int,Int)]]
   rec history i = do is <- getVerticesInGroup i
                      if any (`elem` (map fst history)) (map fst is)
                        then return [ history ]
                        else do xs <- getChildrenInGroup i
                                case xs of
                                  []       -> return []
                                  (i,cs):_ -> do let f c = rec ((i,c):history) c
                                                 xss <- mapM f cs
                                                 return (concat xss)
                                                 
   cutLastPart :: IsTypeGraph m info => [(Int,Int)] -> m [(Int,Int)]
   cutLastPart [] = return [] 
   cutLastPart (x:xs) = do {- bug fix: 26 november 2002 -}
                           is <- getVerticesInGroup (snd x)                        
                           let (as,bs) = break ((`elem` (map fst is)) . fst) (x:xs)
                           case bs of 
                              []  -> return [] {- this should never occur: INTERNAL ERROR ! -}
                              b:_ ->  return $ reverse (as++[b])
                              
-----------------------------------------------------------------------------------------

type VertexID      = Int
type VertexInfo    = ( Maybe String               -- in case it represents a type constant
                     , [VertexID]                 -- its children
                     , Maybe (String,[VertexID])  -- original type synonym
                     )
data EdgeID        = EdgeID VertexID VertexID
data EdgeInfo info = Initial info
                   | Implied Int VertexID VertexID
                   | Child Int
type Clique        = (Int, [(VertexID,VertexID)] )
type Cliques       = (Int,[[(VertexID,VertexID)]])
type Path  info    = [(EdgeID,EdgeInfo info)]
type Paths info    = [Path info]

showPath :: Show info => Path info -> String
showPath = unlines . map f
   where f (edge,info) = "   "++take 15 (show edge++repeat ' ')++show info

instance Show info => Show (EdgeInfo info) where
   show (Initial info)    = show info
   show (Implied i p1 p2) = "(" ++ show i ++ " : " ++ show (p1,p2) ++ ")"
   show (Child i)         = "(" ++ show i ++ ")"

instance Show EdgeID where
   show (EdgeID a b) = "("++show a'++"-"++show b'++")"
     where (a',b') = if a <= b then (a,b) else (b,a)
     
instance Eq EdgeID where
   EdgeID a b == EdgeID c d = (a == c && b == d) || (a == d && b == c)
   
instance Ord EdgeID where
   EdgeID a b <= EdgeID c d = order (a,b) <= order (c,d)
      where order (i,j) = if i <= j then (i,j) else (j,i)                              

{- older default definitions 

   addVertexWithChildren :: VertexID -> VertexInfo -> m ()
   addVertexWithChildren i info@(_,children,_) = 
      do addVertex i info
         mapM_ (\(cnr,v) -> addEdge (EdgeID i v) (Child cnr)) (zip [0..] children)
         
   addImpliedClique :: Cliques -> m ()
   addImpliedClique (cnr,lists) =
       mapM_ id [ do propagateEquality [v1,v2] ; addEdge (EdgeID v1 v2) (Implied cnr p1 p2)
                | (l1,l2) <- combinations lists
                , (v1,p1) <- l1
                , (v2,p2) <- l2
                ]
                
            where combinations :: [a] -> [(a,a)]
                  combinations []     = []
                  combinations (a:as) = zip (repeat a) as ++ combinations as         
                  
   getConstantsInGroup :: VertexID -> m [String]
   getConstantsInGroup i = do vertices <- getVerticesInGroup i
                              return (nub [ s | (_,(Just s,_,_)) <- vertices ])                  
-}
