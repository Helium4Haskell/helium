module IsTypeGraph where

import Types
import List 
import IsSolver
import SolveState
import Utils (internalError)
import TypeGraphConstraintInfo
import Debug.Trace (trace)
                   
debugTypeGraph :: Bool
debugTypeGraph = False                   
                   
class (TypeGraphConstraintInfo info, Monad m) => IsTypeGraph m info | m -> info where

   -- functions to construct a typegraph
   addEdge   :: EdgeID -> info ->         m ()
   addVertex :: VertexID -> VertexInfo -> m ()
   addClique :: Cliques ->                m ()
   
   verticesInGroupOf  :: VertexID -> m [(VertexID, VertexInfo)]
   childrenInGroupOf  :: VertexID -> m [(VertexID, (VertexID, VertexID))]
   constantsInGroupOf :: VertexID -> m [String]
 
   allPaths           :: VertexID -> VertexID   -> m [Path info]
   allPathsList       :: VertexID -> [VertexID] -> m [Path info]

   -- functions to detect/remove inconsistencies
   deleteClique    :: Cliques -> m ()
   deleteEdge      :: EdgeID  -> m ()   
   applyHeuristics :: m ()
   getConflicts    :: m [(UnificationError,Int)]  
       
   -- default definitions
   allPaths i1 i2    = allPathsList i1 [i2]
   allPathsList i is = mapM (allPaths i) is >>= (return . concat)
   
   childrenInGroupOf i = 
      do vs <- verticesInGroupOf i 
         return [ (i, (left, right)) | (i, (VApp left right, _)) <- vs ]
         
   constantsInGroupOf i = 
      do vs <- verticesInGroupOf i 
         return (nub [ s | (_,(VCon s, _)) <- vs ])
   
makeTermGraph :: (IsTypeGraph m info, MonadState (SolveState m info a) m) => Tp -> m Int
makeTermGraph tp = 
   debugTrace ("makeTermGraph " ++ show tp) >>
   case leftSpine tp of 
      (TVar i, tps) -> 
         do is <- mapM makeTermGraph tps
            makeLeftSpine Nothing i is
      (TCon s, tps) ->
         do synonyms <- getTypeSynonyms
            is <- mapM makeTermGraph tps
            let tp' = expandTypeConstructor (snd synonyms) (foldl TApp (TCon s) (map TVar is))
            if tp == tp' 
              then do i <- makeNewVertex (VCon s, Nothing)
                      makeLeftSpine Nothing i is
              else do let (a, as) = leftSpine tp' 
                      ia'  <- makeTermGraph a
                      ias' <- mapM makeTermGraph as
                      makeLeftSpine (Just (s, is)) ia' ias'                      
      _ -> internalError "SolveTypeGraph.hs" "makeTermGraph" "error in leftSpine(1)"
      
 where 
   makeLeftSpine original i is = 
      case is of
         []    -> return i
         hd:tl -> do unique <- makeNewVertex (VApp i hd, if null tl then original else Nothing)
                     makeLeftSpine original unique tl
                     
   makeNewVertex vertexInfo =
      do unique <- getUnique
         setUnique (unique + 1)                 
         addVertex unique vertexInfo
         return unique

checkErrors :: (IsTypeGraph m info, MonadState (SolveState m info a) m, IsSolver m info) => m ()
checkErrors =
   debugTrace "checkErrors" >>
   do errors   <- getErrors
      synonyms <- getTypeSynonyms
      let isValidError info | isReductionErrorInfo info = return True
          isValidError info = 
             let (t1,t2) = getTwoTypes info
             in do t1' <- applySubst t1
                   t2' <- applySubst t2
                   case mguWithTypeSynonyms synonyms t1' t2' of
                      Left  _ -> return True
                      Right _ -> do addDebug $ putStrLn $ "Re-inserted edge ("++show t1++"-"++show t2++")"
                                    unifyTerms info t1 t2
                                    return False
      validErrors <- filterM isValidError errors
      setErrors validErrors
                                   
propagateEquality :: IsTypeGraph m info => [Int] -> m ()
propagateEquality is = 
   debugTrace ("propagateEquality " ++ show is)  >> 
   do rec [] is where

   rec history is
     | length list < 2 || list `elem` history = return ()
     | otherwise = 
          let f c = do rec (list : history) (map (fst . head) (snd c))
                       addClique c
          in do cliques <- lookForCliques list
                mapM_ f cliques 
     
    where list = sort (nub is)
 
lookForCliques :: IsTypeGraph m info => [Int] -> m [Cliques]
lookForCliques is = 
   debugTrace ("lookForCliques " ++ show is) >>
   do childrenList <- mapM childrenInGroupOf is
      let notEmpties = filter (not . null) childrenList  
          f selF xs  = [ (selF is, p) | (p, is) <- xs ]
      return [ (nr, map (f selector) notEmpties)
             | length notEmpties > 1 
             , (nr, selector) <- [(0, fst), (1, snd)]
             ]

infinitePaths :: IsTypeGraph m info => Int -> m [[(Int,Int)]]
infinitePaths i = 
   debugTrace ("infinitePaths " ++ show i) >> 
   do xs <- rec [] i 
      mapM cutLastPart xs where

   rec :: IsTypeGraph m info => [(Int,Int)] -> Int -> m [[(Int,Int)]]
   rec history i = do is <- verticesInGroupOf i
                      if any (`elem` (map fst history)) (map fst is)
                        then return [ history ]
                        else do xs <- childrenInGroupOf i
                                case xs of
                                  []            -> return []
                                  (i,(c1,c2)):_ -> do result1 <- rec ((i,c1):history) c1
                                                      result2 <- rec ((i,c2):history) c2
                                                      return (result1 ++ result2)
                                                 
   cutLastPart :: IsTypeGraph m info => [(Int,Int)] -> m [(Int,Int)]
   cutLastPart [] = return [] 
   cutLastPart (x:xs) = do {- bug fix: 26 november 2002 -}
                           is <- verticesInGroupOf (snd x)   
                           let (as,bs) = break ((`elem` (map fst is)) . fst) (x:xs)
                           case bs of                              
                              b:_ -> return $ reverse (as++[b])
                              _   -> internalError "IsTypeGraph.hs" "infinitePaths" "cutLastPart: empty list"

debugTrace :: Monad m => String -> m ()
debugTrace message
   | debugTypeGraph = trace (message++";") (return ())
   | otherwise      = return ()
                              
-----------------------------------------------------------------------------------------

type VertexID      = Int
type VertexInfo    = ( VertexKind 
                     , Maybe (String,[VertexID])  -- original type synonym
                     )
data VertexKind = VVar
                | VCon String
                | VApp VertexID VertexID
   deriving (Show, Eq, Ord)                
                     
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
   
