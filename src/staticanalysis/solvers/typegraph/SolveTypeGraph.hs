-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- SolveTypeGraph.hs : Solve a set of type constraints using a type graph.
--   All instances of the class TypeGraph are also an instance of the class
--   ConstraintSolver. Known instance of the class TypeGraph is the data
--   type EquivalenceGroups.
--
------------------------------------------------------------------------------

module SolveTypeGraph where

import Types
import SolveConstraints
import SolverOptions           ( getTypeSynonyms )
import List                    ( partition, groupBy, sortBy, transpose, nub, nubBy, maximumBy, sort )
import Utils                   ( internalError )
import Monad                   ( unless, filterM )
import ConstraintInfo          ( ConstraintInfo(..) )
import TypeGraphConstraintInfo ( TypeGraphConstraintInfo(..) ) 

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

showPath :: TypeGraphConstraintInfo info => Path info -> String
showPath = unlines . map f
   where f (edge,info) = "   "++take 15 (show edge++repeat ' ')++show info

instance TypeGraphConstraintInfo info => Show (EdgeInfo info) where
   show (Initial info)    = '#' : take 5 (show (maybe 0 id $ getPosition info)++repeat ' ')++ "(" ++ show (getInfoSource info) ++ ")"
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
                              

class TypeGraph typegraph info where

   -- functions to construct a typegraph
   initializeTypeGraph        ::                            SolveState typegraph info ()
   addVertex                  :: VertexID -> VertexInfo ->  SolveState typegraph info ()
   addEdge                    :: EdgeID -> EdgeInfo info -> SolveState typegraph info ()
   getVerticesInGroup         :: VertexID ->                SolveState typegraph info [(VertexID,VertexInfo)]
   getChildrenInGroup         :: VertexID ->                SolveState typegraph info [(VertexID,[VertexID])]

   -- functions to detect/remove inconsistencies
   getPathsFrom               :: VertexID -> [VertexID] -> SolveState typegraph info [Path info]
   getConflicts               :: SolveState typegraph info [(UnificationError,Int) ]
   deleteEdge                 :: EdgeID -> SolveState typegraph info ()
   getHeuristics              :: SolveState typegraph info ([EdgeID], [info])

   -- additional functions
   getConstantsInGroup :: VertexID -> SolveState typegraph info [String]
   getConstantsInGroup i = do vertices <- getVerticesInGroup i
                              return (nub [ s | (_,(Just s,_,_)) <- vertices ])

   -- implementing this function implies that addEdge is never called with an "Implied" edge
   addImpliedClique :: Cliques -> SolveState typegraph info ()
   addImpliedClique (cnr,lists) =
       mapM_ id [ do propagateEquality [v1,v2] ; addEdge (EdgeID v1 v2) (Implied cnr p1 p2)
                | (l1,l2) <- combinations lists
                , (v1,p1) <- l1
                , (v2,p2) <- l2
                ]
                
            where combinations :: [a] -> [(a,a)]
                  combinations []     = []
                  combinations (a:as) = zip (repeat a) as ++ combinations as

   isConsistent :: SolveState typegraph info Bool
   isConsistent = do conflicts <- getConflicts
                     return (null conflicts)

   -- implementing this function implies that addEdge is never called with a "Child" edge, and
   -- also addVertex will not be called
   addVertexWithChildren :: VertexID -> VertexInfo -> SolveState typegraph info ()
   addVertexWithChildren i info@(_,children,_) = 
      do addVertex i info
         mapM_ (\(cnr,v) -> addEdge (EdgeID i v) (Child cnr)) (zip [0..] children)

instance (TypeGraphConstraintInfo info,TypeGraph typegraph info) => ConstraintSolver typegraph info where

   initialize =
      do unique <- getUnique
         initializeTypeGraph
         newVariables [0..unique-1]

   unifyTerms info t1 t2 =
      do v1 <- makeTermGraph t1
         v2 <- makeTermGraph t2      
         propagateEquality [v1,v2]    
         addEdge (EdgeID v1 v2) (Initial info)

   makeConsistent =
      do consistent <- isConsistent
         if consistent 
           then 
             checkErrors
           else 
             do (edges, errors) <- getHeuristics                         
                mapM_ addError errors               
                mapM_ deleteEdge edges                        
                addDebug (putStrLn $ "> removed edges "++show edges)
                makeConsistent

   newVariables is = 
      mapM_ (\i -> addVertexWithChildren i (Nothing,[],Nothing)) is

   findSubstForVar i =
   
      do options   <- getSolverOptions
         vertices  <- getVerticesInGroup i
         let synonyms = getTypeSynonyms options
             constants = nubBy (\x y -> fst x == fst y)
                       $ [ original | (_,(_,_,Just original)) <- vertices ]
                      ++ [ (s,cs)   | (_,(Just s,cs,Nothing)) <- vertices ] 
         types <- let f (s,cs) = do ts <- mapM findSubstForVar cs
                                    return (foldl TApp (TCon s) ts)
                  in mapM f constants  
         case types of
           []     -> return (TVar . fst . head $ vertices)
           (t:ts) -> let op t1 t2 = case mguWithTypeSynonyms synonyms t1 t2 of
                                      Left _      -> internalError "SolveTypeGraph.hs" "findSubstForVar" "multiple constants present"
                                      Right (b,s) -> equalUnderTypeSynonyms synonyms (s |-> t1) (s |-> t2)
                     in return (foldr op t ts)

makeTermGraph :: TypeGraph typegraph info => Tp -> SolveState typegraph info Int
makeTermGraph tp = case leftSpine tp of
                     (TVar i,[]) -> do return i
                     (TCon s,ts) -> do options <- getSolverOptions
                                       unique   <- getUnique
                                       setUnique (unique+1)
                                       is <- mapM makeTermGraph ts
                                       let synonyms = getTypeSynonyms options
                                           tp'      = foldl TApp (TCon s) $ map TVar is
                                       case leftSpine (expandTypeConstructor (snd synonyms) tp') of
                                          (TVar i,[])   -> do return i
                                          (TCon s',ts') -> do is' <- mapM makeTermGraph ts'
                                                              let expand | s == s'   = Nothing
                                                                         | otherwise = Just (s,is) 
                                                              addVertexWithChildren unique (Just s',is',expand)
                                                              return unique                                                                                                                                                                    
                     _           -> internalError "SolveTypeGraph.hs" "makeTermGraph" "error in leftSpine(1)"

{- history necessary to avoid non-termination? -}                          
propagateEquality :: TypeGraph typegraph info => [Int] -> SolveState typegraph info ()
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
lookForCliques :: TypeGraph typegraph info => [Int] -> SolveState typegraph info [Cliques]
lookForCliques is = do let f i = do children <- getChildrenInGroup i
                                    let sameNumberOfChildren (_,as) (_,bs) = length as == length bs
                                        {- bug fix 3 december 2002: first sort, then group! -}
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

infinitePaths :: TypeGraph typegraph info => Int -> SolveState typegraph info [[(Int,Int)]]
infinitePaths i = do xs <- rec [] i 
                     mapM cutLastPart xs where

   rec :: TypeGraph typegraph info => [(Int,Int)] -> Int -> SolveState typegraph info [[(Int,Int)]]
   rec history i = do is <- getVerticesInGroup i
                      if any (`elem` (map fst history)) (map fst is)
                        then return [ history ]
                        else do xs <- getChildrenInGroup i
                                case xs of
                                  []       -> return []
                                  (i,cs):_ -> do let f c = rec ((i,c):history) c
                                                 xss <- mapM f cs
                                                 return (concat xss)
                                                 
   cutLastPart :: TypeGraph typegraph info => [(Int,Int)] -> SolveState typegraph info [(Int,Int)]
   cutLastPart [] = return [] 
   cutLastPart (x:xs) = do {- bug fix: 26 november 2002 -}
                           is <- getVerticesInGroup (snd x)                        
                           let (as,bs) = break ((`elem` (map fst is)) . fst) (x:xs)
                           case bs of 
                              []  -> return [] {- this should never occur: INTERNAL ERROR ! -}
                              b:_ ->  return $ reverse (as++[b])

checkErrors :: (TypeGraphConstraintInfo info, TypeGraph typegraph info) => SolveState typegraph info ()
checkErrors =
   do errors  <- getErrors
      options <- getSolverOptions
      let isValidError info = 
             let (t1,t2)  = getTwoTypes info
                 synonyms = getTypeSynonyms options
             in do t1' <- applySubst t1
                   t2' <- applySubst t2
                   case mguWithTypeSynonyms synonyms t1' t2' of
                      Left  _ -> return True
                      Right _ -> do addDebug $ putStrLn $ "Re-inserted edge ("++show t1++"-"++show t2++")"
                                    unifyTerms info t1 t2
                                    return False
      validErrors <- filterM isValidError errors
      setErrors validErrors
