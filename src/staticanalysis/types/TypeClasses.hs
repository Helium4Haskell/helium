-- code from the paper
--   "Typing Haskell in Haskell"

module TypeClasses where

import TypeBasics
import QualifiedTypes
import TypeSubstitution
import TypeUnification
import TypeSynonyms
import List  ( nub, sort )
import Maybe ( catMaybes )
import Monad ( msum )
import Data.FiniteMap

----------------------------------------------------------------------  
-- type classes

type ClassEnvironment = FiniteMap String Class
type Class            = ([String], Instances)
type Instances        = [Instance]
type Instance         = (Predicate, Predicates)

matchPredicates :: OrderedTypeSynonyms -> Predicate -> Predicate -> Maybe FiniteMapSubstitution
matchPredicates synonyms (Predicate s1 t1) (Predicate s2 t2)
   | s1 == s2 = case mgu (freezeVariablesInType t1) t2 of
        Left _  -> Nothing
        Right s -> let f _ = unfreezeVariablesInType
                   in Just (mapFM f s)
   | otherwise = Nothing
                
---------------------------------------------------------------------- 
-- Class Environment

inClassEnvironment :: String -> ClassEnvironment -> Bool
inClassEnvironment = elemFM

superclassPaths :: String -> String -> ClassEnvironment -> [[String]]
superclassPaths from to cs 
   | from == to = [[to]]
   | otherwise  = [ from : path | sc <- superclasses from cs, path <- superclassPaths sc to cs ]

-- for example, Eq is a superclass of Ord
superclasses :: String -> ClassEnvironment -> [String]
superclasses s cs = maybe [] fst (lookupFM cs s)

instances :: String -> ClassEnvironment -> Instances 
instances s cs = maybe [] snd (lookupFM cs s)

---------------------------------------------------------------------- 
-- Head Normal Form

inHeadNormalForm :: Predicate -> Bool
inHeadNormalForm (Predicate s tp) = hnf tp
   where hnf (TVar _)   = True
         hnf (TCon _)   = False
         hnf (TApp t _) = hnf t

listToHeadNormalForm :: OrderedTypeSynonyms -> ClassEnvironment -> Predicates -> Maybe Predicates
listToHeadNormalForm synonyms classes ps = 
   do pss <- mapM (toHeadNormalForm synonyms classes) ps
      return (concat pss)
          
toHeadNormalForm :: OrderedTypeSynonyms -> ClassEnvironment -> Predicate -> Maybe Predicates         
toHeadNormalForm synonyms classes p
   | inHeadNormalForm p = Just [p]
   | otherwise          = do ps <- byInstance synonyms classes p
                             listToHeadNormalForm synonyms classes ps   

---------------------------------------------------------------------- 
-- Entailment

bySuperclass :: ClassEnvironment -> Predicate -> Predicates
bySuperclass classes p@(Predicate s tp) =
   p : concat [ bySuperclass classes (Predicate s' tp) | s' <- superclasses s classes ]

byInstance :: OrderedTypeSynonyms -> ClassEnvironment -> Predicate -> Maybe Predicates
byInstance synonyms classes p@(Predicate s tp) =
   let tryInstance (p',list) = do sub <- matchPredicates synonyms p p'
                                  Just (sub |-> list)
   in msum [ tryInstance it | it <- instances s classes ]

entail :: OrderedTypeSynonyms -> ClassEnvironment -> Predicates -> Predicate -> Bool
entail synonyms classes ps p = 
   scEntail classes ps p ||
   case byInstance synonyms classes p of
      Nothing -> False
      Just qs -> all (entail synonyms classes ps) qs

entailList :: OrderedTypeSynonyms -> ClassEnvironment -> Predicates -> Predicates -> Bool
entailList synonyms classes ps = all (entail synonyms classes ps)

scEntail :: ClassEnvironment -> Predicates -> Predicate -> Bool
scEntail classes ps p = any (p `elem`) (map (bySuperclass classes) ps)

---------------------------------------------------------------------- 
-- Context Reduction

newtype ReductionError = ReductionError Predicate
   deriving Show

contextReduction :: OrderedTypeSynonyms -> ClassEnvironment -> Predicates -> (Predicates, [ReductionError])
contextReduction synonyms classes ps = 
   let op p (a,b) = case toHeadNormalForm synonyms classes p of
                       Just ps -> (ps++a,b)
                       Nothing -> (a,ReductionError p : b)                       
       (predicates, errors) = foldr op ([], []) ps
       
       loop rs []                                   = rs
       loop rs (p:ps) | scEntail classes (rs++ps) p = loop rs ps
                      | otherwise                   = loop (p:rs) ps  
                           
   in (loop [] predicates, errors)

{-
contextReduction' :: OrderedTypeSynonyms -> ClassEnvironment -> [(Predicate,a)] -> ([(Predicate,a)], [a])
contextReduction' synonyms classes ps = 
   let op (predicate, a) (reduced, errors) = 
          case toHeadNormalForm synonyms classes predicate of
             Just ps -> ([(p,a) | p <- ps]++reduced,errors)
             Nothing -> (reduced,a : errors)                       
       (predicates, errors) = foldr op ([], []) ps
       
       loop rs []                 = rs
       loop rs (p:ps) | entailed  = loop rs ps
                      | otherwise = loop (p:rs) ps  
          where entailed = scEntail classes (map fst (rs++ps)) (fst p)                      
                           
   in (loop [] predicates, errors) -}
                             
---------------------------------------------------------------------- 
-- Standard Class Environment

standardClasses :: ClassEnvironment
standardClasses = listToFM $ 

   -- only two instances for Num: Int and Float
   ( "Num",  
     ( ["Eq","Show"] -- superclasses
     , [ (Predicate "Num" intType  , []) -- instances
       , (Predicate "Num" floatType, [])
       ]
     )
   ) :
   -- Eq, Ord and Show all have the same instances
   [ ("Eq" ,  ([]    , makeInstances "Eq"  ))
   , ("Ord",  (["Eq"], makeInstances "Ord" ))
   , ("Show", ([],     makeInstances "Show"))
   ]
   
   where 
     makeInstances className = 
        let basicTypes = [intType, floatType, boolType, charType]
            makeTupleInstance i = 
               ( Predicate className (tupleType [ TVar n | n <- [1..i] ])
               , [ Predicate className (TVar n) | n <- [1..i] ]
               ) 
        in (Predicate className (listType (TVar 0)), [Predicate className (TVar 0)]) -- instance for Lists
           :  [ (Predicate className tp, []) | tp <- basicTypes ]
           ++ map makeTupleInstance (0 : [2..10])
