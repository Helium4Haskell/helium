{-| Module      :  DictionaryEnvironment
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module DictionaryEnvironment 
   ( DictionaryEnvironment, DictionaryTree(..) 
   , emptyDictionaryEnvironment, addForDeclaration, addForVariable
   , getPredicateForDecl, getDictionaryTrees
   , makeDictionaryTree, makeDictionaryTrees
   ) where

import Data.FiniteMap
import UHA_Syntax (Name)
import UHA_Utils (NameWithRange(..) )
import Utils (internalError)
import Top.Types

data DictionaryEnvironment = 
     DEnv { declMap :: FiniteMap NameWithRange Predicates
          , varMap  :: FiniteMap NameWithRange [DictionaryTree]
          }
          
data DictionaryTree = ByPredicate Predicate
                    | ByInstance String {- class name -} String {- instance name -} [DictionaryTree]
                    | BySuperClass String {- sub -} String {- super -} DictionaryTree
   deriving Show
   
instance Show DictionaryEnvironment where
   show denv = 
      "{ declMap = " ++ show (fmToList $ declMap denv) ++
      ", varMap = "  ++ show (fmToList $ varMap denv) ++ "}"
       
emptyDictionaryEnvironment :: DictionaryEnvironment
emptyDictionaryEnvironment = 
   DEnv { declMap = emptyFM, varMap = emptyFM }
 
addForDeclaration :: Name -> Predicates -> DictionaryEnvironment -> DictionaryEnvironment
addForDeclaration name predicates dEnv
   | null predicates = dEnv
   | otherwise       = dEnv { declMap = addToFM (declMap dEnv) (NameWithRange name) predicates }
   
addForVariable :: Name -> [DictionaryTree] -> DictionaryEnvironment -> DictionaryEnvironment
addForVariable name trees dEnv
  | null trees = dEnv  
  | otherwise  = dEnv { varMap = addToFM (varMap dEnv) (NameWithRange name) trees }

getPredicateForDecl :: Name -> DictionaryEnvironment -> Predicates
getPredicateForDecl name dEnv =
   case lookupFM (declMap dEnv) (NameWithRange name) of
      Just ps -> ps
      Nothing -> []

getDictionaryTrees :: Name -> DictionaryEnvironment -> [DictionaryTree]
getDictionaryTrees name dEnv = 
   case lookupFM (varMap dEnv) (NameWithRange name) of
      Just dt -> dt
      Nothing -> []

makeDictionaryTrees :: ClassEnvironment -> Predicates -> Predicates -> Maybe [DictionaryTree]
makeDictionaryTrees classEnv ps = mapM (makeDictionaryTree classEnv ps)

makeDictionaryTree :: ClassEnvironment -> Predicates -> Predicate -> Maybe DictionaryTree
makeDictionaryTree classEnv availablePredicates p@(Predicate className tp) =      
   case tp of
      TVar i | p `elem` availablePredicates -> Just (ByPredicate p)
             | otherwise -> case [ (path, availablePredicate)
                                 | availablePredicate@(Predicate c t) <- availablePredicates
                                 , t == tp
                                 , path <- superclassPaths c className classEnv
                                 ] of
                             []     -> Nothing
                             (path,fromPredicate):_ -> 
                                let list = reverse (zip path (tail path))
                                    tree = foldr (uncurry BySuperClass) (ByPredicate fromPredicate) list
                                in Just tree 
                                
      _      -> case byInstance noOrderedTypeSynonyms classEnv p of
                   Nothing -> internalError "DictionaryEnvironment" "makeDictionaryTree" ("reduction error" ++ show (fmToList $ classEnv))
                   Just predicates -> 
                      do let (TCon instanceName, _) = leftSpine tp
                         trees <- makeDictionaryTrees classEnv availablePredicates predicates
                         return (ByInstance className instanceName trees)
