module DictionaryEnvironment 
   ( DictionaryEnvironment, DictionaryTree(..) 
   , emptyDictionaryEnvironment, addForDeclaration, addForVariable
   , getPredicateForDecl, getDictionaryTrees
   ) where

import Data.FiniteMap
import UHA_Syntax (Name)
import UHA_Utils (NameWithRange(..) )
import Utils (internalError)
import Types

data DictionaryEnvironment = 
     DEnv { declMap :: FiniteMap NameWithRange Predicates
          , varMap  :: FiniteMap NameWithRange [DictionaryTree]
          }
          
data DictionaryTree = ByPredicate Predicate
                    | ByInstance String {- class name -} String {- instance name -} [DictionaryTree]
                    | BySuperClass String {- sub -} String {- super -} DictionaryTree
          
emptyDictionaryEnvironment :: DictionaryEnvironment
emptyDictionaryEnvironment = 
   DEnv { declMap = emptyFM, varMap = emptyFM }
 
addForDeclaration :: Name -> Predicates -> DictionaryEnvironment -> DictionaryEnvironment
addForDeclaration name predicates dEnv
   | null predicates = dEnv
   | otherwise       = dEnv { declMap = addToFM (declMap dEnv) (NameWithRange name) predicates }
   
addForVariable :: Name -> Predicates -> Predicates -> DictionaryEnvironment -> DictionaryEnvironment
addForVariable name availablePredicates predicates dEnv
  | null predicates = dEnv  
  | otherwise       = let tree = makeDictionaryTrees availablePredicates predicates
                      in dEnv { varMap = addToFM (varMap dEnv) (NameWithRange name) tree }

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

makeDictionaryTrees :: Predicates -> Predicates -> [DictionaryTree]
makeDictionaryTrees ps = map (makeDictionaryTree ps)

makeDictionaryTree :: Predicates -> Predicate -> DictionaryTree
makeDictionaryTree availablePredicates p@(Predicate className tp) =      
   case tp of
      TVar i | p `elem` availablePredicates -> ByPredicate p
             | otherwise -> case [ (path, availablePredicate)
                                 | availablePredicate@(Predicate c t) <- availablePredicates
                                 , t == tp
                                 , path <- superclassPaths c className standardClasses
                                 ] of
                             []     -> internalError "DictionaryEnvironment" "getDictionary" "no path"
                             (path,fromPredicate):_ -> 
                                foldr (uncurry BySuperClass) (ByPredicate fromPredicate) (reverse (zip path (tail path)))
                                
      _      -> case byInstance noOrderedTypeSynonyms standardClasses p of
                   Nothing -> internalError "ToCoreExpr" "getDictionary" "reduction error"
                   Just predicates -> 
                      let (TCon instanceName, _)  = leftSpine tp
                      in ByInstance className instanceName (makeDictionaryTrees availablePredicates predicates)
