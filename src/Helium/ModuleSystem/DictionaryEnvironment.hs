{-| Module      :  DictionaryEnvironment
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.ModuleSystem.DictionaryEnvironment 
   ( DictionaryEnvironment, DictionaryTree(..) 
   , PredicateWithSource(..), superClassToPredicateWithSource
   , emptyDictionaryEnvironment, addForDeclaration, addForVariable
   , getPredicateForDecl, getDictionaryTrees
   , makeDictionaryTree, makeDictionaryTrees
   , setCurrentClassNames, currentClassNames
   ) where

import qualified Data.Map as M
import Data.List(find)
import Data.Maybe
import Helium.Syntax.UHA_Syntax (Name)
import Helium.Syntax.UHA_Utils
import Helium.Utils.Utils

import Helium.Top.Top.Types

data DictionaryEnvironment = 
     DEnv { declMap :: M.Map NameWithRange Predicates
          , varMap  :: M.Map NameWithRange [DictionaryTree]
          , currentClassNames :: [(Name, String)]
          }

data PredicateWithSource 
    = PredicateFunction Predicate
    | PredicateSuperInstance Predicate String {- Own predicate -} String {- type variable-} String {- ClassName -}
    deriving (Eq, Show)
    
superClassToPredicateWithSource :: Predicate -> String -> String -> PredicateWithSource
superClassToPredicateWithSource p@(Predicate pn _) className typeVariable = PredicateSuperInstance p pn typeVariable className
    

instance Substitutable PredicateWithSource where
    sub |-> (PredicateFunction p) = PredicateFunction  (sub |-> p)
    sub |-> (PredicateSuperInstance p pn pv pc) = PredicateSuperInstance (sub |-> p) pn pv pc
    ftv = ftv . getPredicateFromPredicateWithSource


getPredicateFromPredicateWithSource :: PredicateWithSource -> Predicate
getPredicateFromPredicateWithSource (PredicateFunction p) = p
getPredicateFromPredicateWithSource (PredicateSuperInstance p _ _ _) = p
          
data DictionaryTree = ByPredicate Predicate
                    | ByInstance String {- class name -} String {- instance name -} [Tp] [DictionaryTree]
                    | BySuperClass String {- sub -} String {- super -} Tp DictionaryTree
                    | ByCurrentClass String
                    | BySuperInstance Predicate String {- ClassName -} String {- Type Variable -}
   deriving Show
   
instance Show DictionaryEnvironment where
   show denv = 
      "{ declMap = " ++ unlines (map show (M.assocs $ declMap denv)) ++
      ", varMap = "  ++ unlines (map show (M.assocs $ varMap denv)) ++ 
      ", currentClassNames = " ++ show (currentClassNames denv) ++ "}"
     
setCurrentClassNames :: [(Name, String)] -> DictionaryEnvironment -> DictionaryEnvironment
setCurrentClassNames cur denv = denv{
    currentClassNames = cur
    }      

emptyDictionaryEnvironment :: DictionaryEnvironment
emptyDictionaryEnvironment = 
   DEnv { declMap = M.empty, varMap = M.empty, currentClassNames = [] }
 
addForDeclaration :: Name -> Predicates -> DictionaryEnvironment -> DictionaryEnvironment
addForDeclaration name predicates dEnv
   | null predicates = dEnv
   | otherwise       = dEnv { declMap = M.insert (NameWithRange name) predicates (declMap dEnv) }
   
addForVariable :: Name -> [DictionaryTree] -> DictionaryEnvironment -> DictionaryEnvironment
addForVariable name trees dEnv
  | null trees = dEnv  
  | otherwise  = dEnv { varMap = M.insert (NameWithRange name) trees (varMap dEnv) }

getPredicateForDecl :: Name -> DictionaryEnvironment -> Predicates
getPredicateForDecl name dEnv =
   M.findWithDefault [] (NameWithRange name) (declMap dEnv)

getDictionaryTrees :: Name -> DictionaryEnvironment -> [DictionaryTree]
getDictionaryTrees name dEnv = M.findWithDefault [] (NameWithRange name) (varMap dEnv)

makeDictionaryTrees :: ClassEnvironment -> [PredicateWithSource] -> Maybe String -> Maybe Predicate -> [PredicateWithSource] -> Maybe [DictionaryTree]
makeDictionaryTrees classEnv ps currentClass curPred x = mapM (makeDictionaryTree classEnv ps currentClass curPred) x

makeDictionaryTree :: ClassEnvironment -> [PredicateWithSource] -> Maybe String -> Maybe Predicate -> PredicateWithSource -> Maybe DictionaryTree
makeDictionaryTree classEnv availablePredicates currentClass curPred ps =
    let
        p@(Predicate className tp) = getPredicateFromPredicateWithSource ps
        bareAvailablePredicates = map getPredicateFromPredicateWithSource availablePredicates
        baseSuperClassPredicates = map getPredicateFromPredicateWithSource $ filter isSuperClassPredicate availablePredicates
        hasSuperClassPredicate prd = any (\ps' -> isSuperClassPredicate ps' && getPredicateFromPredicateWithSource ps' == getPredicateFromPredicateWithSource prd) availablePredicates
        isSuperClassPredicate (PredicateFunction _) = False
        isSuperClassPredicate (PredicateSuperInstance _ _ _ _) = True
        getSuperClassPredicate :: Predicate -> PredicateWithSource
        getSuperClassPredicate prd = fromMaybe (PredicateFunction prd) $ find (\ps' -> isSuperClassPredicate ps' && getPredicateFromPredicateWithSource ps' == prd) availablePredicates
        convertPredicate :: (Predicate -> DictionaryTree) -> PredicateWithSource -> DictionaryTree
        convertPredicate f prd  | hasSuperClassPredicate prd = let
                                                                 (PredicateSuperInstance prd' pn tv _) = getSuperClassPredicate $ getPredicateFromPredicateWithSource prd 
                                                               in BySuperInstance prd' pn tv
                                | otherwise = f (getPredicateFromPredicateWithSource prd)
    in 
    case tp of
        TVar _  | curPred == Just (getPredicateFromPredicateWithSource ps) -> Just (ByCurrentClass $ fromMaybe (error "Cannot fromMaybe") currentClass)
                | p `elem` bareAvailablePredicates -> Just (convertPredicate ByPredicate ps)
                | otherwise -> case [ (path, availablePredicate)
                                    | availablePredicate@(Predicate c t) <- bareAvailablePredicates
                                    , t == tp
                                    , path <- superclassPaths c className classEnv
                                    ] of
                                []     -> Nothing
                                (path,fromPredicate):others -> 
                                    let list = reverse (zip path (tail path)) -- ByInstance String {- class name -} String {- instance name -} [DictionaryTree]
                                        tree = foldr (\(sub, super) -> BySuperClass sub super tp) 
                                            (maybe (ByPredicate fromPredicate) ByCurrentClass currentClass) 
                                            list
                                    in if fromPredicate `elem` baseSuperClassPredicates 
                                        then Just (foldr (\(sub, super) -> BySuperClass sub super tp) 
                                            (convertPredicate ByPredicate (getSuperClassPredicate fromPredicate)) list) 
                                        else Just tree
                                
        _      -> case byInstance noOrderedTypeSynonyms classEnv p of
                    Nothing -> internalError "DictionaryEnvironment" "makeDictionaryTree" ("reduction error" ++ show (M.assocs classEnv))
                    Just predicates -> 
                        do 
                            let (TCon instanceName, args) = leftSpine tp
                            trees <- makeDictionaryTrees classEnv availablePredicates currentClass curPred $ map PredicateFunction predicates
                            return (ByInstance className instanceName args trees)
