{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Helium.StaticAnalysis.StaticChecks.TypeFamilyInfos where
import Helium.Syntax.UHA_Syntax ( Name, Names, Type(..), Types, ContextItem(..), Range )
import Helium.Syntax.UHA_Utils ()
import Data.Maybe (isJust, fromJust)
import qualified Data.Map as M
import Data.List (elemIndex)
import Unbound.Generics.LocallyNameless hiding (Name)


deriving instance Show Type
deriving instance Eq Type 
deriving instance Ord Type
deriving instance Show ContextItem
deriving instance Eq ContextItem
deriving instance Ord ContextItem 

type TFDeclInfos = [TFDeclInfo]

data TFType
  = Open -- open type family
  | Closed -- closed type family
  | ATS -- associated type synonym
  deriving (Show, Eq, Ord)

data TFDeclInfo = TDI {
    tfdName :: Name -- name of the type family
  , argNames :: Names -- names of the arguments
  , tfdType :: TFType
  , injective :: Bool
  , injNames :: Maybe Names -- possible names that are injective
  , classIdx :: Maybe [(Int, Int)] -- possible indices of tf args linked to class args (ATS)
  , classDName :: Maybe Name -- possible name of the accompanying class
  } deriving (Show, Eq)

type TFInstanceInfos = [TFInstanceInfo]

data TFInstanceInfo = TII {
    tfiName :: Name 
  , argTypes :: Types
  , defType :: Type
  , tfiType :: TFType
  , priority :: Maybe Int -- priority inside closed type family
  , classTypes :: Maybe Types -- class types in case of ATS
  , classIName :: Maybe Name -- class name of accompanying class
  , preCompat :: [Int] -- contains indices of other instances with which the closed instance is compatible, empty for open tfs and ATSs.
  , tfiRange :: Range
  } deriving (Show, Eq, Ord)

instance Alpha TFInstanceInfo where
   fvAny' _ _ = pure 
   swaps' = error "swaps'"
   lfreshen' = error "lfreshen'"
   freshen' = error "freshen'"
   aeq' = error "aeq'"
   acompare' = error "acompare'"
   close _ _ x = x
   open _ _ x = x
   isPat = error "isPat"
   isTerm = error "isTerm"
   isEmbed = error "isEmbed"
   nthPatFind = error "nthPatFind"
   namePatFind _ = error "namePatFind"
-------------------------------------
-- UTILS

-- decl info creation methods
createATSDecl :: Name -> Names -> Maybe Names -> [(Int, Int)] -> Name -> TFDeclInfo
createATSDecl n ns ins classIs cn = TDI {
    tfdName = n
  , argNames = ns
  , tfdType = ATS
  , injective = isJust ins
  , injNames = ins
  , classIdx = Just classIs
  , classDName = Just cn
}

createOpenTFDecl :: Name -> Names -> Maybe Names -> TFDeclInfo
createOpenTFDecl n ns ins = TDI {
    tfdName = n
  , argNames = ns
  , tfdType = Open
  , injective = isJust ins
  , injNames = ins
  , classIdx = Nothing
  , classDName = Nothing
}

createClosedTFDecl :: Name -> Names -> Maybe Names -> TFDeclInfo
createClosedTFDecl n ns ins = TDI {
    tfdName = n
  , argNames = ns
  , tfdType = Closed
  , injective = isJust ins
  , injNames = ins
  , classIdx = Nothing
  , classDName = Nothing
}

createATSInst :: Name -> Types -> Type -> Types -> Name -> Range -> TFInstanceInfo
createATSInst n ts t ct cn range = TII {
    tfiName = n
  , argTypes = ts
  , defType = t
  , tfiType = ATS
  , priority = Nothing
  , classTypes = Just ct
  , classIName = Just cn
  , preCompat = []
  , tfiRange = range
}

createOpenTFInst :: Name -> Types -> Type -> Range -> TFInstanceInfo
createOpenTFInst n ts t range = TII {
    tfiName = n
  , argTypes = ts
  , defType = t
  , tfiType = Open
  , priority = Nothing
  , classTypes = Nothing
  , classIName = Nothing
  , preCompat = [] 
  , tfiRange = range
}

createClosedTFInst :: Name -> Types -> Type -> Int -> Range -> TFInstanceInfo
createClosedTFInst n ts t prio range= TII {
    tfiName = n
  , argTypes = ts
  , defType = t
  , tfiType = Closed
  , priority = Just prio
  , classTypes = Nothing
  , classIName = Nothing
  , preCompat = [] 
  , tfiRange = range
}

insertPreCompat :: [Int] -> TFInstanceInfo -> TFInstanceInfo
insertPreCompat pcs ti = ti { preCompat = pcs }

-- Like fst and snd
thrd :: (a, b, c) -> c
thrd (_, _, z) = z

-- Builds all unique pairs inside the list.
createPairs :: Show a => [a] -> [(a, a)]
createPairs xs = [(x, y) | (x:ys) <- tails xs, y <- ys]

tails :: [a] -> [[a]]
tails [] = []
tails (x:xs) = (x:xs) : tails xs

splitBy :: (a -> Bool) -> [a] -> ([a], [a])
splitBy p (x:xs) = let (l, r) = splitBy p xs
  in if p x then (x:l, r) else (l, x:r)
splitBy _ []     = ([], [])

ordPrio :: TFInstanceInfo -> TFInstanceInfo -> Ordering
ordPrio i1 i2 
  | priority i1 < priority i2 = LT
  | priority i1 > priority i2 = GT 
  | otherwise = EQ 

-- Obtains the type family declaration info as needed for `typeToMonoType`
obtainTyFams :: TFDeclInfos -> [(String, Int)]
obtainTyFams = map (\d -> (show $ tfdName d, length $ argNames d))

-- Obtains the type family declaration info as needed for KindChecking.ag
obtainTyFams1 :: TFDeclInfos -> [(Name, Int)]
obtainTyFams1 = map (\d -> (tfdName d, length $ argNames d))

obtainInjectiveTFInstances :: TFDeclInfos -> TFInstanceInfos -> TFInstanceInfos
obtainInjectiveTFInstances dis tis = let
  iNames = obtInjDeclNames dis

  in [inst | inst <- tis, tfiName inst `elem` iNames]
  where
    obtInjDeclNames (d:decls) = if injective d
                                  then tfdName d : obtInjDeclNames decls
                                  else obtInjDeclNames decls
    obtInjDeclNames []        = []

-- Builds Injective environment.
buildInjectiveEnv :: TFDeclInfos -> M.Map String [Int]
buildInjectiveEnv
  = foldr (\ d
          -> M.insert
                (show $ tfdName d) (getInjIndices (argNames d) (injNames d))
          )
          M.empty

getInjIndices :: Names -> Maybe Names -> [Int]
getInjIndices _  Nothing = []
getInjIndices ns (Just ins) = map (fromJust . flip elemIndex ins) ns