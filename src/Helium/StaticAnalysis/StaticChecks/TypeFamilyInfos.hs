{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Helium.StaticAnalysis.StaticChecks.TypeFamilyInfos where
import Helium.Syntax.UHA_Syntax ( Name, Names, Type(..), Types, ContextItem(..) )
import Helium.Syntax.UHA_Utils ()
import Data.Maybe (isJust)

deriving instance Show Type
deriving instance Eq Type 
deriving instance Show ContextItem
deriving instance Eq ContextItem 

type TFDeclInfos = [TFDeclInfo]
-- data TFDeclInfo
--   = DOpen Name Names (Maybe Names)
--   | DClosed Name Names (Maybe Names)
--   | DAssoc Name Names (Maybe Names) [(Int, Int)] Name
--   deriving (Show, Eq)

data TFType
  = Open -- open type family
  | Closed -- closed type family
  | ATS -- associated type synonym
  deriving (Show, Eq)

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
-- data TFInstanceInfo
--   = IOpen Name Types Type
--   | IClosed Name Types Type Int --Int resembles the priority that the instance has in the closed type family
--   | IAssoc Name Types Type Types Name
--   deriving (Show, Eq)

data TFInstanceInfo = TII {
    tfiName :: Name 
  , argTypes :: Types
  , defType :: Type
  , tfiType :: TFType
  , priority :: Maybe Int -- priority inside closed type family
  , classTypes :: Maybe Types -- class types in case of ATS
  , classIName :: Maybe Name -- class name of accompanying class
  , preCompat :: [Int] -- contains indices of other instances with which the closed instance is compatible, empty for open tfs and ATSs.
  } deriving (Show, Eq)
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

createATSInst :: Name -> Types -> Type -> Types -> Name -> TFInstanceInfo
createATSInst n ts t ct cn = TII {
    tfiName = n
  , argTypes = ts
  , defType = t
  , tfiType = ATS
  , priority = Nothing
  , classTypes = Just ct
  , classIName = Just cn
  , preCompat = [] 
}

createOpenTFInst :: Name -> Types -> Type -> TFInstanceInfo
createOpenTFInst n ts t = TII {
    tfiName = n
  , argTypes = ts
  , defType = t
  , tfiType = Open
  , priority = Nothing
  , classTypes = Nothing
  , classIName = Nothing
  , preCompat = [] 
}

createClosedTFInst :: Name -> Types -> Type -> Int -> TFInstanceInfo
createClosedTFInst n ts t prio = TII {
    tfiName = n
  , argTypes = ts
  , defType = t
  , tfiType = Closed
  , priority = Just prio
  , classTypes = Nothing
  , classIName = Nothing
  , preCompat = [] 
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