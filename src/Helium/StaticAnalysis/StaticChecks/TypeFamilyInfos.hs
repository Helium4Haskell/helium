{-# LANGUAGE StandaloneDeriving #-}
{-# OPTIONS_GHC -Wno-orphans #-}
module Helium.StaticAnalysis.StaticChecks.TypeFamilyInfos where
import Helium.Syntax.UHA_Syntax ( Name, Names, Type(..), Types, ContextItem(..) )
import Helium.Syntax.UHA_Utils ()

deriving instance Show Type
deriving instance Show ContextItem

type TFDeclInfos = [TFDeclInfo]
data TFDeclInfo
  = DOpen Name Names (Maybe Names)
  | DClosed Name Names (Maybe Names)
  | DAssoc Name Names (Maybe Names) [(Int, Int)] Name
  deriving Show

type TFInstanceInfos = [TFInstanceInfo]
data TFInstanceInfo
  = IOpen Name Types Type
  | IClosed Name Types Type Int --Int resembles the priority that the instance has in the closed type family
  | IAssoc Name Types Type Types Name
  deriving Show
-------------------------------------
-- UTILS

-- Obtains the name of a typefam declaration
obtainDeclName :: TFDeclInfo -> Name
obtainDeclName (DOpen n _ _)      = n
obtainDeclName (DClosed n _ _)    = n
obtainDeclName (DAssoc n _ _ _ _) = n

-- Obtains the name of a typefam instance
obtainInstanceName :: TFInstanceInfo -> Name
obtainInstanceName (IOpen n _ _)      = n
obtainInstanceName (IClosed n _ _ _)  = n
obtainInstanceName (IAssoc n _ _ _ _) = n

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
obtainTyFams (DAssoc n ns _ _ _:ts) = (show n, length ns) : obtainTyFams ts
obtainTyFams (DClosed n ns _:ts)    = (show n, length ns) : obtainTyFams ts
obtainTyFams (DOpen n ns _:ts)      = (show n, length ns) : obtainTyFams ts
obtainTyFams []                     = []

-- Obtains the type family declaration info as needed for KindChecking.ag
obtainTyFams1 :: TFDeclInfos -> [(Name, Int)]
obtainTyFams1 (DAssoc n ns _ _ _:ts) = (n, length ns) : obtainTyFams1 ts
obtainTyFams1 (DClosed n ns _:ts)    = (n, length ns) : obtainTyFams1 ts
obtainTyFams1 (DOpen n ns _:ts)      = (n, length ns) : obtainTyFams1 ts
obtainTyFams1 []                     = []

-- Obtains the argument types of a type family instance (lhs)
obtainArguments :: TFInstanceInfo -> Types
obtainArguments (IAssoc _ ts _ _ _) = ts
obtainArguments (IClosed _ ts _ _)  = ts
obtainArguments (IOpen _ ts _)      = ts

-- Obtains the definition of a type family instance (rhs)
obtainDefinition :: TFInstanceInfo -> Type
obtainDefinition (IAssoc _ _ t _ _) = t
obtainDefinition (IClosed _ _ t _)  = t
obtainDefinition (IOpen _ _ t)      = t