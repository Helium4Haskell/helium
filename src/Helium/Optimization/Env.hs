module Helium.Optimization.Env where

import Helium.Optimization.Types
import Helium.Optimization.Utils

import Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
--import Data.Set (Set)
--import qualified Data.Set as Set
import Helium.Utils.Utils

data Env key = Env (Map key T) (Map key T)
    deriving (Show)

empty :: Env key
empty = Env Map.empty Map.empty

singletonGlobal :: Ord key => key -> T -> Env key
singletonGlobal key t = insertGlobal key t empty

singletonLocal :: Ord key => key -> T -> Env key
singletonLocal key t = insertLocal key t empty

insertGlobal :: Ord key => key -> T -> Env key -> Env key
insertGlobal key t (Env global local) = Env (Map.insert key t global) local

insertLocal :: Ord key => key -> T -> Env key -> Env key
insertLocal key t (Env global local) = Env global (Map.insert key t local)

union :: Ord key => Env key -> Env key -> Env key
union (Env extendGlobal extendLocal) env = unionLocal extendLocal $ unionGlobal extendGlobal env

unionGlobal :: Ord key => Map key T -> Env key -> Env key
unionGlobal extendGlobal (Env global local) = Env (Map.union extendGlobal global) local

unionLocal :: Ord key => Map key T -> Env key -> Env key
unionLocal extendLocal (Env global local) = Env global (Map.union extendLocal local)

infixr 5 |?|
(|?|) :: (Ord k, Show k) => (Int, Env k) -> (k, String) -> (Int, T)
(uniqueId, env@(Env global local)) |?| (key, err) = case Map.lookup key local of
    Just x -> (uniqueId, x)
    Nothing -> case Map.lookup key global of
        Just x -> freshTOld uniqueId x
        Nothing -> internalError "LVM_Syntax.ag" "|?|" ("key : " ++ show key ++ " : not found in env : " ++ show env ++ " : " ++ err )

infixr 5 |??|
(|??|) :: (Ord k, Show k) => Env k -> (k, String) -> Fresh T
(env@(Env global local)) |??| (key, err) = case Map.lookup key local of
    Just x -> return x
    Nothing -> case Map.lookup key global of
        Just x -> freshT x
        Nothing -> internalError "LVM_Syntax.ag" "|?|" ("key : " ++ show key ++ " : not found in env : " ++ show env ++ " : " ++ err )

