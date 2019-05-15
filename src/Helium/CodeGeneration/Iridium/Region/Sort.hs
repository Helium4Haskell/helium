module Helium.CodeGeneration.Iridium.Region.Sort
  ( TypeVar(..), showSubscript
  , Sort(..), SortArgument(..), sortArgumentEmpty, SortArgumentRegion(..)
  , sortArgumentSubstitute
  ) where

import Lvm.Core.Type
import qualified Data.IntMap as IntMap
import Data.List

newtype TypeVar = TypeVar Int
  deriving (Eq, Ord)

showSubscript :: Int -> String
showSubscript idx
  | idx >= 0 = showInt idx ""
  | otherwise = '₋' : showInt (-idx) ""
  where
    numbersSubscript = "₀₁₂₃₄₅₆₇₈₉"
    showInt :: Int -> String -> String
    showInt value accum
      | rest == 0 = accum'
      | otherwise = showInt rest accum'
      where
        accum' = char : accum
        digit = value `mod` 10
        char = numbersSubscript !! digit
        rest = value `div` 10

instance Show TypeVar where
  show (TypeVar idx) = 'α' : showSubscript idx

data Sort
  = SortForall !TypeVar !Sort
  | SortFun !(SortArgument Sort) !(SortArgument SortArgumentRegion) !Sort
  | SortRelation

data SortArgument a
  = SortArgumentMonomorphic !a
  | SortArgumentPolymorphic !TypeVar ![Type]
  | SortArgumentList ![SortArgument a]

sortArgumentEmpty :: SortArgument a
sortArgumentEmpty = SortArgumentList []

instance Functor SortArgument where
  fmap f (SortArgumentMonomorphic a) = SortArgumentMonomorphic $ f a
  fmap _ (SortArgumentPolymorphic x tps) = SortArgumentPolymorphic x tps
  fmap f (SortArgumentList args) = SortArgumentList $ fmap (fmap f) args

data SortArgumentRegion = SortArgumentRegion

instance Show Sort where
  show (SortForall tvar sort) = "forall " ++ show tvar ++ ". " ++ show sort
  show (SortFun sortArgs regionArgs s1) = "[" ++ show sortArgs ++ "; " ++ show regionArgs ++ "] -> " ++ show s1
  show SortRelation = "R"

instance Show SortArgumentRegion where
  show SortArgumentRegion = "Ρ"

instance Show a => Show (SortArgument a) where
  show (SortArgumentMonomorphic a) = show a
  show (SortArgumentPolymorphic tvar tps) = "<" ++ show tvar ++ (tps >>= (\tp -> " " ++ showType [] tp)) ++ ">"
  show (SortArgumentList args) = show args

  showList args = ('(' :) . (intercalate ", " (map show args) ++) . (')' :)

type SubstitutionFunctions a = [(TypeVar, [Type] -> SortArgument a)]

sortArgumentSubstitute :: SubstitutionFunctions a -> (a -> a) -> SortArgument a -> SortArgument a
sortArgumentSubstitute substitution mapValue (SortArgumentMonomorphic a) = SortArgumentMonomorphic $ mapValue a
sortArgumentSubstitute substitution mapValue sort@(SortArgumentPolymorphic tvar tps) = case lookup tvar substitution of
  Just fn -> fn tps
  Nothing -> sort
sortArgumentSubstitute substitution mapValue (SortArgumentList sorts) = SortArgumentList $ map (sortArgumentSubstitute substitution mapValue) sorts
