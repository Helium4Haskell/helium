module Helium.CodeGeneration.Iridium.Region.Sort
  ( TypeVar(..), showSubscript
  , Sort(..), SortArgument(..), sortArgumentEmpty, SortArgumentRegion(..)
  , sortArgumentSubstitute, variableIncrementLambdaBound
  , IndexVariable(..), indexBoundLambda, indexInArgument, showIndexVariable, variableFromIndices
  , TypeSubstitution(..)
  , Tp(..), tpFromType, tpSubstitute, tpStrict, tpNotStrict, tpIsStrict
  ) where

import Lvm.Core.Type
import qualified Data.IntMap as IntMap
import Data.Bits
import Data.List

import Helium.CodeGeneration.Iridium.Region.Utils

newtype TypeVar = TypeVar Int
  deriving (Eq, Ord)

data Tp
  = TpVar !TypeVar
  | TpCon !TypeConstant
  | TpApp !Tp !Tp
  | TpForall !Tp
  | TpStrict !Tp
  deriving (Eq, Ord)

instance Show Tp where
  show (TpForall tp) = "∀ " ++ show tp
  show (TpApp (TpApp (TpCon TConFun) tArg) tRet) = showTpApp tArg ++ " -> " ++ show tRet
  show tp = showTpApp tp

showTpAtom :: Tp -> String
showTpAtom (TpVar var) = show var
showTpAtom (TpCon con) = show con
showTpAtom (TpStrict tp) = '!' : showTpAtom tp
showTpAtom tp = "(" ++ show tp ++ ")"

showTpApp :: Tp -> String
showTpApp (TpApp t1 t2) = showTpApp t1 ++ " " ++ showTpAtom t2
showTpApp tp = showTpAtom tp

tpFromType :: [Int] -> Type -> Tp
tpFromType quantors (TAp t1 t2) = tpFromType quantors t1 `TpApp` tpFromType quantors t2
tpFromType quantors (TForall (Quantor idx _) _ tp) = TpForall $ tpFromType (idx : quantors) tp
tpFromType quantors (TStrict tp) = TpStrict $ tpFromType quantors tp
tpFromType quantors (TVar var) = case elemIndex var quantors of
  Nothing -> error "tpFromType: Type variable not found"
  Just idx -> TpVar $ TypeVar $ idx + 1
tpFromType quantors (TCon tcon) = TpCon tcon

tpStrict :: Tp -> Tp
tpStrict (TpForall tp) = TpForall $ tpStrict tp
tpStrict (TpStrict tp) = TpStrict tp
tpStrict tp = TpStrict tp

tpNotStrict :: Tp -> Tp
tpNotStrict (TpForall tp) = TpForall $ tpNotStrict tp
tpNotStrict (TpStrict tp) = tp
tpNotStrict tp = tp

tpIsStrict :: Tp -> Bool
tpIsStrict (TpForall tp) = tpIsStrict tp
tpIsStrict (TpStrict _) = True
tpIsStrict _ = False

tpIncreaseScope :: Int -> Int -> Tp -> Tp
tpIncreaseScope 0 = const id
tpIncreaseScope inc = increment
  where
    increment minScope (TpVar (TypeVar idx))
      | idx >= minScope = TpVar (TypeVar (idx + inc))
    increment minScope (TpApp t1 t2) = TpApp (increment minScope t1) (increment minScope t2)
    increment minScope (TpForall tp) = TpForall $ increment (minScope + 1) tp
    increment minScope (TpStrict tp) = TpStrict $ increment minScope tp
    increment _ tp = tp

tpSubstitute :: Int -> Tp -> Tp -> Tp
tpSubstitute index substitution = substitute 0
  where
    substitute nesting (TpVar (TypeVar tvar))
      | tvar == index + nesting = tpIncreaseScope nesting 1 substitution
    substitute nesting (TpApp t1 t2) = substitute nesting t1 `TpApp` substitute nesting t2
    substitute nesting (TpForall tp) = TpForall $ substitute (nesting + 1) tp
    substitute nesting (TpStrict tp) = TpStrict $ substitute nesting tp
    substitute _ t = t

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

class IndexVariable a where
  variableToInt :: a -> Int
  variableFromInt :: Int -> a

indexBoundLambda :: IndexVariable a => a -> Int
indexBoundLambda x = variableToInt x `shiftR` 32

indexInArgument :: IndexVariable a => a -> Int
indexInArgument x = variableToInt x .&. 0xFFFFFFFF

variableFromIndices :: IndexVariable a => Int -> Int -> a
variableFromIndices boundLambda arg = variableFromInt $ (boundLambda `shiftL` 32) .|. arg

showIndexVariable :: IndexVariable a => a -> String
showIndexVariable var = showSubscript (indexBoundLambda var) ++ "₋" ++ showSubscript (indexInArgument var)

variableIncrementLambdaBound :: IndexVariable a => Int -> Int -> a -> a
variableIncrementLambdaBound minimumLambda inc var
  | lam < minimumLambda = var
  | otherwise = variableFromIndices (lam + inc) idx
  where
    lam = indexBoundLambda var
    idx = indexInArgument var

instance Show TypeVar where
  show (TypeVar idx) = 'α' : showSubscript idx

data Sort
  = SortForall !Sort
  | SortFun !(SortArgument Sort) !(SortArgument SortArgumentRegion) !Sort
  | SortRelation
  deriving (Eq, Ord)

data SortArgument a
  = SortArgumentMonomorphic !a
  | SortArgumentPolymorphic !TypeVar ![Tp]
  | SortArgumentList ![SortArgument a]
  deriving (Eq, Ord)

sortArgumentEmpty :: SortArgument a
sortArgumentEmpty = SortArgumentList []

instance Functor SortArgument where
  fmap f (SortArgumentMonomorphic a) = SortArgumentMonomorphic $ f a
  fmap _ (SortArgumentPolymorphic x tps) = SortArgumentPolymorphic x tps
  fmap f (SortArgumentList args) = SortArgumentList $ fmap (fmap f) args

data SortArgumentRegion = SortArgumentRegion
  deriving (Eq, Ord)

sortIncreaseScope :: Int -> Int -> Sort -> Sort
sortIncreaseScope 0 = const id
sortIncreaseScope inc = increment
  where
    increment minScope (SortForall sort) = SortForall $ increment (minScope + 1) sort
    increment minScope (SortFun argAnnotation argRegion a) =
      SortFun
        (sortArgumentIncreaseScope inc minScope (increment minScope) argAnnotation)
        (sortArgumentIncreaseScope inc minScope id argRegion)
        $ increment minScope a
    increment minScope SortRelation = SortRelation

sortArgumentIncreaseScope :: Int -> Int -> (a -> a) -> SortArgument a -> SortArgument a
sortArgumentIncreaseScope inc minScope f (SortArgumentMonomorphic a) = SortArgumentMonomorphic $ f a
sortArgumentIncreaseScope inc minScope f (SortArgumentPolymorphic (TypeVar idx) tps) =
  SortArgumentPolymorphic tvar $ map (tpIncreaseScope inc minScope) tps
  where
    tvar
      | idx < minScope = TypeVar idx
      | otherwise = TypeVar (idx + minScope)
sortArgumentIncreaseScope inc minScope f (SortArgumentList as) =
  SortArgumentList $ map (sortArgumentIncreaseScope inc minScope f) as

instance Show Sort where
  show (SortForall sort) = "forall " ++ show sort
  show (SortFun sortArgs regionArgs s1) = "[" ++ show sortArgs ++ "; " ++ show regionArgs ++ "] -> " ++ show s1
  show SortRelation = "R"

instance Show SortArgumentRegion where
  show SortArgumentRegion = "Ρ"

instance Show a => Show (SortArgument a) where
  show (SortArgumentMonomorphic a) = show a
  show (SortArgumentPolymorphic tvar tps) = "<" ++ show tvar ++ (tps >>= (\tp -> " " ++ show tp)) ++ ">"
  show (SortArgumentList args) = show args

  showList args = ('(' :) . (intercalate ", " (map show args) ++) . (')' :)

data TypeSubstitution = TypeSubstitution !Int ![Tp]

sortArgumentSubstitute :: TypeSubstitution -> (Tp -> [Tp] -> SortArgument a) -> (a -> a) -> SortArgument a -> SortArgument a
sortArgumentSubstitute substitution f mapValue (SortArgumentMonomorphic a) = SortArgumentMonomorphic $ mapValue a
sortArgumentSubstitute (TypeSubstitution first substitution) f mapValue sort@(SortArgumentPolymorphic (TypeVar tvar) tps)
  | tvar >= first = case tryIndex substitution (tvar - first) of
    Nothing -> sort
    Just tp -> f tp tps
  | otherwise = sort
sortArgumentSubstitute substitution f mapValue (SortArgumentList sorts) = SortArgumentList $ map (sortArgumentSubstitute substitution f mapValue) sorts
