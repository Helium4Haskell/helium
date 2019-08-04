module Helium.CodeGeneration.Iridium.Region.Sort
  ( TypeVar(..), showSubscript, RegionDirection(..)
  , Sort(..), Argument(..), argumentEmpty, SortArgumentRegion(..), sortIncreaseScope
  , variableIncrementLambdaBound, argumentFlatten
  , IndexVariable(..), indexBoundLambda, indexInArgument, showIndexVariable, variableFromIndices
  , Tp(..), tpFromType, tpStrict, tpNotStrict, tpIsStrict
  , tpIncreaseScope, tpInstantiate, tpInstantiate', TypeInstantiation(..), typeInstantiationTry, typeInstantiationIncrement
  , regionIncreaseScope
  ) where

import Lvm.Core.Type
import qualified Data.IntMap as IntMap
import Data.Bits
import Data.List

import Helium.CodeGeneration.Iridium.Region.Utils

newtype TypeVar = TypeVar Int
  deriving (Eq, Ord)

data RegionDirection
  -- Argument may only be used on the right hand side of the >=,
  -- eg it may only be used to increase the life times of other regions.
  = RegionDirectionOutlives
  -- Argument may be used on both sides of >=.
  | RegionDirectionAny
  deriving (Eq, Ord)

instance Show RegionDirection where
  show RegionDirectionOutlives = "↓"
  show RegionDirectionAny = ""

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
tpFromType quantors (TAp t1 t2) = tpFromType quantors t1 `TpApp` tpNotStrict (tpFromType quantors t2)
tpFromType quantors (TForall (Quantor idx _) _ tp) = TpForall $ tpFromType (idx : quantors) tp
tpFromType quantors (TStrict tp) = TpStrict $ tpFromType quantors tp
tpFromType quantors (TVar var) = case elemIndex var quantors of
  Nothing -> error "tpFromType: Type variable not found"
  Just idx -> TpVar $ TypeVar $ idx
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

-- Instantiation of a sort / annotation / argument / type
-- Int represents the number of foralls that we found during the traversal of the AST
data TypeInstantiation = TypeInstantiation !Int !Tp

typeInstantiationTry :: TypeInstantiation -> TypeVar -> Either TypeVar Tp
typeInstantiationTry (TypeInstantiation foralls tp) (TypeVar index)
  | foralls == index = Right $ tpIncreaseScope foralls 0 tp
  | index < foralls = Left $ TypeVar index
  | otherwise = Left $ TypeVar $ index - 1

typeInstantiationIncrement :: TypeInstantiation -> TypeInstantiation
typeInstantiationIncrement (TypeInstantiation foralls tp) = TypeInstantiation (foralls + 1) tp

tpInstantiate :: Tp -> Tp -> Tp
tpInstantiate = tpInstantiate' . TypeInstantiation 0

tpInstantiate' :: TypeInstantiation -> Tp -> Tp
tpInstantiate' inst (TpVar tvar) = case typeInstantiationTry inst tvar of
  Left tvar' -> TpVar tvar'
  Right tp -> tp
tpInstantiate' inst (TpApp t1 t2) = tpInstantiate' inst t1 `TpApp` tpInstantiate' inst t2
tpInstantiate' inst (TpForall tp) = TpForall $ tpInstantiate' (typeInstantiationIncrement inst) tp
tpInstantiate' inst (TpStrict tp) = TpStrict $ tpInstantiate' inst tp
tpInstantiate' _ t = t

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
        char = numbersSubscript !!! digit
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
  | SortFun !(Argument Sort) !(Argument SortArgumentRegion) !RegionDirection !Sort
  | SortRelation
  | SortPolymorphic !TypeVar ![Tp]
  deriving (Eq, Ord)

data Argument a
  = ArgumentValue !a
  | ArgumentList ![Argument a]
  deriving (Eq, Ord)

argumentFlatten :: Argument a -> [a]
argumentFlatten (ArgumentValue a) = [a]
argumentFlatten (ArgumentList args) = args >>= argumentFlatten

instance (Show a) => Show (Argument a) where
  show (ArgumentValue r1) = show r1
  show (ArgumentList args) = show args

  showList args = ("( " ++) . (intercalate ", " (map show args) ++) . (" )" ++)

instance Functor Argument where
  fmap f (ArgumentValue a) = ArgumentValue $ f a
  fmap f (ArgumentList args) = ArgumentList $ fmap (fmap f) args

instance Applicative Argument where
  pure = ArgumentValue
  ArgumentValue f <*> b = fmap f b
  ArgumentList as <*> b = ArgumentList $ map (<*> b) as

instance Monad Argument where
  return = ArgumentValue
  ArgumentValue a >>= f = f a
  ArgumentList as >>= f = ArgumentList $ map (>>= f) as

instance Foldable Argument where
  foldMap f (ArgumentValue a) = f a
  foldMap f (ArgumentList as) = foldMap (foldMap f) as

instance Traversable Argument where
  sequenceA (ArgumentValue a) = ArgumentValue <$> a
  sequenceA (ArgumentList as) = ArgumentList <$> traverse sequenceA as

argumentEmpty :: Argument a
argumentEmpty = ArgumentList []

data SortArgumentRegion = SortArgumentRegionMonomorphic | SortArgumentRegionPolymorphic !TypeVar ![Tp]
  deriving (Eq, Ord)

sortIncreaseScope :: Int -> Int -> Sort -> Sort
sortIncreaseScope 0 = const id
sortIncreaseScope inc = increment
  where
    increment minScope (SortForall sort) = SortForall $ increment (minScope + 1) sort
    increment minScope (SortFun argAnnotation argRegion dir a) =
      SortFun
        (increment minScope <$> argAnnotation)
        (regionIncreaseScope inc minScope <$> argRegion)
        dir
        $ increment minScope a
    increment minScope SortRelation = SortRelation
    increment minScope (SortPolymorphic (TypeVar idx) tps) =
      SortPolymorphic tvar $ map (tpIncreaseScope inc minScope) tps
      where
        tvar
          | idx < minScope = TypeVar idx
          | otherwise = TypeVar (idx + inc)

regionIncreaseScope :: Int -> Int -> SortArgumentRegion -> SortArgumentRegion
regionIncreaseScope inc minScope SortArgumentRegionMonomorphic = SortArgumentRegionMonomorphic
regionIncreaseScope inc minScope (SortArgumentRegionPolymorphic (TypeVar idx) tps) =
  SortArgumentRegionPolymorphic tvar $ map (tpIncreaseScope inc minScope) tps
  where
    tvar
      | idx < minScope = TypeVar idx
      | otherwise = TypeVar (idx + inc)

instance Show Sort where
  show (SortForall sort) = "∀ " ++ show sort
  show (SortFun sortArgs regionArgs dir s1) = "[" ++ show sortArgs ++ "; " ++ show regionArgs ++ "]" ++ show dir ++ " -> " ++ show s1
  show SortRelation = "R"
  show (SortPolymorphic tvar tps) = "Ψ⟨" ++ show tvar ++ (tps >>= (\tp -> " " ++ showTpAtom tp)) ++ "⟩"

instance Show SortArgumentRegion where
  show SortArgumentRegionMonomorphic = "Ρ"
  show (SortArgumentRegionPolymorphic tvar tps) = "Ρ⟨" ++ show tvar ++ (tps >>= (\tp -> " " ++ showTpAtom tp)) ++ "⟩"
