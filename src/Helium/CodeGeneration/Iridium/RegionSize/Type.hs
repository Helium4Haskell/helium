module Helium.CodeGeneration.Iridium.RegionSize.Type
    ( TypeAlg(..), idTypeAlg, foldTypeAlg, foldTypeAlgN
    ) where

import Lvm.Core.Type

  
----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

----------------------------------------------------------------
-- Type algebra
----------------------------------------------------------------

type Depth = Int
data TypeAlg a = TypeAlg {
    tAp     :: Depth -> a -> a -> a,
    tForall :: Depth -> Quantor -> Kind -> a -> a,
    tStrict :: Depth -> a -> a,
    tVar    :: Depth -> TypeVar -> a,
    tCon    :: Depth -> TypeConstant -> a
  }

idTypeAlg :: TypeAlg Type
idTypeAlg = TypeAlg {
    tAp     = \_ -> TAp    ,
    tForall = \_ -> TForall,
    tStrict = \_ -> TStrict,
    tVar    = \_ -> TVar   ,
    tCon    = \_ -> TCon   
}

foldTypeAlg ::  TypeAlg a -> Type -> a
foldTypeAlg = foldTypeAlgN 1

foldTypeAlgN :: Int -> TypeAlg a -> Type -> a
foldTypeAlgN n alg = go n
    where go d (TAp     t1 t2) =  tAp     alg d (go d t1) (go d t2)
          go d (TForall q k t) =  tForall alg d q k $ go (d + 1) t
          go d (TStrict t1   ) =  tStrict alg d (go d t1)
          go d (TVar    x    ) =  tVar    alg d x
          go d (TCon    tc   ) =  tCon    alg d tc

----------------------------------------------------------------
-- Type utilities
----------------------------------------------------------------
