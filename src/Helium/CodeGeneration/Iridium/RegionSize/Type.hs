module Helium.CodeGeneration.Iridium.RegionSize.Type
    (showTypeN, 
    TypeAlg(..), idTypeAlg, foldTypeAlg, foldTypeAlgN,
    typeReIndex, typeInsantiate
    ) where

import Helium.CodeGeneration.Iridium.RegionSize.Utils

import Lvm.Core.Type hiding (showType)


  
----------------------------------------------------------------
-- Pretty printing
----------------------------------------------------------------

showTypeN :: Depth -> Type -> String
showTypeN n = foldTypeAlgN n showAlg
    where showAlg = TypeAlg {
        tAp     = \_ t1 t2 -> t1 ++ " " ++ t2,
        tForall = \d _ _ t -> "∀" ++ typeVarName d ++". " ++ t,
        tStrict = \_ t     -> "!" ++ t,
        tVar    = \d idx   -> typeVarName $ d - idx - 1,
        tCon    = \_ tc    -> show tc
    }

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
foldTypeAlg = foldTypeAlgN 0

foldTypeAlgN :: Int -> TypeAlg a -> Type -> a
foldTypeAlgN n alg = go n
    where go d (TAp     t1 t2) =  tAp     alg d (go d t1) (go d t2)
          go d (TForall q k t) =  tForall alg d q k $ go (d + 1) t
          go d (TStrict t1   ) =  tStrict alg d (go d t1)
          go d (TVar    x    ) =  tVar    alg d x
          go d (TCon    tc   ) =  tCon    alg d tc

----------------------------------------------------------------
-- De Bruijn reindexing
----------------------------------------------------------------

-- TODO: Check if we can use Ivos implementation of typeReindex
-- | Re-index the debruin indices of a sort
typeReIndex :: (Depth -> Int -> Int) -- ^ Reindex function
            -> Depth -> Type -> Type
typeReIndex f n = foldTypeAlgN n reIdxAlg
    where reIdxAlg = idTypeAlg {
        tVar = \d idx -> TVar $ f d idx
    }

----------------------------------------------------------------
-- Type substitution
----------------------------------------------------------------

-- | Instantiate a type within a type
typeInsantiate :: Depth -- ^ Depth in sort 
               -> Type -> Type -> Type
typeInsantiate subD subT = foldTypeAlgN subD instAlg
  where instAlg = idTypeAlg {
    tVar = \d idx -> if d == idx
                     then typeWeaken d subT
                     else TVar idx
  }
