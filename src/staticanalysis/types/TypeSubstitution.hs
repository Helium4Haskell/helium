-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- TypeSubstitution.hs : A class and some instances for substitutions and 
--    substitutables on types.
--
-------------------------------------------------------------------------------

module TypeSubstitution where

import Array
import List                 ( (\\), union )
import TypeRepresentation
import FiniteMap
import Utils                ( internalError )

----------------------------------------------------------------------
-- Substitutions and substitutables

class Substitution s where
   lookupInt   :: Int -> s -> Maybe Tp   -- lookup Int in substitution   
   removeDom   :: [Int] -> s -> s        -- remove from the domain of the substitution
   restrictDom :: [Int] -> s -> s        -- restrict the domain of the substitution
   dom         :: s -> [Int]             -- domain of substitution
   cod         :: s -> Tps               -- co-domain of substitution
   
class Substitutable a where 
   (|->) :: Substitution s => s -> a -> a    -- apply substitution
   ftv    :: a -> [Int]                      -- free type variables   
   
   sub |-> a = a        -- default definition (do nothing)
   ftv a     = []       -- default definition (do nothing)

----------------------------------------------------------------------
-- Substitution instances 

type FiniteMapSubstitution = FiniteMap Int Tp

instance Substitution FiniteMapSubstitution where

   lookupInt      = flip lookupFM 
   removeDom      = flip delListFromFM
   restrictDom is = filterFM (\i _ -> i `elem` is)
   
   dom = keysFM
   cod = eltsFM 

emptySubst :: FiniteMapSubstitution
emptySubst = emptyFM

-- compose two substitutions: safe
-- Note for `plusFM`: Bindings in right argument shadow those in the left
(@@) :: FiniteMapSubstitution -> FiniteMapSubstitution -> FiniteMapSubstitution
fm1 @@ fm2 = fm1 `plusFM` mapFM (\_ t -> fm1 |-> t) fm2  

-- compose two substitutions: quick and dirty!
(@@@) :: FiniteMapSubstitution -> FiniteMapSubstitution -> FiniteMapSubstitution
(@@@) = plusFM 

singleSubstitution :: Int -> Tp -> FiniteMapSubstitution
singleSubstitution = unitFM

listToSubstitution :: [(Int,Tp)] -> FiniteMapSubstitution
listToSubstitution = listToFM

-- An array as a substitution

instance Substitution (Array Int (Maybe Tp)) where

   lookupInt   i  array = Just $ maybe (TVar i) (array |->) (array ! i)
   removeDom   is array = array // zip is (repeat Nothing)
   restrictDom is array = let is' = filter (`notElem` is) (dom array)
                          in array // zip is' (repeat Nothing)
   
   dom array = let p i = maybe False (const True) (array!i)
               in filter p (indices array)
   cod = let op mtp xs = maybe xs (:xs) mtp 
         in foldr op [] . elems

-- Either of two substitutions

type Subst = Either (Array Int (Maybe Tp)) BinTreeSubst

instance (Substitution a,Substitution b) => Substitution (Either a b) where 
   lookupInt   i  = either (lookupInt i) (lookupInt i)
   removeDom   is = either (Left . removeDom   is) (Right . removeDom   is)
   restrictDom is = either (Left . restrictDom is) (Right . restrictDom is)
   dom            = either dom dom 
   cod            = either cod cod

-- A binary tree as a substitution

data BinTreeSubst = BinTreeSubstSplit Int BinTreeSubst BinTreeSubst 
                  | BinTreeSubstNode Tp
                  | BinTreeSubstEmpty

instance Substitution BinTreeSubst where 
   lookupInt i bintree = case bintree of 
                           BinTreeSubstSplit j l r 
                               | i <= j    -> lookupInt i l
                               | otherwise -> lookupInt i r
                           BinTreeSubstNode tp     -> Just tp 
                           BinTreeSubstEmpty       -> Nothing
   removeDom   is = internalError "SATypes.hs" "BinTreeSubst" "removeDom: substitution is static" 
   restrictDom is = internalError "SATypes.hs" "BinTreeSubst" "restrictDom: substitution is static" 
   dom            = internalError "SATypes.hs" "BinTreeSubst" "dom: substitution is static" 
   cod            = internalError "SATypes.hs" "BinTreeSubst" "cod: substitution is static" 

----------------------------------------------------------------------
-- Substitutables instances
   
instance Substitutable Tp where   
   sub |-> tp = case tp of 
                   TVar i     -> maybe tp id (lookupInt i sub)
                   TCon s     -> tp
                   TApp t1 t2 -> TApp (sub |-> t1) (sub |-> t2) 
   ftv tp = case tp of      
               TVar i     -> [i]
               TCon s     -> []
               TApp t1 t2 -> ftv t1 `union` ftv t2   
    
instance Substitutable TpScheme where    
   sub |-> (Scheme monos nm tp) = Scheme monos nm (removeDom monos sub |-> tp)
   ftv     (Scheme monos nm tp) = ftv tp \\ monos

instance Substitutable a => Substitutable [a] where
   sub |-> as  = map (sub |->) as
   ftv         = foldr union [] . map ftv   

instance Substitutable a => Substitutable (Maybe a) where
   sub |-> ma = maybe Nothing (Just . (sub |->)) ma
   ftv     ma = maybe [] ftv ma

instance (Substitutable a, Substitutable b) => Substitutable (a,b) where
   sub |-> (a,b) = (sub |-> a, sub |-> b)
   ftv     (a,b) = ftv a `union` ftv b
