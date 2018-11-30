module Helium.StaticAnalysis.Inferencers.OutsideInX.TopConversion(
        monoTypeToTp
    ,   monoTypeToTypeScheme
    ,   tpSchemeListDifference

) where

import Unbound.LocallyNameless hiding (Name)
import Cobalt.Core.Types
import Top.Types.Primitive
import Top.Types.Quantification
import Top.Types.Qualification
import Top.Types.Substitution
import Top.Types.Schemes
import Helium.Syntax.UHA_Syntax
import Helium.Syntax.UHA_Utils
import qualified Data.Map as M
import Data.Maybe 
import Debug.Trace

monoTypeToTypeScheme :: MonoType -> TpScheme
monoTypeToTypeScheme mtp = let
    tp = monoTypeToTp mtp 
    qualifiedType = [] .=>. tp
    quantifiedType = generalizeAll qualifiedType
    in quantifiedType
monoTypeToTp :: MonoType -> Tp
monoTypeToTp (MonoType_Var n) = TVar (fromInteger (name2Integer n))
monoTypeToTp (MonoType_Con n args) = foldr TApp (TCon n) (map monoTypeToTp args)
monoTypeToTp (MonoType_Arrow f a) = monoTypeToTp f .->. monoTypeToTp a

tpSchemeListDifference :: M.Map Name TpScheme -> M.Map Name TpScheme -> M.Map Name (Tp, Tp)
tpSchemeListDifference m1 m2 = M.map fromJust $ M.filter isJust $ M.intersectionWith eqTpScheme m1 m2



eqTpScheme :: TpScheme -> TpScheme -> Maybe (Tp, Tp)
eqTpScheme t1@(Quantification (is1, qmap1, tp1)) t2@(Quantification (is2, qmap2, tp2)) = let
    subs = M.fromList $ zipWith (\orig rep -> (orig, TVar rep)) is2 is1
    tp2r = subs |-> unqualify tp2
    tp1r = unqualify tp1
    in if tp1r == tp2r  then Nothing else Just (tp1r, tp2r)


