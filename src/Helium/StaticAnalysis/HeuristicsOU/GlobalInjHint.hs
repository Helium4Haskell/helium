{-# LANGUAGE FlexibleContexts #-}
module Helium.StaticAnalysis.HeuristicsOU.GlobalInjHint where

import Helium.StaticAnalysis.Inferencers.OutsideInX.Rhodium.RhodiumTypes (TyVar, Axiom, RType, Constraint)
import Helium.StaticAnalysis.Miscellaneous.Diagnostics (Diagnostics, Diagnostic)
import Helium.StaticAnalysis.Miscellaneous.ConstraintInfoOU (ConstraintInfo)
import Unbound.Generics.LocallyNameless (Fresh)
import Rhodium.TypeGraphs.GraphProperties (HasTypeGraph)
import Control.Monad (foldM)

buildGlobalInjHint :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic) 
                   => Diagnostics -> [TyVar] -> m (ConstraintInfo -> ConstraintInfo)
buildGlobalInjHint diags tvs = do
  hints <- mapM (buildGlobalInjHint' diags) tvs
  return $ foldl1 (.) hints
  where
    buildGlobalInjHint' :: (Fresh m, HasTypeGraph m (Axiom ConstraintInfo) TyVar (RType ConstraintInfo) (Constraint ConstraintInfo) ConstraintInfo Diagnostic) 
                       => Diagnostics -> TyVar -> m (ConstraintInfo -> ConstraintInfo)
    buildGlobalInjHint' diags tv = undefined