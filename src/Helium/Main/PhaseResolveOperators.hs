{-| Module      :  PhaseResolveOperators
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Helium.Main.PhaseResolveOperators(phaseResolveOperators) where

import Helium.Main.CompileUtils
import Helium.Parser.ResolveOperators(resolveOperators, operatorsFromModule, ResolveError)
import qualified Helium.Syntax.UHA_Pretty as PP(sem_Module,wrap_Module,Inh_Module(..),text_Syn_Module)
import qualified Data.Map as M

phaseResolveOperators :: 
   Module -> [ImportEnvironment] -> [Option] -> 
   Phase ResolveError Module

phaseResolveOperators moduleBeforeResolve importEnvs options = do
    enterNewPhase "Resolving operators" options

    let importOperatorTable = 
            M.unions (operatorsFromModule moduleBeforeResolve : map operatorTable importEnvs)
                          
        (module_, resolveErrors) = 
                  resolveOperators importOperatorTable moduleBeforeResolve

    case resolveErrors of
       
       _:_ ->
          return (Left resolveErrors)
          
       [] ->
          do when (DumpUHA `elem` options) $
                print $ PP.text_Syn_Module $ PP.wrap_Module (PP.sem_Module module_) PP.Inh_Module
    
             return (Right module_)

    

