{-| Module      :  PhaseResolveOperators
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module PhaseResolveOperators(phaseResolveOperators) where

import CompileUtils
import ResolveOperators(resolveOperators, operatorsFromModule)
import qualified UHA_Pretty as PP(sem_Module)
import Data.FiniteMap

phaseResolveOperators :: String -> [String] -> Module -> [ImportEnvironment] -> 
                            [Option] -> IO Module
phaseResolveOperators fullName doneModules moduleBeforeResolve importEnvs options = do
    enterNewPhase "Resolving operators" options

    let importOperatorTable = 
            foldr1 plusFM ( operatorsFromModule moduleBeforeResolve
                          : map operatorTable importEnvs
                          )
        (module_, resolveErrors) = 
                  resolveOperators importOperatorTable moduleBeforeResolve

    when (not (null resolveErrors)) $ do
        unless (NoLogging `elem` options) $ 
            sendLog "R" fullName doneModules options
        showErrorsAndExit resolveErrors 20 options

    when (DumpUHA `elem` options) $
        putStrLn $ show $ PP.sem_Module module_
    
    return module_

