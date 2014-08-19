{-| Module      :  PhaseKindInferencer
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}

module Main.PhaseKindInferencer (phaseKindInferencer) where

import Main.CompileUtils
import StaticAnalysis.Inferencers.KindInferencing as KI
-- import ImportEnvironment
import qualified Data.Map as M
import Top.Types
import StaticAnalysis.Messages.KindErrors

phaseKindInferencer :: ImportEnvironment -> Module -> [Option] -> Phase KindError ()
phaseKindInferencer importEnvironment module_ options =
   do enterNewPhase "Kind inferencing" options
      let res = KI.wrap_Module (KI.sem_Module module_) (KI.Inh_Module {
                   KI.importEnvironment_Inh_Module = importEnvironment,
                   KI.options_Inh_Module = options })
      when (DumpTypeDebug `elem` options) $ 
         do KI.debugIO_Syn_Module res
            putStrLn . unlines . map (\(n,ks) -> show n++" :: "++showKindScheme ks) . M.assocs $ KI.kindEnvironment_Syn_Module res
      case KI.kindErrors_Syn_Module res of
      
         _:_ ->
            return (Left $ KI.kindErrors_Syn_Module res)
         [] ->
            return (Right ())