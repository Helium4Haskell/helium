module PhaseKindInferencer (phaseKindInferencer) where

import Args
import CompileUtils
import KindInferencing as KI
import ImportEnvironment
import Data.FiniteMap
import Types

phaseKindInferencer :: ImportEnvironment -> Module -> [Option] -> IO ()
phaseKindInferencer importEnvironment module_ options = 
   do enterNewPhase "Kind inferencing" options
      let (debugIO, kindEnv, kindErrors, _) = KI.sem_Module module_ importEnvironment options 
      when (DumpTypeDebug `elem` options) $ 
         do debugIO  
            putStrLn . unlines . map (\(n,ks) -> show n++" :: "++showKindScheme ks) . fmToList $ kindEnv
      unless (null kindErrors) $
         showErrorsAndExit (reverse kindErrors) maximumNumberOfKindErrors options            

maximumNumberOfKindErrors :: Int
maximumNumberOfKindErrors = 1
