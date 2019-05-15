module Helium.CodeGeneration.Iridium.Region.Utils where

import System.IO
import Lvm.Common.Id
import Lvm.Core.Type

typeDependencies :: Bool -> Type -> [Id]
typeDependencies inFunctions tp = dependencies tp []
  where
    dependencies :: Type -> [Id] -> [Id]
    dependencies (TAp (TAp (TCon TConFun) t1) t2) accum
      | inFunctions = dependencies t1 $ dependencies t2 accum
      | otherwise = accum
    dependencies (TAp t1 t2) accum = dependencies t1 $ dependencies t2 accum
    dependencies (TForall _ _ t1) accum = dependencies t1 accum
    dependencies (TStrict t1) accum = dependencies t1 accum
    dependencies (TCon (TConDataType name)) accum = name : accum
    dependencies (TCon (TConTypeClassDictionary name)) accum = dictionaryDataTypeName name : accum
    dependencies _ accum = accum

debugLog :: Maybe Handle -> String -> IO ()
debugLog Nothing _ = return ()
debugLog (Just h) string = hPutStrLn h string
