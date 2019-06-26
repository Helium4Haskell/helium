module Helium.CodeGeneration.Iridium.Region.Utils where

import System.IO
import Lvm.Common.Id
import Lvm.Core.Type
import Data.IntMap (IntMap)
import qualified Data.IntMap.Strict as IntMap

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

tryIndex :: [a] -> Int -> Maybe a
tryIndex [] _ = Nothing
tryIndex (a:_) 0 = Just a
tryIndex (_:as) n = tryIndex as (n - 1)

(!!!) :: Show a => [a] -> Int -> a
(!!!) as idx = case tryIndex as idx of
  Just a -> a
  Nothing -> error $ "index: cannot find index " ++ show idx ++ " in " ++ show as

showIntMap :: Show a => IntMap a -> String
showIntMap m = IntMap.toList m >>= showElem
  where
    showElem (key, value) = "\n" ++ show key ++ " = " ++ show value
