--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$

module Helium.Lvm.Path 
   ( searchPath, searchPathMaybe, 
     explodePath, slashify, splitFilePath, getLvmPath
   ) where

import qualified Control.Exception as CE (catch, IOException)
import Data.List
import System.FilePath
import System.Directory
import System.Environment
import System.Exit

slash :: Char
slash =  pathSeparator

{-# DEPRECATED slashify "Please use the System.FilePath.</> operator instead of the partially defined, ill-named slashify function." #-}
slashify :: String -> String
slashify xs = if last xs == slash then xs else xs ++ [slash]

-- Split file name
-- e.g. /docs/haskell/Hello.hs =>
--   directory = /docs/haskell  baseName = Hello  ext = hs
splitFilePath :: String -> (String, String, String)
splitFilePath filePath = let (dir, fullName) = splitFileName filePath
                             (baseName, ext) = splitExtension fullName
                         in (dir, baseName, ext)

----------------------------------------------------------------
-- file searching
----------------------------------------------------------------

searchPath :: [String] -> String -> String -> IO String
searchPath path ext name = do
   ms <- searchPathMaybe path ext name
   case ms of 
      Just s  -> return s
      Nothing -> do 
         putStrLn ("Error: could not find " ++ show nameext)
         putStrLn ("   with search path " ++ show path)
         exitFailure
  where
    nameext
      | ext `isSuffixOf` name = name
      | otherwise             = name ++ ext
        
searchPathMaybe :: [String] -> String -> String -> IO (Maybe String)
searchPathMaybe  path ext name
  = walk (map makeFName path) -- was ("":path), but we don't want to look in the current directory by default
  where
    walk []         = return Nothing
    walk (fname:xs) = do{ exist <- doesFileExist fname
                        ; if exist
                           then return (Just fname)
                           else walk xs
                        }

    makeFName dir = dir </> nameext

    nameext
      | ext `isSuffixOf` name = name
      | otherwise             = name ++ ext

      
getLvmPath :: IO [String]
getLvmPath
  = do{ xs <- getEnv "LVMPATH"
      ; return (explodePath xs)
      }
  `CE.catch` handler
  where
    handler :: CE.IOException -> IO [String] 
    handler _ = return []

explodePath :: String -> [String]
explodePath = walk [] ""
  where
    walk ps p xs
      = case xs of
          []             -> if null p
                             then reverse ps
                             else reverse (reverse p:ps)
          (';':cs)       -> walk (reverse p:ps) "" cs
          (':':'\\':cs)  -> walk ps ("\\:" ++ p) cs
          (':':cs)       -> walk (reverse p:ps) "" cs
          (c:cs)         -> walk ps (c:p) cs
