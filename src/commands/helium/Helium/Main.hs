{-| Module      :  Main
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}
module Main where

import Helium.Main.Make(make)
import Helium.Parser.Parser(parseOnlyImports)
import qualified Helium.CodeGeneration.Iridium.FileCache as Iridium
import Control.Monad
import System.FilePath(joinPath)
import Data.List(nub)
import Lvm.Path(explodePath,getLvmPath)
import System.Directory(doesFileExist)
import Helium.Main.Args
import Helium.Main.Make
import Helium.Main.CompileUtils
import Data.IORef
import Paths_helium(getDataDir)

-- Prelude will be treated specially
prelude :: String
prelude = "Prelude.hs"

-- Order matters
coreLibs :: [String]
coreLibs = ["LvmLang", "LvmIO", "LvmException", "HeliumLang", "PreludePrim"]

main :: IO ()
main = do
    args                     <- getArgs
    (options, Just fullName) <- processHeliumArgs args -- Can't fail, because processHeliumArgs checks it.

    lvmPathFromOptionsOrEnv <- case lvmPathFromOptions options of
        Nothing -> getLvmPath
        Just s  -> return (explodePath s)

    dataDir <- getDataDir 
    
    baseLibs <- case basePathFromOptions options of
        Nothing -> if overloadingFromOptions options
                   then return $ joinPath [dataDir, "lib"]
                   else return $ joinPath [dataDir, "lib", "simple"]
        Just path -> if overloadingFromOptions options
                     then return path
                     else return $ joinPath [path,"simple"] -- The lib will be part of path already.

    let (filePath, moduleName, _) = splitFilePath fullName
        filePath' = if null filePath then "." else filePath
        lvmPath   = filter (not.null) . nub
                  $ (filePath' : lvmPathFromOptionsOrEnv) ++ [baseLibs] -- baseLibs always last

    cache <- Iridium.newFileCache lvmPath

    -- File that is compiled must exist, this test doesn't use the search path
    fileExists <- doesFileExist fullName
    newFullName <-
        if fileExists then
            return fullName
        else do
            let filePlusHS = fullName ++ ".hs"
            filePlusHSExists <- doesFileExist filePlusHS
            unless filePlusHSExists $ do
                putStrLn $ "Can't find file " ++ show fullName ++ " or " ++ show filePlusHS
                exitWith (ExitFailure 1)
            return filePlusHS

    doneRef <- newIORef []
    _ <- make filePath' newFullName lvmPath [moduleName] options cache doneRef
    return ()
