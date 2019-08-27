{-| Module      :  Main
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
-}
module Main where

import Control.Monad
import System.FilePath(joinPath)
import Data.List(nub)
import Lvm.Path(explodePath,getLvmPath)
import System.Directory(doesFileExist)
import Helium.Main.Args
import Helium.Main.Make
import Helium.Main.CompileUtils
import Data.IORef
import Paths_helium

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

    baseLibs <- case basePathFromOptions options of
        Nothing -> getDataFileName $
                     if overloadingFromOptions options
                     then "lib"
                     else joinPath ["lib","simple"]
        Just path -> if overloadingFromOptions options
                     then return path
                     else return $ joinPath [path,"simple"] -- The lib will be part of path already.

    let (filePath, moduleName, _) = splitFilePath fullName
        filePath' = if null filePath then "." else filePath
        lvmPath   = filter (not.null) . nub
                  $ (filePath' : lvmPathFromOptionsOrEnv) ++ [baseLibs] -- baseLibs always last

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

    -- Ensure .core libs are compiled to .lvm
    mapM_ (makeCoreLib baseLibs) coreLibs

    -- And now deal with Prelude
    preludeRef <- newIORef []
    let preludeFullname = joinPath [baseLibs,prelude]
    preludeDone <- make filePath' preludeFullname lvmPath [prelude] options preludeRef

    doneRef <- newIORef [(preludeFullname, preludeDone)]
    _ <- make filePath' newFullName lvmPath [moduleName] options doneRef
    return ()