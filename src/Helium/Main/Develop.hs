module Helium.Main.Develop where

import System.Directory
import System.Process
import System.FilePath
import Data.IORef

import Control.Monad

import Helium.Main.Make
import Helium.Main.Args
import qualified Helium.CodeGeneration.Iridium.FileCache as Iridium


compileFile :: String -> IO ()
compileFile = compileFile' "../lib" "../develop"

compileFile' :: String -> String -> String -> IO ()
compileFile' preludePath developLocation s = do
    pwc <- getCurrentDirectory
    putStrLn pwc
    let file = developLocation ++ "/" ++ s
    let output = fst (splitExtension file)
    doneRef <- newIORef []
    let paths = [preludePath, developLocation]
    cache <- Iridium.newFileCache paths
    _ <- make developLocation file paths [] [Overloading, BuildAll, Verbose, VerifyBackend, Strictness 1] cache doneRef
    putStrLn "Compiled!"
    (code, res, err) <- readProcessWithExitCode output [] ""
    putStrLn("Exit code: " ++ show code)
    putStrLn "Program result:"
    putStrLn res
    unless (null err) $ do
        putStrLn "Program error"
        putStrLn err
