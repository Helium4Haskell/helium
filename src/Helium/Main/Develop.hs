module Helium.Main.Develop where

import System.Directory
import System.Process
import System.FilePath

import Control.Monad

import Helium.Main.Compile
import Helium.Main.Args

compileFile :: String -> IO ()
compileFile = compileFile' "../lib" "../develop"

compileFile' :: String -> String -> String -> IO ()
compileFile' preludePath developLocation s = do
    pwc <- getCurrentDirectory
    putStrLn pwc
    
    let file = developLocation ++ "/" ++ s
    let lvmFile = fst (splitExtension file) ++ ".lvm"
    compile developLocation file [Overloading] [preludePath, developLocation] []
    print $ "-P../lib:"++developLocation++":../test/make"
    (x, res, err) <- readProcessWithExitCode "lvmrun" ["-P../lib:"++developLocation, lvmFile] "abc\r\n"
    putStrLn("Exit code: " ++ show x)
    putStrLn "Program result:"
    putStrLn res
    unless (null err) $ do
        putStrLn "Program error"
        putStrLn err
