module Main where

import Directory
import Monad
import List
import IO

main = oneDir "."
    
oneDir :: String -> IO (Int, Int)
oneDir name = do
    files <- filesInDir "." 
    let haskellFiles = filter (\name -> ".hs" `isSuffixOf` name) files -- || ".ag" `isSuffixOf` name) files
    counts <- mapM wc haskellFiles
    dirs <- dirsInDir "."
    results <- mapM (\dir -> do
        setCurrentDirectory dir
        x <- oneDir (name ++ "/" ++ dir)
        setCurrentDirectory ".."
        return x) dirs
    let (nrFiless, countss) = unzip results
        totalFiles = length haskellFiles + sum nrFiless
        totalLines = sum counts + sum countss
    when (totalLines > 0) $
      putStrLn (take 50 (name ++ repeat ' ') ++ ": " ++ align 7 (show totalLines) ++
          " (in " ++ align 3 (show totalFiles) ++ " files)")
    return (length haskellFiles + sum nrFiless, sum counts + sum countss)

align x s = if length s >= x then s else replicate (x - length s) ' ' ++ s

wc :: String -> IO Int
wc fileName = do
    handle <- openFile fileName ReadMode
    firstLine <- hGetLine handle
    if "-- do not edit" `isPrefixOf` firstLine then
      return 0
     else do
        ls <- countLines handle
        hClose handle
        return (ls+1)

countLines :: Handle -> IO Int
countLines h = do
    hGetLine h
    i <- countLines h
    return (i + 1)
  `catch` (\_ -> return 0)
  
filesInDir :: String -> IO [String]
filesInDir path = do
    entries <- getDirectoryContents path
    filterM doesFileExist entries

dirsInDir :: String -> IO [String]
dirsInDir path = do
    entries <- getDirectoryContents path
    dirs <- filterM doesDirectoryExist entries
    return (filter ((/= '.') . head) dirs)