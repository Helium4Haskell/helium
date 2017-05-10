{-| Module      :  Main
    License     :  GPL

    Maintainer  :  helium@cs.uu.nl
    Stability   :  experimental
    Portability :  portable
    
    The only thing this program does is display the path information 
    on where to find the files associated with this version of Helium.
    This can be used by external tools, like Hint.
       
-}

module Main where

import Paths_helium

main :: IO ()
main = do
    bd <- getBinDir
    dd <- getDataDir
    
    putStrLn bd
    putStrLn dd
    return ()


