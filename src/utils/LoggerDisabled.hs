module Logger ( logger ) where

{-# NOTINLINE logger #-}

logger :: String -> Maybe ([String],String) -> Bool -> IO ()
logger _ _ _ = return ()
  

