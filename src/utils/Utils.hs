{---

Utils: 
    Some Prelude-like functions
    
Changes:

DATE        CHANGE
05-05-2001  Cleanup
06-05-2001  Added "import Char" for GHC
16-05-2001  groupAllBy doesn't need Eq instance for a
-}

module Utils where

import List hiding (intersectBy)
import System
import Char -- GHC
import IdMap
import IOExts
import Logger
import ST

-------------------------------------------------------
-- String utils
-------------------------------------------------------
ltrim :: String -> String
ltrim (' ':xs) = ltrim xs
ltrim xs       = xs

rtrim :: String -> String
rtrim = reverse . ltrim . reverse

trim :: String -> String
trim = ltrim . rtrim

commaList :: [String] -> String
commaList [] = ""
commaList [x] = x
commaList (x:xs) = x ++ ", " ++ commaList xs

-------------------------------------------------------
-- From SAUtils
-------------------------------------------------------
                
mapFst :: (a -> b) -> [(a, c)] -> [(b, c)]
mapFst f xs = [ (f a, c) | (a, c) <- xs ]

mapSnd :: (c -> b) -> [(a, c)] -> [(a, b)]
mapSnd f xs = [ (a, f c) | (a, c) <- xs ]

fst3 (a,_,_)   = a
snd3 (_,a,_)   = a
thd3 (_,_,a)   = a

fst4 (a,_,_,_) = a
snd4 (_,a,_,_) = a
thd4 (_,_,a,_) = a
fth4 (_,_,_,a) = a

-------------------------------------------------------
-- Debugging tools
-------------------------------------------------------
traceList :: Show a => [a] -> b -> b
traceList l s = trace (show (Table l)) s

traceShowList :: Show a => [a] -> [a]
traceShowList l = trace (show (Table l)) l

data Table a = Table [a]

fromTable :: Table a -> [a]
fromTable (Table a) = a

instance Show a => Show (Table a) where
    show (Table (x:xs)) =
        let show' (x:xs) = "\n, " ++ show x ++ show' xs
            show' []     = ""
        in
            "[ " ++ show x ++ show' xs ++ "\n]\n"
    show (Table []) =
        "[\n]\n"

-------------------------------------------------------

intersectBy :: (a -> b -> Bool) -> [a] -> [b] -> [a]
intersectBy eq xs ys = [x | x <- xs, any (eq x) ys]

throw :: String -> IO a
throw = ioError . userError

groupAll :: Ord a => [a] -> [[a]]
groupAll = group.sort

groupAllBy :: Ord a => (a -> a -> Bool) -> [a] -> [[a]]
groupAllBy eq = groupBy eq.sort

{-- Just for renaming elemIndex to a more usual name -}
indexOf :: Eq a => a -> [a] -> Maybe Int
indexOf = elemIndex

{--- Returns the index of the last occurrence of the given element in the given list -}
lastIndexOf :: Eq a => a -> [a] -> Maybe Int
lastIndexOf x xs =
    case indexOf x (reverse xs) of
    
        Nothing     ->  Nothing
        Just idx    ->  Just (length xs - idx - 1)
   
-- extractPath "dir\dir2\test" -> ("dir\dir2", "test")
-- extractPath "test" -> (".", "test")
-- supports both windows and unix (and even mixed!) paths
extractPath filePath =
    case (lastIndexOf '\\' filePath, lastIndexOf '/' filePath) of 
        (Nothing, Nothing) -> (".", filePath)
        (Nothing, Just i ) -> (take i filePath, drop (i+1) filePath)
        (Just i , Nothing) -> (take i filePath, drop (i+1) filePath)
        (Just i , Just j )
            | i >= j       -> (take i filePath, drop (i+1) filePath)
            | otherwise    -> (take j filePath, drop (j+1) filePath)

splitFileName :: String -> (String, String)
splitFileName filename =
    case lastIndexOf '.' filename of
        Nothing     ->  (filename, "")
        Just idx    ->  let (name, _:ext) = splitAt idx filename in (name, ext)

splitFilePath :: String -> (String, String, String)
splitFilePath filePath =
    let
        (path    , fileName) = extractPath filePath
        (baseName, ext     ) = splitFileName fileName
    in
        (path, baseName, ext)

-- unsafePerformIO only to be able to make an error report 
-- in case of an internal error
refToCurrentFileName :: IORef String
refToCurrentFileName = unsafePerformIO (newIORef "<no module>")

-- unsafePerformIO only to be able to make an error report 
-- in case of an internal error
refToCurrentImported :: IORef [String]
refToCurrentImported = unsafePerformIO (newIORef [])

internalError :: String -> String -> String -> a
internalError moduleName functionName message 
   = unsafePerformIO 
   $ do (do -- internal errors are automatically logged
            curFileName <- readIORef refToCurrentFileName
            curImports  <- readIORef refToCurrentImported       
            logger "I" (Just (curImports,curFileName))
            `catch`
               \exception -> return () )
    
        return . error . unlines $
           [ ""
           , "INTERNAL ERROR - " ++ message
           , "** Module   : " ++ moduleName
           , "** Function : " ++ functionName
           ]

doubleSizeOfSTArray :: a -> STArray state Int a -> ST state (STArray state Int a)
doubleSizeOfSTArray unit starray = 
   do let (lower,upper) = boundsSTArray starray
      newarray <- newSTArray (lower,2 * upper - lower) unit
      let f i = do value <- readSTArray starray i            
                   writeSTArray newarray i value
      mapM_ f [lower..upper]
      return newarray
