module PreludeIO where

import Foreign

type FileDescriptor = CInt

foreign import ccall "_putchar" _putchar :: FileDescriptor -> Char -> IO CInt
foreign import ccall "_getchar" _getchar :: FileDescriptor -> IO Char

stdin :: FileDescriptor
stdin = CInt 0

stdout :: FileDescriptor
stdout = CInt 1

stderr :: FileDescriptor
stderr = CInt 2

primPutChar :: Char -> IO ()
primPutChar c = do
    _putchar stdout c
    returnIO ()

putChars :: String -> IO ()
putChars [] = returnIO ()
putChars (x : xs) = do
    primPutChar x
    putChars xs

putStr :: String -> IO ()
putStr s = do
    putChars s

putStrLn :: String -> IO ()
putStrLn s = do
    putChars s
    primPutChar '\n'

print :: Show a => a -> IO ()
print e = putStrLn (show e)

primGetChar :: IO Char
primGetChar = _getchar stdin

getChar :: IO Char
getChar = primGetChar

getLine :: IO String
getLine = do
    c <- getChar
    if c == '\n'
        then return ""
        else do
            rest <- getLine
            return (c : rest)