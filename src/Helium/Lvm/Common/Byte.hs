--------------------------------------------------------------------------------
-- Copyright 2001-2012, Daan Leijen, Bastiaan Heeren, Jurriaan Hage. This file 
-- is distributed under the terms of the BSD3 License. For more information, 
-- see the file "LICENSE.txt", which is included in the distribution.
--------------------------------------------------------------------------------
--  $Id$
module Helium.Lvm.Common.Byte
   ( Byte, Bytes 
   , Monoid(..), unit, isEmpty
   , bytesLength, writeBytes, bytesFromList, listFromBytes
   , bytesFromString, stringFromBytes, bytesFromInt32, byteFromInt8
   , readByteList, int32FromByteList, stringFromByteList, bytesFromByteList
   ) where

import qualified Control.Exception as CE (catch, IOException) 
--import Data.Monoid
import Data.Word
import System.Exit
import System.IO
import Data.Semigroup as Sem

{----------------------------------------------------------------
  types
----------------------------------------------------------------}
type Byte   = Word8

-- | A spine-strict sequence of 'Byte's with @O(1)@ pairwise concatenation
data Bytes  = Nil
            | Cons Byte   !Bytes    -- Byte is not strict since LvmWrite uses it lazily right now.
            | Cat  !Bytes !Bytes

instance Show Bytes where
  show bs     = show (listFromBytes bs)

instance Eq Bytes where
  bs1 == bs2  = listFromBytes bs1 == listFromBytes bs2

{----------------------------------------------------------------
  conversion to bytes
----------------------------------------------------------------}
byteFromInt8 :: Int -> Byte
byteFromInt8 = toEnum
  
intFromByte :: Byte -> Int
intFromByte = fromEnum

bytesFromString :: String -> Bytes
bytesFromString 
  = bytesFromList . map (toEnum . fromEnum)

stringFromBytes :: Bytes -> String
stringFromBytes 
  = map (toEnum . fromEnum) . listFromBytes 

bytesFromInt32 :: Int -> Bytes    -- 4 byte big-endian encoding
bytesFromInt32 i
  = let n0 = if i < 0 then max32+i+1 else i
        n1 = div n0 256
        n2 = div n1 256
        n3 = div n2 256
        xs = map (byteFromInt8 . flip mod 256) [n3,n2,n1,n0]
    in bytesFromList xs

max32 :: Int 
max32 = 2^(32::Int) -1 -- Bastiaan (Todo: check)

{----------------------------------------------------------------
  Byte lists
----------------------------------------------------------------}

instance Sem.Semigroup Bytes where
   bs  <> Nil = bs
   Nil <> cs  = cs
   bs  <> cs  = Cat bs cs

instance Monoid Bytes where
   mempty  = Nil
   mappend = (<>)

isEmpty :: Bytes -> Bool
isEmpty Nil         = True
isEmpty (Cons _ _)  = False
isEmpty (Cat bs cs) = isEmpty bs && isEmpty cs

unit :: Byte -> Bytes
unit = (`Cons` Nil)

listFromBytes :: Bytes -> [Byte]
listFromBytes = loop []
  where
    loop next bs
      = case bs of
          Nil       -> next
          Cons b xs -> b:loop next xs
          Cat xs ys -> loop (loop next ys) xs

bytesFromList :: [Byte] -> Bytes
bytesFromList = foldr Cons Nil

bytesLength :: Bytes -> Int
bytesLength = loop 0
  where
    loop n bs
      = case bs of
          Nil       -> n
          Cons _ xs -> (loop $! (n+1)) xs
          Cat xs ys -> loop (loop n ys) xs

writeBytes :: FilePath -> Bytes -> IO ()
writeBytes path bs
  = do{ h <- openBinaryFile path WriteMode
      ; writeHandle h bs
      ; hClose h

      }
      
writeHandle :: Handle -> Bytes -> IO ()
writeHandle h bs
   = case bs of
       Nil       -> return ()
       Cons b xs -> do{ hPutChar h (toEnum (fromEnum b)); writeHandle h xs }
       Cat xs ys -> do{ writeHandle h xs; writeHandle h ys }


{----------------------------------------------------------------
  Byte lists
----------------------------------------------------------------}
int32FromByteList :: [Byte] -> (Int,[Byte])
int32FromByteList bs
  = case bs of
      n3:n2:n1:n0:cs -> let i = int32FromByte4 n3 n2 n1 n0 in seq i (i,cs)
      _              -> error "Byte.int32FromBytes: invalid byte stream"
              
int32FromByte4 :: Byte -> Byte -> Byte -> Byte -> Int      
int32FromByte4 n0 n1 n2 n3
  = (intFromByte n0*16777216) + (intFromByte n1*65536) + (intFromByte n2*256) + intFromByte n3


stringFromByteList :: [Byte] -> String
stringFromByteList = map (toEnum . fromEnum)

bytesFromByteList :: [Byte] -> Bytes
bytesFromByteList = bytesFromList

readByteList :: FilePath -> IO [Byte]
readByteList path 
  = do{ h  <- openBinaryFile path ReadMode
      ; xs <- hGetContents h
      ; seq (last xs) (hClose h)
      ; return (map (toEnum . fromEnum) xs)
      } `CE.catch` (\exception ->
            let message =  show (exception :: CE.IOException) ++ "\n\nUnable to read from file " ++ show path
            in do { putStrLn message; exitWith (ExitFailure 1) })
