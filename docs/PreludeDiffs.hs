Same in Helium
--------------

map, (++), concat, filter, 
head, last, tail, init, null, length, (!!),
foldl, foldl1, scanl, scanl1, foldr, foldr1, scanr, scanr1,
iterate, repeat, replicate, cycle,
take, drop, splitAt, takeWhile, dropWhile, span, break,
lines, words, unlines, unwords, reverse, and, or,
any, all, 
concatMap, 
zip, zip3, zipWith, zipWith3, unzip, unzip3,
putChar, putStr, putStrLn, 
getChar, getLine, 
isSpace, isUpper, isLower,
isAlpha, isDigit, isAlphaNum,
toUpper, toLower,
ord, chr,
Bool(False, True),
Maybe(Nothing, Just),
Either(Left, Right),
Ordering(LT, EQ, GT),
Char, String, Int, Float, IO,
(:),
pi, 
maybe, either,
(&&), (||), not, otherwise,
fst, snd, curry, uncurry, id, const, (.), flip, ($), until,
seq, ($!)
error, undefined,

Overloaded
----------

elem -- elemBy
notElem -- notElemBy
lookup -- lookupBy
sum, product, maximum, minimum -- only for Int
print -- extra parameter: a -> String
Eq((==), (/=)), -- only for Int, others are called eq... (eqChar, eqString..)
Ord(compare, (<), (<=), (>=), (>), max, min), -- only for Int (except compare)
    -- Floats can be compared using <. <=. >=. >. 
Enum(succ, pred, toEnum, fromEnum, enumFrom, enumFromThen,
     enumFromTo, enumFromThenTo),
    -- enumFrom(Then)(To) only for Int, rest unavailable
Num((+), (-), (*), negate, abs, signum, fromInteger, fromInt),
    -- only for Int; fromInt(eger) not available 
    -- Floats can be computed with using +. -. *. /. negateFloat
Integral(quot, rem, div, mod, quotRem, divMod, even, odd, toInteger, toInt),
    -- quot, rem, div, mod, even, odd only for Int; rest unavailable
sequence, sequence_, -- only for IO monad
Monad((>>=), (>>), return, fail), -- return for IO monad; rest unavailable
subtract, -- Int
even, odd, gcd, lcm, -- Int
(^), -- only for Int; for Float is called ^.

Not there
---------

ReadS, ShowS,
Read(readsPrec, readList),
Show(show, showsPrec, showList), -- show in different versions (showChar, showInt...)
reads, shows, read, lex, -- read for Ints = readInt
showChar, showString, readParen, showParen, -- showChar and showString do exist but return a String, not ShowS
FilePath, IOError, ioError, userError, catch,
getContents, interact,
readFile, writeFile, appendFile, readIO, readLn,
Ix(range, index, inRange, rangeSize),
isAscii, isControl, isPrint, 
isOctDigit, isHexDigit, 
digitToInt, intToDigit,
readLitChar, showLitChar, lexLitChar,
showSigned, showInt, -- showInt exists with different type: Int -> String
readSigned, readInt, -- showInt exists with different type: String -> Int
readDec, readOct, readHex, readSigned,
readFloat, lexDigits, 
Ratio, Rational, (%), numerator, denominator, approxRational,
{-
--  Non-standard exports
IO(..), IOResult(..), primExitWith, Addr, Word, StablePtr, ForeignObj,
basicIORun, blockIO, IOFinished(..),
threadToIOResult,
HugsException, catchHugsException, primThrowException,
-}
Integer, Double, 
Rec, EmptyRec, EmptyRow, -- non-standard, should only be exported if TREX
Bounded(minBound, maxBound),
Real(toRational),
Fractional((/), recip, fromRational, fromDouble), -- /. for Floats
Floating(exp, log, sqrt, (**), logBase, sin, cos, tan,
         asin, acos, atan, sinh, cosh, tanh, asinh, acosh, atanh),
RealFrac(properFraction, truncate, round, ceiling, floor),
RealFloat(floatRadix, floatDigits, floatRange, decodeFloat,
          encodeFloat, exponent, significand, scaleFloat, isNaN,
          isInfinite, isDenormalized, isIEEE, isNegativeZero, atan2),
Functor(fmap),
mapM, mapM_, (=<<),
fromIntegral, realToFrac,
asTypeOf, 
(^^), 