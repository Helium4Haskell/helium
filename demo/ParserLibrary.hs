module ParserLibrary where

type Parser symbol result  =  [symbol] -> [([symbol],result)]

{- A parser that yields just one solution and no rest-string
   is called a deterministic parser:
-}

type DetPars symbol result  =  [symbol] -> result

------------------------------------------------------------
-- Priorities of operators

infixr 6  <*> , <*   ,  *> , <:*>
infixl 5  <@  , <?@
infixr 4  <|>

------------------------------------------------------------
-- Auxiliary functions

list        ::  (a, [a]) -> [a]
list (x,xs)  =  x:xs

single      ::  a -> [a]
single x     =  [x]

ap2         ::  (a -> b -> c, b) -> a -> c
ap2 (op,y)   =  (\x -> x `op` y)

ap1         ::  (a, a -> b -> c) -> b -> c
ap1 (x,op)   =  (\y -> x `op` y)

ap          ::  (a -> b, a) -> b
ap  (f,x)    =  f x

ap'         ::  (a, a -> b) -> b
ap' (x,f)    =  f x

------------------------------------------------------------
-- Trivial parsers

fail         ::  Parser s r
fail _        =  []

succeed      ::  r -> Parser s r
succeed v xs  =  [ (xs,v) ]

epsilon      ::  Parser s ()
epsilon       =  succeed ()

------------------------------------------------------------
-- Elementary parsers

satisfy              ::  (s -> Bool) -> Parser s s
satisfy _ []          =  []
satisfy p (x:xs)      =  [ (xs,x) | p x ]

symbol               ::  (s -> s -> Bool) ->  s -> Parser s s
symbol eq             =  satisfy . eq

symbol'              ::  (s -> s -> Bool) ->  s -> Parser s s
symbol' _ _ []        =  []
symbol' eq a (x:xs)   =  [ (xs,x) | a `eq` x ]

symbol''             ::  (s -> s -> Bool) ->  s -> Parser s s
symbol'' _ _ []                     =  []
symbol'' eq a (x:xs)  |  a `eq` x   =  [ (xs,x) ]
                      |  otherwise  =  []

token                ::  (s -> s -> Bool) ->  [s] -> Parser s [s]
token eq              =  sequenceP . map (symbol eq)

token'               ::  (s -> s -> Bool) ->  [s] -> Parser s [s]
token' eq k xs        |  (eqList eq) k (take n xs)  =  [ (drop n xs, k) ]
                      |  otherwise                  =  []
                  where  n :: Int
                         n = length k

------------------------------------------------------------
-- Parser combinators 

(<*>)          ::  Parser s a -> Parser s b -> Parser s (a, b)
(p1 <*> p2) xs  =  [  (xs2,(v1,v2)) 
                   |  (xs1, v1) <- p1 xs
                   ,  (xs2, v2) <- p2 xs1
                   ]

(<|>)          ::  Parser s a -> Parser s a -> Parser s a
(p1 <|> p2) xs  =  p1 xs ++ p2 xs

(<@)           ::  Parser s a -> (a -> b) -> Parser s b
(p <@ f) xs     =  [ (ys, f v)
                   | (ys,   v) <- p xs
                   ]

option         ::  Parser s a -> Parser s [a]
option p        =  p  <@  single  <|>  succeed []

many           ::  Parser s a  -> Parser s [a]
many p          =  p <:*> (many p)  <|>  succeed []

many1          ::  Parser s a -> Parser s [a]
many1 p         =  p <:*> many p 

-----------------------------------------------------------
-- Determinsm

determ      ::  Parser a b -> Parser a b
determ p xs  |  null r     =  []
             |  otherwise  =  [head r]
         where  r = p xs

compulsion  ::  Parser a b -> Parser a [b]
compulsion  =   determ . option

greedy      ::  Parser a b -> Parser a [b]
greedy       =  determ . many

greedy1     ::  Parser a b -> Parser a [b]
greedy1      =  determ . many1

------------------------------------------------------------
-- Abbreviations

(<*)         ::  Parser s a -> Parser s b -> Parser s a
p <* q        =  p <*> q  <@  fst

(*>)         ::  Parser s a -> Parser s b -> Parser s b
p *> q        =  p <*> q  <@  snd

(<:*>)       ::  Parser s a -> Parser s [a] -> Parser s [a]
p <:*> q      =  p <*> q  <@  list

(<?@)        ::  Parser s [a] -> (b, a -> b) -> Parser s b
p <?@ (n,y)   =  p <@ f
          where  f []  = n
                 f [h] = y h

pack         ::  Parser s a -> Parser s b -> Parser s c -> Parser s b
pack s1 p s2  =  s1 *> p <* s2

listOf       ::  Parser s a -> Parser s b -> Parser s [a]
listOf p s    =  p <:*> many (s *> p)  <|>  succeed []

chainl       ::  Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainl p s    =  p <*> many (s <*> p)  <@  uncurry (foldl (flip ap2))


chainr       ::  Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainr p s    =  many (p <*> s) <*> p  <@  uncurry (flip (foldr ap1))

sequenceP    ::  [Parser s a] -> Parser s [a]
sequenceP     =  foldr (<:*>) (succeed [])

choice       ::  [Parser s a] -> Parser s a
choice        =  foldr (<|>) fail

chainl'      ::  Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainl' p s   =  q
          where  q = (option (q <*> s) <?@ (id,ap1) ) <*> p <@ ap

chainr'      ::  Parser s a -> Parser s (a -> a -> a) -> Parser s a
chainr' p s   =  q
          where  q = p <*> (option (s <*> q) <?@ (id,ap2) ) <@ ap'

------------------------------------------------------------
-- Parser transformators

just       ::  Parser s a -> Parser s a
just p      =  filter (null.fst) . p

just'      ::  Parser s a -> Parser s a
just' p xs  =  [ ([],v)
               | (ys,v) <- p xs
               , null ys
               ]

some       ::  Parser s a -> DetPars s a
some p      =  snd . head . just p

------------------------------------------------------------
-- Some common special cases

identifier  ::  Parser Char String
identifier   =  satisfy isAlpha <:*> greedy (satisfy isAlphaNum)


digit       ::  Parser Char Int
digit        =  satisfy isDigit  <@  f
         where  f :: Char -> Int
                f c = ord c - ord '0'


natural     ::  Parser Char Int
natural      =  greedy1 digit  <@  foldl f 0
         where  f :: Int -> Int -> Int
                f a b = a*10 + b

integer     ::  Parser Char Int
integer      =  option (symbol eqChar '-') <*> natural  <@  f
         where  f :: ([a], Int) -> Int
                f ([],n) =  n
                f (_ ,n) = -n

integer'    ::  Parser Char Int
integer'     =  (option (symbol eqChar '-') <?@ (id,const negate)) <*> natural  <@ ap


fixed       ::  Parser Char Float
fixed        =  (integer <@ intToFloat)
                <*> 
                (option (symbol eqChar '.' *> fractpart)  <?@  (0.0,id))
                <@  uncurry (+.)

fractpart   ::  Parser Char Float
fractpart    =  greedy digit  <@  foldr f 0.0
         where  f :: Int -> Float -> Float
                f d n = (n +. intToFloat d) /. 10.0

float       ::  Parser Char Float
float        =  fixed 
                <*> 
                (option (symbol eqChar 'E' *> integer) <?@ (0,id) )
                <@ f
         where  f :: (Float, Int) -> Float 
                f (m,e)  =  m *. power e
                power :: Int -> Float
                power e | e<0       = 1.0 /. power (-e)
                        | otherwise = intToFloat (10^e)


sp          ::  Parser Char a -> Parser Char a
sp           =  (\x -> greedy (satisfy isSpace) *> x)

sp'         ::  Parser Char a -> Parser Char a
sp'          =  (\x -> x . (dropWhile isSpace))
 
sptoken     ::  String -> Parser Char String
sptoken      =  sp . token eqChar

spsymbol    ::  Char -> Parser Char Char
spsymbol     =  sp . symbol eqChar

spident     ::  Parser Char String
spident      =  sp identifier

parenthesized, bracketed, braced, 
   angled, quoted, stropped  ::  Parser Char a -> Parser Char a
 
parenthesized p  =  pack (spsymbol '(')  p (spsymbol ')')
bracketed p      =  pack (spsymbol '[')  p (spsymbol ']')
braced p         =  pack (spsymbol '{')  p (spsymbol '}')
angled p         =  pack (spsymbol '<')  p (spsymbol '>')
quoted p         =  pack (spsymbol '"')  p (spsymbol '"')
stropped p       =  pack (spsymbol '\'') p (spsymbol '\'')

commaList, semicList  ::  Parser Char a -> Parser Char [a]
commaList p  =  listOf p (spsymbol ',')
semicList p  =  listOf p (spsymbol ';')

twopass  ::  Parser a b -> Parser b c -> Parser a c
twopass lex synt xs  =  [ (rest,tree)
                        | (rest,tokens) <- many lex xs
                        , (_,tree)      <- just synt tokens
                        ]
