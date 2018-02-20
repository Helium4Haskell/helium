Below you can find an overview of the functions made available by the Helium Prelude.
Note that only the non-overloaded Prelude is described. 

*A* [abs](#AbsPrelude), [all](#AllPrelude), [and](#AndPrelude),
[any](#AnyPrelude) *B* [break](#BreakPrelude) *C*
[ceiling](#CeilingPrelude), [chr](#ChrPrelude), [concat](#ConcatPrelude),
[concatMap](#ConcatmapPrelude), [const](#ConstPrelude), [cos](#CosPrelude)
*D* [div](#DivPrelude), [drop](#DropPrelude), [dropWhile](#DropwhilePrelude)
*E* [elemBy](#ElembyPrelude), [eqBool](#EqboolPrelude),
[eqChar](#EqcharPrelude), [eqList](#EqlistPrelude), [eqString](#EqstringPrelude),
[error](#ErrorPrelude), [even](#EvenPrelude), [exp](#ExpPrelude)
*F* [filter](#FilterPrelude), [flip](#FlipPrelude),
[floor](#FloorPrelude), [foldl](#FoldlPrelude), [foldl1](#Foldl1Prelude),
[foldr](#FoldrPrelude), [foldr1](#Foldr1Prelude), [fromInt](#FromintPrelude),
[fst](#FstPrelude) *G* [gcd](#GcdPrelude) *H* [head](#HeadPrelude)
*I* [id](#IdPrelude), [init](#InitPrelude), [isAlpha](#IsalphaPrelude),
[isDigit](#IsdigitPrelude), [isLower](#IslowerPrelude),
[isSpace](#IsspacePrelude), [isUpper](#IsupperPrelude),
[iterate](#IteratePrelude) *L* [last](#LastPrelude),
[lcm](#LcmPrelude), [length](#LengthPrelude), [lines](#LinesPrelude),
[log](#LogPrelude) *M* [map](#MapPrelude), [max](#MaxPrelude),
[maximum](#MaximumPrelude), [min](#MinPrelude), [minimum](#MinimumPrelude),
[mod](#ModPrelude) *N* [not](#NotPrelude), [notElemBy](#NotelembyPrelude),
[null](#NullPrelude) *O* [odd](#OddPrelude), [or](#OrPrelude),
[ord](#OrdPrelude), [ordChar](#OrdcharPrelude), [ordFloat](#OrdfloatPrelude),
[ordInt](#OrdintPrelude), [ordList](#OrdlistPrelude),
[ordString](#OrdstringPrelude) *P* [pi](#PiPrelude),
[putStr](#PutstrPrelude), [product](#ProductPrelude) *Q*
[quot](#QuotPrelude) *R* [readInt](#ReadintPrelude),
[rem](#RemPrelude), [repeat](#RepeatPrelude), [replicate](#ReplicatePrelude),
[reverse](#ReversePrelude), [round](#RoundPrelude), *S*
[showInt](#ShowintPrelude),
[signum](#SignumPrelude), [signumFloat](#SignumfloatPrelude),
[sin](#SinPrelude), [snd](#SndPrelude), [span](#SpanPrelude),
[splitAt](#SplitatPrelude), [sqrt](#SqrtPrelude), [subtract](#SubtractPrelude),
[sum](#SumPrelude) *T* [tail](#TailPrelude), [take](#TakePrelude),
[takeWhile](#TakewhilePrelude), [tan](#TanPrelude), [toLower](#TolowerPrelude),
[toUpper](#ToupperPrelude), [truncate](#TruncatePrelude) *U*
[undefined](#UndefinedPrelude), [unlines](#UnlinesPrelude),
[until](#UntilPrelude), [unwords](#UnwordsPrelude) *W*
[words](#WordsPrelude) *Z* [zip](#ZipPrelude), [zipWith](#ZipwithPrelude)

*Boolean operators* [(&&)](#OpandPrelude),
[(%VBAR%%VBAR%)](#OporPrelude) 

*Integer operators* [(*)](#MulPrelude),
[(/)](#OpdivPrelude), [(+)](#AddPrelude), [(-)](#SubPrelude),
[(^)](#HatPrelude) [(/=)](#NePrelude), [(==)](#EqPrelude),
[(<)](#LtPrelude), [(<=)](#LePrelude), [(>)](#GtPrelude),
[(>=)](#GePrelude) 

*Floating-point operators* [(*.)](#MulfltPrelude),
[(/.)](#OpdivfltPrelude), [(+.)](#AddfltPrelude), [(-.)](#SubfltPrelude),
[(^.)](#PowfltPrelude) [(/=.)](#NefltPrelude), [(==.)](#EqfltPrelude),
[(<.)](#LtfltPrelude), [(<=.)](#LefltPrelude), [(>.)](#GtfltPrelude),
[(>=.)](#GefltPrelude) [(**.)](#StarstarPrelude) 

*Other operators* [(!!)](#IndexPrelude), [(:)](#ConsPrelude),
[(++)](#AppendPrelude), [(.)](#ComposePrelude) 


<a name="AbsPrelude"></a>
| _type:_ | abs :: Int -> Int |
| _description:_ | returns the absolute value of a number. |
| _definition:_ | <pre>abs x
  %VBAR% x >= 0 = x
  %VBAR% otherwise = -x</pre> |
| _usage:_ | <pre>Prelude> abs (-3)
3</pre> |

<a name="AllPrelude"></a>
| _type:_ | all 			:: (a -> Bool) -> [a] -> Bool |
| _description:_ | applied to a predicate and a list, \
returns True if all elements of the list satisfy the predicate, and False otherwise. \
Similar to the function <a href="<a name="AnyPrelude">any</a>. |"></a>
| _definition:_ | <pre>all p xs = <a href="<a name="AndPrelude">and</a> (<a href="#MapPrelude">map</a> p xs)</pre> |"></a>
| _usage:_ | <pre>Prelude> all (< 11) [1..10]
True
Prelude> all isDigit "123abc"
False</pre> |

<a name="AndPrelude"></a>
| _type:_ | and 			:: [Bool] -> Bool |
| _description:_ | takes the logical conjunction of a list of boolean values (see \
			also `<a href="<a name="OrPrelude">or</a>'). |"></a>
| _definition:_ | <pre>and xs = <a href="<a name="FoldrPrelude">foldr</a> (&&) True xs</pre> |"></a>
| _usage:_ | <pre>Prelude> and [True, True, False, True]
False
Prelude> and [True, True, True, True]
True
Prelude> and []
True</pre> |

<a name="AnyPrelude"></a>
| _type:_ | any :: (a -> Bool) -> [a] -> Bool |
| _description:_ | applied to a predicate and a list, returns True if any of the \
			elements of the list satisfy the predicate, and False otherwise. \
			Similar to the function <a href="<a name="AllPrelude">all</a>. |"></a>
| _definition:_ | <pre>any p xs = <a href="<a name="OrPrelude">or</a> (<a href="#MapPrelude">map</a> p xs)</pre> |"></a>
| _usage:_ | <pre>Prelude> any (< 11) [1..10]
True
Prelude> any isDigit "123abc"
True
Prelude> any isDigit "alphabetics"
False</pre> |

<a name="BreakPrelude"></a>
| _type:_ | break :: (a -> Bool) -> [a] -> ([a],[a]) |
| _description:_ | given a predicate and a list, breaks the list into two lists \
			(returned as a tuple) at the point where the predicate is first \
			satisfied. If the predicate is never satisfied then the first \
			element of the resulting tuple is the entire list and the second \
			element is the empty list ([]). |
| _definition:_ | <pre>break p xs
  = <a href="<a name="SpanPrelude">span</a> p' xs"></a>
    where
    p' x = <a href="<a name="NotPrelude">not</a> (p x)</pre> |"></a>
| _usage:_ | <pre>Prelude> break isSpace "hello there fred"
("hello", " there fred")
Prelude> break isDigit "no digits here"
("no digits here","")</pre> |

<a name="CeilingPrelude"></a>
| _type:_ | ceiling :: Float -> Int |
| _description:_ | returns the smallest integer not less than its argument. |
| _usage:_ | <pre>Prelude> ceiling 3.8
4
Prelude> ceiling (-.3.8)
-3</pre> |
| _see also:_ | <a href="<a name="FloorPrelude">floor</a> |"></a>

<a name="ChrPrelude"></a>
| _type:_ | chr :: Int -> Char |
| _description:_ | applied to an integer in the range 0 -- 255, returns the \
			character whose ascii code is that integer. It is the converse of \
			the function ord. An error will result if chr is applied to an \
			integer outside the correct range. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> chr 65
'A'
Prelude> (ord (chr 65)) == 65
True</pre> |
| _see also:_ | <a href="<a name="OrdPrelude">ord</a> |"></a>

<a name="ConcatPrelude"></a>
| _type:_ | concat :: [[a]] -> [a] |
| _description:_ | applied to a list of lists, joins them together using the ++ operator. |
| _definition:_ | <pre>concat xs = <a href="<a name="FoldrPrelude">foldr</a> (++) [] xs</pre> |"></a>
| _usage:_ | <pre>Prelude> concat [[1,2,3], [4], [], [5,6,7,8]]
[1, 2, 3, 4, 5, 6, 7, 8]</pre> |

<a name="ConcatmapPrelude"></a>
| _type:_ | concatMap :: (a -> [b]) -> [a] -> [b] |
| _description:_ | given a function which maps a value to a list, and a list of \
			elements of the same type as the value, applies the function to \
			the list and then concatenates the result (thus flattening the \
			resulting list). |
| _definition:_ | <pre>concatMap f = <a href="<a name="ConcatPrelude">concat</a> . <a href="#MapPrelude">map</a> f</pre> |"></a>
| _usage:_ | <pre>Prelude> concatMap showInt [1,2,3,4]
"1234"</pre> |

<a name="ConstPrelude"></a>
| _type:_ | const :: const :: a -> b -> a |
| _description:_ | creates a constant valued function which always has the value \
			of its first argument, regardless of the value of its second \
			argument. |
| _definition:_ | <pre>const k _ = k</pre> |
| _usage:_ | <pre>Prelude> const 12 "lucky"
12</pre> |

<a name="CosPrelude"></a>
| _type:_ | cos :: Float -> Float |
| _description:_ | the trigonometric cosine function, arguments are interpreted to be in radians. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> cos pi
-1
Prelude> cos (pi/.2.0)
6.12303e-017</pre> |

<a name="DivPrelude"></a>
| _type:_ | div :: Int -> Int -> Int |
| _description:_ | computes the integer division of its integral arguments. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> 16 `div` 9
1
Prelude> (-12) `div` 5
-3</pre> |
| _notes:_ | <tt>`div`</tt> is integer division such that the result is \
truncated towards negative infinity. |

<a name="DropPrelude"></a>
| _type:_ | drop :: Int -> [a] -> [a] |
| _description:_ | applied to a number and a list, returns the list with the \
			specified number of elements removed from the front of the list. \
			If the list has less than the required number of elements then it \
			returns []. |
| _definition:_ | <pre>drop n xs %VBAR% n <= 0  = xs
drop _ []           = []
drop n (_:xs)       = drop (n-1) xs</pre> |
| _usage:_ | <pre>Prelude> drop 3 [1..10]
[4, 5, 6, 7, 8, 9, 10]
Prelude> drop 4 "abc"
""</pre> |

<a name="DropwhilePrelude"></a>
| _type:_ | dropWhile :: (a -> Bool) -> [a] -> [a] |
| _description:_ | applied to a predicate and a list, removes elements from the \
			front of the list while the predicate is satisfied. |
| _definition:_ | <pre>dropWhile p [] = []
dropWhile p (x:xs)
  %VBAR% p x = dropWhile p xs
  %VBAR% otherwise = (x:xs)</pre> |
| _usage:_ | <pre>Prelude> dropWhile (< 5) [1..10]
[5, 6, 7, 8, 9, 10]</pre> |

<a name="ElembyPrelude"></a>
| _type:_ | elemBy :: (a -> a -> Bool) -> a -> [a] -> Bool |
| _description:_ | applied to a comparison function, a value and a list returns \
			True if the value is in the list and False otherwise. The elements \
			of the list must be of the same type as the value. |
| _definition:_ | <pre>elemBy _ _ [] = False
elemBy eq x (y:ys)
  %VBAR% x `eq` y = True
  %VBAR% otherwise = elemBy eq x ys</pre> |
| _usage:_ | <pre>Prelude> elemBy (==) 5 [1..10]
True
Prelude> elemBy eqString "rat" ["fat", "cat"]
False</pre> |

<a name="EqboolPrelude"></a>
| _type:_ | eqBool :: Bool -> Bool -> Bool |
| _description:_ | is <tt>True</tt> if its first argument is equal to its second \
			argument, and <tt>False</tt> otherwise. |
| _definition:_ | <pre>eqBool True True = True
eqBool False False = True
eqBool _ _ = False</pre> |
| _usage:_ | <pre>Prelude> eqBool True False
False</pre> |
| _see also:_ | <a href="<a name="EqboolPrelude">eqBool</a>, <a href="#EqcharPrelude">eqChar</a>, \"></a>
			<a href="<a name="EqlistPrelude">eqList</a>, <a href="#EqstringPrelude">eqString</a>, \"></a>
			<a href="<a name="EqPrelude">(&#61;&#61;)</a>, <a href="#EqfltPrelude">(&#61;&#61;.)</a> |"></a>

<a name="EqcharPrelude"></a>
| _type:_ | eqChar :: Char -> Char -> Bool |
| _description:_ | is <tt>True</tt> if its first argument is equal to its second \
			argument, and <tt>False</tt> otherwise. |
| _definition:_ | <pre>eqChar c1 c2 =
    case ordChar c1 c2 of
        EQ -> True
        _  -> False</pre> |
| _usage:_ | <pre>Prelude> filter (eqChar 'a') "banana"
"aaa;"
Prelude> elemBy eqChar 'x' "yada"
False</pre> |
| _see also:_ | <a href="<a name="EqboolPrelude">eqBool</a>, <a href="#EqcharPrelude">eqChar</a>, \"></a>
			<a href="<a name="EqlistPrelude">eqList</a>, <a href="#EqstringPrelude">eqString</a>, \"></a>
			<a href="<a name="EqPrelude">(&#61;&#61;)</a>, <a href="#EqfltPrelude">(&#61;&#61;.)</a> |"></a>

<a name="EqlistPrelude"></a>
| _type:_ | eqList :: (a -> a -> Bool) -> [a] -> [a] -> Bool |
| _description:_ | is <tt>True</tt> if the first list is equal to the second list, \
			and <tt>False</tt> otherwise. Elements are compared using the \
			function passed as first argument. |
| _definition:_ | <pre>eqList _      []     []     =  True
eqList eqElem (x:xs) (y:ys) =
        x `eqElem` y && eqList eqElem xs ys
eqList _      _      _      = False</pre> |
| _usage:_ | <pre>Prelude> eqList (==) [1,2,3] [1,2,4]
False
Prelude> eqList eqChar "abc" "abc"
True</pre> |
| _see also:_ | <a href="<a name="EqboolPrelude">eqBool</a>, <a href="#EqcharPrelude">eqChar</a>, \"></a>
			<a href="<a name="EqlistPrelude">eqList</a>, <a href="#EqstringPrelude">eqString</a>, \"></a>
			<a href="<a name="EqPrelude">(&#61;&#61;)</a>, <a href="#EqfltPrelude">(&#61;&#61;.)</a> |"></a>

<a name="EqstringPrelude"></a>
| _type:_ | eqString :: String -> String -> Bool |
| _description:_ | is <tt>True</tt> if its first argument is equal to its second \
			argument, and <tt>False</tt> otherwise. |
| _definition:_ | <pre>eqString s1 s2 =
    case ordString s1 s2 of
        EQ -> True
        _  -> False</pre> |
| _usage:_ | <pre>Prelude> eqString "Abc" "abc"
False
Prelude> eqString "abc" "abc"
True</pre> |
| _see also:_ | <a href="<a name="EqboolPrelude">eqBool</a>, <a href="#EqcharPrelude">eqChar</a>, \"></a>
			<a href="<a name="EqlistPrelude">eqList</a>, <a href="#EqstringPrelude">eqString</a>, \"></a>
			<a href="<a name="EqPrelude">(&#61;&#61;)</a>, <a href="#EqfltPrelude">(&#61;&#61;.)</a> |"></a>

<a name="ErrorPrelude"></a>
| _type:_ | error :: String -> a |
| _description:_ | applied to a string creates an error value with an associated \
			message. Error values are equivalent to the undefined value \
			(undefined), any attempt to access the value causes the program to \
			terminate and print the string as a diagnostic. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>error "this is an error message"</pre> |

<a name="EvenPrelude"></a>
| _type:_ | even :: Int -> Bool |
| _description:_ | applied to an integral argument, returns True if the argument \
			is even, and False otherwise. |
| _definition:_ | <pre>even n = n `rem` 2 == 0</pre> |
| _usage:_ | <pre>Prelude> even 2
True
Prelude> even (11 * 3)
False</pre> |

<a name="ExpPrelude"></a>
| _type:_ | exp :: Float -> Float |
| _description:_ | the exponential function (exp n is equivalent to e<sup>n</sup>). |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> exp 1.0
2.71828</pre> |

<a name="FilterPrelude"></a>
| _type:_ | filter :: (a -> Bool) -> [a] -> [a] |
| _description:_ | applied to a predicate and a list, returns a list containing \
			all the elements from the argument list that satisfy the \
			predicate. |
| _definition:_ | <pre>filter p xs = [k %VBAR% k <- xs, p k]</pre> |
| _usage:_ | <pre>Prelude> filter isDigit "fat123cat456"
"123456"</pre> |

<a name="FlipPrelude"></a>
| _type:_ | flip :: (a -> b -> c) -> b -> a -> c |
| _description:_ | applied to a binary function, returns the same function with \
			the order of the arguments reversed. |
| _definition:_ | <pre>flip f x y = f y x</pre> |
| _usage:_ | <pre>Prelude> flip (<a href="<a name="ElembyPrelude">elemBy</a> (==)) [1..10] 5"></a>
True</pre> |

<a name="FloorPrelude"></a>
| _type:_ | floor :: Float -> Int |
| _description:_ | returns the largest integer not greater than its argument. |
| _usage:_ | <pre>Prelude> floor 3.8
3
Prelude> floor (-.3.8)
-4</pre> |
| _see also:_ | <a href="<a name="CeilingPrelude">ceiling</a> |"></a>

<a name="FoldlPrelude"></a>
| _type:_ | foldl :: (a -> b -> a) -> a -> [b] -> a |
| _description:_ | folds up a list, using a given binary operator and a given \
			start value, in a left associative manner. \
			foldl op r [a, b, c] &rarr; ((r `op` a) `op` b) `op` c</pre> |
| _definition:_ | <pre>foldl f z [] = z
foldl f z (x:xs) = foldl f (f z x) xs</pre> |
| _usage:_ | <pre>Prelude> foldl (+) 0 [1..10]
55
Prelude> foldl (<a href="<a name="FlipPrelude">flip</a> (:)) [] [1..10]"></a>
[10, 9, 8, 7, 6, 5, 4, 3, 2, 1]</pre> |

<a name="Foldl1Prelude"></a>
| _type:_ | foldl1 :: (a -> a -> a) -> [a] -> a |
| _description:_ | folds left over non--empty lists. |
| _definition:_ | <pre>foldl1 f (x:xs) = <a href="<a name="FoldlPrelude">foldl</a> f x xs</pre> |"></a>
| _usage:_ | <pre>Prelude> foldl1 max [1, 10, 5, 2, -1]
10</pre> |

<a name="FoldrPrelude"></a>
| _type:_ | foldr :: (a -> b -> b) -> b -> [a] -> b |
| _description:_ | folds up a list, using a given binary operator and a given \
			start value, in a right associative manner. \
			foldr op r [a, b, c] &rarr; a `op` (b `op` (c `op` r))</pre> |
| _definition:_ | <pre>foldr f z [] = z
foldr f z (x:xs) = f x (foldr f z xs)</pre> |
| _usage:_ | <pre>Prelude> foldr (++) [] ["con", "cat", "en", "ate"]
"concatenate"</pre> |

<a name="Foldr1Prelude"></a>
| _type:_ | foldr1 :: (a -> a -> a) -> [a] -> a |
| _description:_ | folds right over non--empty lists. |
| _definition:_ | <pre>foldr1 f [x] = x
foldr1 f (x:xs) = f x (foldr1 f xs)</pre> |
| _usage:_ | <pre>Prelude> foldr1 (*) [1..10]
3628800</pre> |

<a name="FromintPrelude"></a>
| _type:_ | fromInt :: Int -> Float |
| _description:_ | Converts from an Int to a Float |
| _usage:_ | <pre>Prelude> fromInt 3 +. 4.1
7.1</pre> |

<a name="FstPrelude"></a>
| _type:_ | fst :: (a, b) -> a |
| _description:_ | returns the first element of a two element tuple. |
| _definition:_ | <pre>fst (x, _) = x</pre> |
| _usage:_ | <pre>Prelude> fst ("harry", 3)
"harry"</pre> |

<a name="GcdPrelude"></a>
| _type:_ | gcd :: Int -> Int -> Int |
| _description:_ | returns the greatest common divisor between its two integral arguments. |
| _definition:_ | <pre>gcd 0 0 =
    error "Prelude.gcd: gcd 0 0 is undefined"
gcd x y = gcd' (abs x) (abs y)
          where
             gcd' x 0 = x
             gcd' x y = gcd' y (x `rem` y)</pre> |
| _usage:_ | <pre>Prelude> gcd 2 10
2
Prelude> gcd (-7) 13
1</pre> |

<a name="HeadPrelude"></a>
| _type:_ | head :: [a] -> a |
| _description:_ | returns the first element of a non--empty list. If applied to \
			an empty list an error results. |
| _definition:_ | <pre>head (x:_) = x</pre> |
| _usage:_ | <pre>Prelude> head [1..10]
1
Prelude> head ["this", "and", "that"]
"this"</pre> |

<a name="IdPrelude"></a>
| _type:_ | id :: a -> a |
| _description:_ | the identity function, returns the value of its argument. |
| _definition:_ | <pre>id x = x</pre> |
| _usage:_ | <pre>Prelude> id 12
12
Prelude> id (id "fred")
"fred"
Prelude> eqList (==) (<a href="<a name="MapPrelude">map</a> id [1..10]) [1..10]"></a>
True</pre> |

<a name="InitPrelude"></a>
| _type:_ | init :: [a] -> [a] |
| _description:_ | returns all but the last element of its argument list. The \
			argument list must have at least one element. If init is applied \
			to an empty list an error occurs. |
| _definition:_ | <pre>init [x] = []
init (x:xs) = x : init xs</pre> |
| _usage:_ | <pre>Prelude> init [1..10]
[1, 2, 3, 4, 5, 6, 7, 8, 9]</pre> |

<a name="IsalphaPrelude"></a>
| _type:_ | isAlpha :: Char -> Bool |
| _description:_ | applied to a character argument, returns True if the character \
			is alphabetic, and False otherwise. |
| _definition:_ | <pre>isAlpha c = isUpper c %VBAR%%VBAR% isLower c</pre> |
| _usage:_ | <pre>Prelude> isAlpha 'a'
True
Prelude> isAlpha '1'
False</pre> |

<a name="IsdigitPrelude"></a>
| _type:_ | isDigit :: Char -> Bool |
| _description:_ | applied to a character argument, returns True if the character \
			is a numeral, and False otherwise. |
| _definition:_ | <pre>isDigit c = c >= '0' && c <= '9'</pre> |
| _usage:_ | <pre>Prelude> isDigit '1'
True
Prelude> isDigit 'a'
False</pre> |

<a name="IslowerPrelude"></a>
| _type:_ | isLower :: Char -> Bool |
| _description:_ | applied to a character argument, returns True if the character \
			is a lower case alphabetic, and False otherwise. |
| _definition:_ | <pre>isLower c = c >= 'a' && c <= 'z'</pre> |
| _usage:_ | <pre>Prelude> isLower 'a'
True
Prelude> isLower 'A'
False
Prelude> isLower '1'
False</pre> |

<a name="IsspacePrelude"></a>
| _type:_ | isSpace :: Char -> Bool |
| _description:_ | returns True if its character argument is a whitespace \
			character and False otherwise. |
| _definition:_ | <pre>isSpace c  =
        c == ' '  %VBAR%%VBAR% c == '\t' %VBAR%%VBAR% c == '\n' %VBAR%%VBAR%
        c == '\r' %VBAR%%VBAR% c == '\f' %VBAR%%VBAR% c == '\v'</pre> |
| _usage:_ | <pre>Prelude> dropWhile isSpace "   \nhello  \n"
"hello  \n"</pre> |

<a name="IsupperPrelude"></a>
| _type:_ | isUpper :: Char -> Bool |
| _description:_ | applied to a character argument, returns True if the character \
			is an upper case alphabetic, and False otherwise. |
| _definition:_ | <pre>isUpper c = c >= 'A' && c <= 'Z'</pre> |
| _usage:_ | <pre>Prelude> isUpper 'A'
True
Prelude> isUpper 'a'
False
Prelude> isUpper '1'
False</pre> |

<a name="IteratePrelude"></a>
| _type:_ | iterate :: (a -> a) -> a -> [a] |
| _description:_ | iterate f x returns the infinite list [x,f x,f (f x),...]. |
| _definition:_ | <pre>iterate f x = x : iterate f (f x)</pre> |
| _usage:_ | <pre>Prelude> iterate (+1) 1
[1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, .....</pre> |

<a name="LastPrelude"></a>
| _type:_ | last :: [a] -> a |
| _description:_ | applied to a non--empty list, returns the last element of the list. |
| _definition:_ | <pre>last [x] = x
last (_:xs) = last xs</pre> |
| _usage:_ | <pre>Prelude> last [1..10]
10</pre> |

<a name="LcmPrelude"></a>
| _type:_ | lcm :: Int -> Int -> Int |
| _description:_ | returns the least common multiple of its two integral arguments. |
| _definition:_ | <pre>lcm _ 0 = 0
lcm 0 _ = 0
lcm x y = abs ((x `quot` gcd x y) * y)</pre> |
| _usage:_ | <pre>Prelude> lcm 2 10
10
Prelude> lcm 2 11
22</pre> |

<a name="LengthPrelude"></a>
| _type:_ | length :: [a] -> Int |
| _description:_ | returns the number of elements in a finite list. |
| _definition:_ | <pre>length [] = 0
length (x:xs) = 1 + length xs</pre> |
| _usage:_ | <pre>Prelude> length [1..10]
10</pre> |

<a name="LinesPrelude"></a>
| _type:_ | lines :: String -> [String] |
| _description:_ | applied to a list of characters containing newlines, returns a \
			list of lists by breaking the original list into lines using the \
			newline character as a delimiter. The newline characters are \
			removed from the result. |
| _usage:_ | <pre>Prelude> lines "hello world\nit's me,\neric\n"
["hello world", "it's me,", "eric"]</pre> |

<a name="LogPrelude"></a>
| _type:_ | log :: Float -> Float |
| _description:_ | returns the natural logarithm of its argument. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> log 1.0
0
Prelude> log 3.2
1.16315</pre> |

<a name="MapPrelude"></a>
| _type:_ | map :: (a -> b) -> [a] -> [b] |
| _description:_ | given a function, and a list of any type, returns a list where \
			each element is the result of applying the function to the \
			corresponding element in the input list. |
| _definition:_ | <pre>map f xs = [f x %VBAR% x <- xs]</pre> |
| _usage:_ | <pre>Prelude> map sqrt [1.0,2.0,3.0,4.0,5.0]
[1,1.41421,1.73205,2,2.23607]</pre> |

<a name="MaxPrelude"></a>
| _type:_ | max :: Int -> Int -> Int |
| _description:_ | applied to two integers, returns the maximum of the two \
			elements. |
| _definition:_ | <pre>max :: Int -> Int -> Int
max x y = if x < y then y else x</pre> |
| _usage:_ | <pre>Prelude> max 1 2
2</pre> |

<a name="MaximumPrelude"></a>
| _type:_ | maximum :: [Int] -> Int |
| _description:_ | applied to a non--empty list of integers, returns the maximum \
			element of the list. |
| _definition:_ | <pre>maximum xs = <a href="<a name="foldl1Prelude">foldl1</a> <a href="#MaxPrelude">max</a> xs</pre> |"></a>
| _usage:_ | <pre>Prelude> maximum [-10, 0 , 5, 22, 13]
22</pre> |

<a name="MinPrelude"></a>
| _type:_ | min :: Int -> Int -> Int |
| _description:_ | applied to two integers, returns the minimum of the two. |
| _definition:_ | <pre>min x y
  %VBAR% x <= y = x
  %VBAR% otherwise = y</pre> |
| _usage:_ | <pre>Prelude> min 1 2
1</pre> |

<a name="MinimumPrelude"></a>
| _type:_ | minimum :: [Int] -> Int |
| _description:_ | applied to a non--empty list of integers, returns the minimum \
			element of the list. |
| _definition:_ | <pre>minimum xs = <a href="<a name="foldl1Prelude">foldl1</a> <a href="#MinPrelude">min</a> xs</pre> |"></a>
| _usage:_ | <pre>Prelude> minimum [-10, 0 , 5, 22, 13]
-10</pre> |

<a name="ModPrelude"></a>
| _type:_ | mod :: Int -> Int -> Int |
| _description:_ | returns the modulus of its two arguments. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> 16 `mod` 9
7</pre> |

<a name="NotPrelude"></a>
| _type:_ | not :: Bool -> Bool |
| _description:_ | returns the logical negation of its boolean argument. |
| _definition:_ | <pre>not True = False
not False = True</pre> |
| _usage:_ | <pre>Prelude> not (3 == 4)
True
Prelude> not (10 > 2)
False</pre> |

<a name="NotelembyPrelude"></a>
| _type:_ | notElemBy :: (a -> a -> Bool) -> a -> [a] -> Bool |
| _description:_ | returns <tt>True</tt> if its first argument is <em>not</em> an \
			element of the list as its second argument. |
| _usage:_ | <pre>Prelude> notElemBy (==) 3 [1,2,3]
False
Prelude> notElemBy (==) 4 [1,2,3]
True</pre> |

<a name="NullPrelude"></a>
| _type:_ | null :: [a] -> Bool |
| _description:_ | returns True if its argument is the empty list ([]) and False \
			otherwise. |
| _definition:_ | <pre>null [] = True
null (_:_) = False</pre> |
| _usage:_ | <pre>Prelude> null []
True
Prelude> null (<a href="<a name="TakePrelude">take</a> 3 [1..10])"></a>
False</pre> |

<a name="OddPrelude"></a>
| _type:_ | odd :: Int -> Bool |
| _description:_ | applied to an integral argument, returns True if the argument \
			is odd, and False otherwise. |
| _definition:_ | <pre>odd = <a href="<a name="NotPrelude">not</a> . <a href="#EvenPrelude">even</a></pre> |"></a>
| _usage:_ | <pre>Prelude> odd 1
True
Prelude> odd (2 * 12)
False</pre> |

<a name="OrPrelude"></a>
| _type:_ | or :: [Bool] -> Bool |
| _description:_ | applied to a list of boolean values, returns their logical \
			disjunction (see also `<a href="<a name="AndPrelude">and</a>'). |"></a>
| _definition:_ | <pre>or xs = <a href="<a name="FoldrPrelude">foldr</a> (%VBAR%%VBAR%) False xs</pre> |"></a>
| _usage:_ | <pre>Prelude> or [False, False, True, False]
True
Prelude> or [False, False, False, False]
False
Prelude> or []
False</pre> |

<a name="OrdPrelude"></a>
| _type:_ | ord :: Char -> Int |
| _description:_ | applied to a character, returns its ascii code as an integer. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> ord 'A'
65
Prelude> (chr (ord 'A')) `eqChar` 'A'
True</pre> |
| _see also:_ | <a href="<a name="ChrPrelude">chr</a> |"></a>

<a name="OrdcharPrelude"></a>
| _type:_ | ordChar :: Char -> Char -> Ordering |
| _description:_ | returns LT if the first argument is less than the second \
			argument, GT if greater, EQ if equal |
| _definition:_ | <pre>ordChar c1 c2 = ordInt (ord c1) (ord c2)</pre> |
| _usage:_ | <pre>Prelude> ordChar 'a' 'b'
LT
List> sortBy ordChar "Helium is cool"
"  Hceiillmoosu"</pre> |
| _see also:_ | <a href="<a name="OrdcharPrelude">ordChar</a>, <a href="#OrdlistPrelude">ordList</a>, \"></a>
			<a href="<a name="OrdstringPrelude">ordString</a>, <a href="#OrdintPrelude">ordInt</a>, \"></a>
			<a href="<a name="OrdfloatPrelude">ordFloat</a> |"></a>

<a name="OrdfloatPrelude"></a>
| _type:_ | ordFloat :: Float -> Float -> Ordering |
| _description:_ | returns LT if the first argument is less than the second \
			argument, GT if greater, EQ if equal |
| _definition:_ | <pre>ordFloat x y
    %VBAR% x <. y    = LT
    %VBAR% x ==. y   = EQ
    %VBAR% otherwise = GT</pre> |
| _usage:_ | <pre>Prelude> ordFloat 3.0 2.5
GT
List> sortBy ordFloat [10.0, -.2.0, 2.5, 0.0, 2.6]
[-2,0,2.5,2.6,10]</pre> |
| _see also:_ | <a href="<a name="OrdcharPrelude">ordChar</a>, <a href="#OrdlistPrelude">ordList</a>, \"></a>
			<a href="<a name="OrdstringPrelude">ordString</a>, <a href="#OrdintPrelude">ordInt</a>, \"></a>
			<a href="<a name="OrdfloatPrelude">ordFloat</a> |"></a>

<a name="OrdintPrelude"></a>
| _type:_ | ordInt :: Int -> Int -> Ordering |
| _description:_ | returns LT if the first argument is less than the second \
			argument, GT if greater, EQ if equal |
| _definition:_ | <pre>ordInt x y
    %VBAR% x < y     = LT
    %VBAR% x == y    = EQ
    %VBAR% otherwise = GT</pre> |
| _usage:_ | <pre>Prelude> ordInt 3 3
EQ
List> sortBy ordInt [10, -2, 3, 0, 4]
[(-2),0,3,4,10]</pre> |
| _see also:_ | <a href="<a name="OrdcharPrelude">ordChar</a>, <a href="#OrdlistPrelude">ordList</a>, \"></a>
			<a href="<a name="OrdstringPrelude">ordString</a>, <a href="#OrdintPrelude">ordInt</a>, \"></a>
			<a href="<a name="OrdfloatPrelude">ordFloat</a> |"></a>

<a name="OrdlistPrelude"></a>
| _type:_ | ordList :: (a -> a -> Ordering) -> [a] -> [a] -> Ordering |
| _description:_ | returns LT if the first argument is less than the second \
			argument, GT if greater, EQ if equal |
| _definition:_ | <pre>ordList _ []     (_:_)  = LT
ordList _ []     []     = EQ
ordList _ (_:_)  []     = GT
ordList ordElem (x:xs) (y:ys) =
    case ordElem x y of
        GT -> GT
        LT -> LT
        EQ -> ordList ordElem xs ys</pre> |
| _usage:_ | <pre>Prelude> ordList ordInt [1,2,3] [1,2,4]
LT
List> sortBy (ordList ordInt) [[1,2],[], [1,0]]
[[],[1,0],[1,2]]</pre> |
| _see also:_ | <a href="<a name="OrdcharPrelude">ordChar</a>, <a href="#OrdlistPrelude">ordList</a>, \"></a>
			<a href="<a name="OrdstringPrelude">ordString</a>, <a href="#OrdintPrelude">ordInt</a>, \"></a>
			<a href="<a name="OrdfloatPrelude">ordFloat</a> |"></a>

<a name="OrdstringPrelude"></a>
| _type:_ | ordString :: String -> String -> Ordering |
| _description:_ | returns LT if the first argument is less than the second \
			argument, GT if greater, EQ if equal |
| _definition:_ | <pre>ordString = ordList ordChar</pre> |
| _usage:_ | <pre>Prelude> ordString "Abc" "abc"
LT
List> sortBy ordString ["helium", "is", "cool" ]
["cool","helium","is"]</pre> |
| _see also:_ | <a href="<a name="OrdcharPrelude">ordChar</a>, <a href="#OrdlistPrelude">ordList</a>, \"></a>
			<a href="<a name="OrdstringPrelude">ordString</a>, <a href="#OrdintPrelude">ordInt</a>, \"></a>
			<a href="<a name="OrdfloatPrelude">ordFloat</a> |"></a>

<a name="PiPrelude"></a>
| _type:_ | pi :: Float |
| _description:_ | the ratio of the circumference of a circle to its diameter. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> pi
3.14159
Prelude> cos pi
-1</pre> |

<a name="PutstrPrelude"></a>
| _type:_ | putStr :: String -> IO () |
| _description:_ | takes a string as an argument and returns an I/O action as a \
			result. A side-effect of applying putStr is that it causes its \
			argument string to be printed to the screen. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> putStr "Hello World\nI'm here!"
Hello World
I'm here!</pre> |

<a name="ProductPrelude"></a>
| _type:_ | product :: [Int] -> Int |
| _description:_ | applied to a list of numbers, returns their product. |
| _definition:_ | <pre>product xs = <a href="<a name="FoldlPrelude">foldl</a> (*) 1 xs</pre> |"></a>
| _usage:_ | <pre>Prelude> product [1..10]
3628800</pre> |

<a name="QuotPrelude"></a>
| _type:_ | quot :: Int -> Int -> Int |
| _description:_ | returns the quotient after dividing the its first integral \
			argument by its second integral argument. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> 16 `quot` 8
2
Prelude> quot 16 9
1</pre> |

<a name="ReadintPrelude"></a>
| _type:_ | readInt :: String -> Int |
| _description:_ | converts a String to an integer |
| _usage:_ | <pre>Prelude> readInt "-123" + 3
(-120)</pre> |

<a name="RemPrelude"></a>
| _type:_ | rem :: Int -> Int -> Int |
| _description:_ | returns the remainder after dividing its first integral \
			argument by its second integral argument. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> 16 `rem` 8
0
Prelude> rem 16 9
7</pre> |
| _notes:_ | The following equality holds: <pre>(x `quot` y)*y + (x `rem` y) == x</pre> |

<a name="RepeatPrelude"></a>
| _type:_ | repeat :: a -> [a] |
| _description:_ | given a value, returns an infinite list of elements the same as \
			the value. |
| _definition:_ | <pre>repeat x
  = xs
  where xs = x:xs</pre> |
| _usage:_ | <pre>Prelude> repeat 12
[12, 12, 12, 12, 12, 12, 12, 12, 12, ...</pre> |

<a name="ReplicatePrelude"></a>
| _type:_ | replicate :: Int -> a -> [a] |
| _description:_ | given an integer (positive or zero) and a value, returns a list \
			containing the specified number of instances of that value. |
| _definition:_ | <pre>replicate n x = <a href="<a name="TakePrelude">take</a> n (<a href="#RepeatPrelude">repeat</a> x)</pre> |"></a>
| _usage:_ | <pre>Prelude> replicate 3 "apples"
["apples", "apples", "apples"]</pre> |

<a name="ReversePrelude"></a>
| _type:_ | reverse :: [a] -> [a] |
| _description:_ | applied to a finite list of any type, returns a list of the \
			same elements in reverse order. |
| _definition:_ | <pre>reverse = <a href="<a name="FoldlPrelude">foldl</a> (<a href="#FlipPrelude">flip</a> (:)) []</pre> |"></a>
| _usage:_ | <pre>Prelude> reverse [1..10]
[10, 9, 8, 7, 6, 5, 4, 3, 2, 1]</pre> |

<a name="RoundPrelude"></a>
| _type:_ | round :: Float -> Int |
| _description:_ | rounds its argument to the nearest integer. |
| _usage:_ | <pre>Prelude> round 3.2
3
Prelude> round 3.5
4
Prelude> round (-.3.2)
-3</pre> |

<a name="ShowintPrelude"></a>
| _type:_ | showInt :: Int -> String |
| _description:_ | returns the textual representation of an integer number |
| _usage:_ | <pre>Prelude> showInt 42
"42"</pre> |

<a name="SignumPrelude"></a>
| _type:_ | signum :: Int -> Int |
| _description:_ | returns the sign (-1, 0 or 1) of a number. |
| _usage:_ | <pre> Prelude> signum (-3)
-1</pre> |

<a name="SignumfloatPrelude"></a>
| _type:_ | signumFloat :: Float -> Int |
| _description:_ | returns the sign (-1, 0 or 1) of a floating-point number. |
| _usage:_ | <pre>Prelude> signumFloat 3.14
1</pre> |

<a name="SinPrelude"></a>
| _type:_ | sin :: Float -> Float |
| _description:_ | the trigonometric sine function, arguments are interpreted to be in radians. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> sin (pi/.2.0)
1
Prelude> ((sin pi)^.2) +. ((cos pi)^.2)
1</pre> |

<a name="SndPrelude"></a>
| _type:_ | snd :: (a, b) -> b |
| _description:_ | returns the second element of a two element tuple. |
| _definition:_ | <pre>snd (_, y) = y</pre> |
| _usage:_ | <pre>Prelude> snd ("harry", 3)
3</pre> |

<a name="SpanPrelude"></a>
| _type:_ | span :: (a -> Bool) -> [a] -> ([a],[a]) |
| _description:_ | given a predicate and a list, splits the list into two lists \
			(returned as a tuple) such that elements in the first list are \
			taken from the head of the list while the predicate is satisfied, \
			and elements in the second list are the remaining elements from \
			the list once the predicate is not satisfied. |
| _definition:_ | <pre>span p [] = ([],[])
span p xs@(x:xs')
  %VBAR% p x = (x:ys, zs)
  %VBAR% otherwise = ([],xs)
    where (ys,zs) = span p xs'</pre> |
| _usage:_ | <pre>Prelude> span isDigit "123abc456"
("123", "abc456")</pre> |

<a name="SplitatPrelude"></a>
| _type:_ | splitAt :: Int -> [a] -> ([a],[a]) |
| _description:_ | given an integer (positive or zero) and a list, splits the list \
			into two lists (returned as a tuple) at the position corresponding \
			to the given integer. If the integer is greater than the length of \
			the list, it returns a tuple containing the entire list as its \
			first element and the empty list as its second element. |
| _definition:_ | <pre>splitAt n xs %VBAR% n <= 0 = ([],xs)
splitAt _ []          = ([],[])
splitAt n (x:xs)      = (x:xs',xs'')
        where (xs',xs'') = splitAt (n-1) xs</pre> |
| _usage:_ | <pre>Prelude> splitAt 3 [1..10]
([1, 2, 3], [4, 5, 6, 7, 8, 9, 10])
Prelude> splitAt 5 "abc"
("abc", "")</pre> |

<a name="SqrtPrelude"></a>
| _type:_ | sqrt :: Float -> Float |
| _description:_ | returns the square root of a number. |
| _definition:_ | <pre>sqrt x = x **. 0.5</pre> |
| _usage:_ | <pre>Prelude> sqrt 16.0
4</pre> |

<a name="SubtractPrelude"></a>
| _type:_ | subtract :: Int -> Int -> Int |
| _description:_ | subtracts its first argument from its second argument. |
| _definition:_ | <pre>subtract = <a href="<a name="FlipPrelude">flip</a> (-)</pre> |"></a>
| _usage:_ | <pre>Prelude> subtract 7 10
3</pre> |

<a name="SumPrelude"></a>
| _type:_ | sum :: [Int] -> Int |
| _description:_ | computes the sum of a finite list of numbers. |
| _definition:_ | <pre>sum xs = <a href="<a name="FoldlPrelude">foldl</a> (+) 0 xs</pre> |"></a>
| _usage:_ | <pre>Prelude> sum [1..10]
55</pre> |

<a name="TailPrelude"></a>
| _type:_ | tail :: [a] -> [a] |
| _description:_ | applied to a non--empty list, returns the list without its \
			first element. |
| _definition:_ | <pre>tail (_:xs) = xs</pre> |
| _usage:_ | <pre>Prelude> tail [1,2,3]
[2,3]
Prelude> tail "helium"
"elium"</pre> |

<a name="TakePrelude"></a>
| _type:_ | take :: Int -> [a] -> [a] |
| _description:_ | applied to an integer (positive or zero) and a list, returns \
			the specified number of elements from the front of the list. If \
			the list has less than the required number of elements, take \
			returns the entire list. |
| _definition:_ | <pre>take n _  %VBAR% n <= 0  = []
take _ []           = []
take n (x:xs)       = x : take (n-1) xs</pre> |
| _usage:_ | <pre>Prelude> take 4 "goodbye"
"good"
Prelude> take 10 [1,2,3]
[1,2,3]</pre> |

<a name="TakewhilePrelude"></a>
| _type:_ | takeWhile :: (a -> Bool) -> [a] -> [a] |
| _description:_ | applied to a predicate and a list, returns a list containing \
			elements from the front of the list while the predicate is \
			satisfied. |
| _definition:_ | <pre>takeWhile p [] = []
takeWhile p (x:xs)
  %VBAR% p x = x : takeWhile p xs
  %VBAR% otherwise = []</pre> |
| _usage:_ | <pre>Prelude> takeWhile (<5) [1, 2, 3, 10, 4, 2]
[1, 2, 3]</pre> |

<a name="TanPrelude"></a>
| _type:_ | tan :: Float -> Float |
| _description:_ | the trigonometric function tan, arguments are interpreted to be \
			in radians. |
| _definition:_ | defined internally. |
| _usage:_ | <pre>Prelude> tan (pi/.4.0)
1.0</pre> |

<a name="TolowerPrelude"></a>
| _type:_ | toLower :: Char -> Char |
| _description:_ | converts an uppercase alphabetic character to a lowercase \
			alphabetic character. If this function is applied to an argument \
			which is not uppercase the result will be the same as the argument \
			unchanged. |
| _definition:_ | <pre>toLower c
    %VBAR% isUpper c =
        chr ( ord c - ord 'A' + ord 'a' )
    %VBAR% otherwise = c</pre> |
| _usage:_ | <pre>Prelude> toLower 'A'
'a'
Prelude> toLower '3'
'3'</pre> |

<a name="ToupperPrelude"></a>
| _type:_ | toUpper :: Char -> Char |
| _description:_ | converts a lowercase alphabetic character to an uppercase \
			alphabetic character. If this function is applied to an argument \
			which is not lowercase the result will be the same as the argument \
			unchanged. |
| _definition:_ | <pre>toUpper c
    %VBAR% isLower c =
        chr ( ord c - ord 'a' + ord 'A' )
    %VBAR% otherwise = c</pre> |
| _usage:_ | <pre>Prelude> toUpper 'a'
'A'
Prelude> toUpper '3'
'3'</pre> |

<a name="TruncatePrelude"></a>
| _type:_ | truncate :: Float -> Int |
| _description:_ | drops the fractional part of a floating point number, returning \
			only the integral part. |
| _usage:_ | <pre>Prelude> truncate 3.2
3
Prelude> truncate (-.3.2)
(-3)</pre> |

<a name="UndefinedPrelude"></a>
| _type:_ | undefined :: a |
| _description:_ | an undefined value. It is a member of every type. |
| _definition:_ | <pre>undefined
   %VBAR% False = undefined</pre> |

<a name="UnlinesPrelude"></a>
| _type:_ | unlines :: [String] -> String |
| _description:_ | converts a list of strings into a single string, placing a \
			newline character between each of them. It is the converse of the \
			function lines. |
| _definition:_ | <pre>unlines [] = []
unlines (l:ls) = l ++ '\n' : unlines ls</pre> |
| _usage:_ | <pre>Prelude> unlines ["helium","is","cool"]
"helium\nis\ncool\n"</pre> |

<a name="UntilPrelude"></a>
| _type:_ | until :: (a -> Bool) -> (a -> a) -> a -> a |
| _description:_ | given a predicate, a unary function and a value, it recursively \
			re--applies the function to the value until the predicate is \
			satisfied. If the predicate is never satisfied until will not \
			terminate. |
| _definition:_ | <pre>until p f x
  %VBAR% p x = x
  %VBAR% otheriwise = until p f (f x)</pre> |
| _usage:_ | <pre>Prelude> until (> 1000) (*2) 1
1024</pre> |

<a name="UnwordsPrelude"></a>
| _type:_ | unwords :: [String] -> String |
| _description:_ | concatenates a list of strings into a single string, placing a \
			single space between each of them. |
| _definition:_ | <pre>unwords [] = ""
unwords [w] = w
unwords (w:ws) = w ++ ' ' : unwords ws</pre> |
| _usage:_ | <pre>Prelude> unwords ["the", "quick", "brown", "fox"]
"the quick brown fox"</pre> |

<a name="WordsPrelude"></a>
| _type:_ | words :: String -> [String] |
| _description:_ | breaks its argument string into a list of words such that each \
			word is delimited by one or more whitespace characters. |
| _definition:_ | <pre>words s =
    case dropWhile isSpace s of
        "" -> []
        s' -> w : words s''
              where w,s'' :: String
                    (w,s'') = break isSpace s'</pre> |
| _usage:_ | <pre>Prelude> words "the quick brown\n\nfox"
["the", "quick", "brown", "fox"]</pre> |

<a name="ZipPrelude"></a>
| _type:_ | zip :: [a] -> [b] -> [(a,b)] |
| _description:_ | applied to two lists, returns a list of pairs which are formed \
			by tupling together corresponding elements of the given lists. If \
			the two lists are of different length, the length of the resulting \
			list is that of the shortest. |
| _definition:_ | <pre>zip xs ys
  = zipWith pair xs ys
  where
  pair x y = (x, y)</pre> |
| _usage:_ | <pre>Prelude> zip [1..6] "abcd"
[(1, 'a'), (2, 'b'), (3, 'c'), (4, 'd')]</pre> |

<a name="ZipwithPrelude"></a>
| _type:_ | zipWith :: (a -> b -> c) -> [a] -> [b] -> [c] |
| _description:_ | applied to a binary function and two lists, returns a list \
			containing elements formed be applying the function to \
			corresponding elements in the lists. |
| _definition:_ | <pre>zipWith z (a:as) (b:bs) = z a b : zipWith z as bs
zipWith _ _ _ = []</pre> |
| _usage:_ | <pre>Prelude> zipWith (+) [1..5] [6..10]
[7, 9, 11, 13, 15]</pre> |

<a name="OpandPrelude"></a>
| _type:_ | (&&) :: Bool -> Bool -> Bool |
| _description:_ | returns the logical conjunction of its two boolean arguments. |
| _usage:_ | <pre>Prelude> True && True
True
Prelude> (3 < 4) && (4 < 5) && False
False</pre> |

<a name="OporPrelude"></a>
| _type:_ | (%VBAR%%VBAR%) :: Bool -> Bool -> Bool |
| _description:_ | returns the logical disjunction of its two boolean arguments. |
| _usage:_ | <pre>Prelude> True %VBAR%%VBAR% False
True
Prelude> (3 < 4) %VBAR%%VBAR% (4 > 5) %VBAR%%VBAR% False
True</pre> |

<a name="IndexPrelude"></a>
| _type:_ | (!!) :: [a] -> Int -> a |
| _description:_ | given a list and a number, returns the element of the list \
			whose position is the same as the number. |
| _usage:_ | <pre>Prelude> [1..10] !! 0
1
Prelude> "a string" !! 3
't'</pre> |
| _notes:_ | the valid subscripts for a list l are: 0 .. (length l) - 1. \
			Therefore, negative subscripts are not allowed, nor are subscripts \
			greater than one less than the length of the list argument. \
			Subscripts out of this range will result in a program error. |

<a name="ConsPrelude"></a>
| _type:_ | (:) :: a -> [a] -> [a] |
| _description:_ | prefixes an element onto the front of a list. |
| _usage:_ | <pre>Prelude> 1:[2,3]
[1,2,3]
Prelude> True:[]
[True]
Prelude> 'h':"elium"
"helium"</pre> |

<a name="AppendPrelude"></a>
| _type:_ | (++) :: [a] -> [a] -> [a] |
| _description:_ | appends its second list argument onto the end of its first list \
			argument. |
| _usage:_ | <pre>Prelude> [1,2,3] ++ [4,5,6]
[1,2,3,4,5,6]
Prelude> "foo " ++ "was" ++ " here"
"foo was here"</pre> |

<a name="ComposePrelude"></a>
| _type:_ | (.) :: (b -> c) -> (a -> b) -> a -> c |
| _description:_ | composes two functions into a single function. |
| _usage:_ | <pre>Prelude> (sqrt . fromInt . sum ) [1,2,3,4,5]
3.87298</pre> |
| _notes:_ | <tt>(f.g.h) x</tt> is equivalent to <tt>f (g (h x))</tt>. |

<a name="StarstarPrelude"></a>
| _type:_ | (**.) :: Float -> Float -> Float |
| _description:_ | raises its first argument to the power of its second argument. |
| _usage:_ | <pre>Prelude> 3.2**.pi
38.6345</pre> |

<a name="HatPrelude"></a>
| _type:_ | (^) :: Int -> Int -> Int |
| _description:_ | raises its first argument to the power of its second argument. |
| _usage:_ | <pre>Prelude> 3^4
81</pre> |

<a name="MulPrelude"></a>
| _type:_ | (*) :: Int -> Int -> Int |
| _description:_ | returns the multiple of its two arguments. |
| _usage:_ | <pre>Prelude> 6 * 2
12</pre> |

<a name="OpdivPrelude"></a>
| _type:_ | (/) :: Int -> Int -> Int |
| _description:_ | returns the result of dividing its first argument by its \
			second. . |
| _usage:_ | <pre>Prelude> 12 / 5
2</pre> |

<a name="AddPrelude"></a>
| _type:_ | (+) :: Int -> Int -> Int |
| _description:_ | returns the addition of its arguments. |
| _usage:_ | <pre>Prelude> 3 + 4
7</pre> |

<a name="SubPrelude"></a>
| _type:_ | (-) :: Int -> Int -> Int |
| _description:_ | returns the substraction of its second argument from its first. |
| _usage:_ | <pre>Prelude> 4 - 3
1
Prelude> 4 - (-3)
7</pre> |

<a name="NePrelude"></a>
| _type:_ | (/=) :: Int -> Int -> Bool |
| _description:_ | is <tt>True</tt> if its first argument is not equal to its \
			second argument, and <tt>False</tt> otherwise. |
| _usage:_ | <pre>Prelude> 3 /= 4
True</pre> |

<a name="EqPrelude"></a>
| _type:_ | (==) :: Int -> Int -> Bool |
| _description:_ | is <tt>True</tt> if its first argument is equal to its second \
			argument, and <tt>False</tt> otherwise. |
| _usage:_ | <pre>Prelude> 3 == 4
False</pre> |
| _see also:_ | <a href="<a name="EqboolPrelude">eqBool</a>, <a href="#EqcharPrelude">eqChar</a>, \"></a>
			<a href="<a name="EqlistPrelude">eqList</a>, <a href="#EqstringPrelude">eqString</a>, \"></a>
			<a href="<a name="EqPrelude">(&#61;&#61;)</a>, <a href="#EqfltPrelude">(&#61;&#61;.)</a> |"></a>

<a name="LtPrelude"></a>
| _type:_ | (<) :: Int -> Int -> Bool |
| _description:_ | returns <tt>True</tt> if its first argument is strictly less \
			than its second argument, and <tt>False</tt> otherwise. |
| _usage:_ | <pre>Prelude> 1 < 2
True</pre> |

<a name="LePrelude"></a>
| _type:_ | (<=) :: Int -> Int -> Bool |
| _description:_ | returns <tt>True</tt> if its first argument is less than or \
			equal to its second argument, and <tt>False</tt> otherwise. |
| _usage:_ | <pre>Prelude> 3 <= 4
True
Prelude> 4 <= 4
True
Prelude> 5 <= 4
False</pre> |

<a name="GtPrelude"></a>
| _type:_ | (>) :: Int -> Int -> Bool |
| _description:_ | returns <tt>True</tt> if its first argument is strictly greater \
			than its second argument, and <tt>False</tt> otherwise. . |
| _usage:_ | <pre>Prelude> 2 > 1
True</pre> |

<a name="GePrelude"></a>
| _type:_ | (>=) :: Int -> Int -> Bool |
| _description:_ | returns <tt>True</tt> if its first argument is greater than or \
			equal to its second argument, and <tt>False</tt> otherwise. |
| _usage:_ | <pre>Prelude> 4 >= 3
True
Prelude> 4 >= 4
True
Prelude> 4 >= 5
False</pre> |

<a name="MulfltPrelude"></a>
| _type:_ | (*.) :: Float -> Float -> Float |
| _description:_ | returns the multiple of its two arguments. |
| _usage:_ | <pre>Prelude> 6.0 * 2.5
15</pre> |

<a name="OpdivfltPrelude"></a>
| _type:_ | (/.) :: Float -> Float -> Float |
| _description:_ | returns the result of dividing its first argument by its \
			second. |
| _usage:_ | <pre>Prelude> 12.0 /. 5.0
2.4</pre> |

<a name="AddfltPrelude"></a>
| _type:_ | (+.) :: Float -> Float -> Float |
| _description:_ | returns the addition of its arguments. |
| _usage:_ | <pre>Prelude> 3.0 +. 4.5
7.5</pre> |

<a name="SubfltPrelude"></a>
| _type:_ | (-.) :: Float -> Float -> Float |
| _description:_ | returns the substraction of its second argument from its first. |
| _usage:_ | <pre>Prelude> 4.0 -. 3.0
1
Prelude> 4.5 -. (-.3.0)
7.5</pre> |

<a name="PowfltPrelude"></a>
| _type:_ | (^.) :: Float -> Int -> Float |
| _description:_ | raises its first argument to the power of its second argument. |
| _usage:_ | <pre>Prelude> 2.5 ^. 3
15.625</pre> |

<a name="NefltPrelude"></a>
| _type:_ | (/=.) :: Float -> Float -> Bool |
| _description:_ | is <tt>True</tt> if its first argument is not equal to its \
			second argument, and <tt>False</tt> otherwise. |
| _usage:_ | <pre>Prelude> 3.0 /=. 4.0
True</pre> |

<a name="EqfltPrelude"></a>
| _type:_ | (==.) :: Float -> Float -> Bool |
| _description:_ | is <tt>True</tt> if its first argument is equal to its second \
			argument, and <tt>False</tt> otherwise. |
| _usage:_ | <pre>Prelude> 3.0 ==. 4.0
False</pre> |
| _see also:_ | <a href="<a name="EqboolPrelude">eqBool</a>, <a href="#EqcharPrelude">eqChar</a>, \"></a>
			<a href="<a name="EqlistPrelude">eqList</a>, <a href="#EqstringPrelude">eqString</a>, \"></a>
			<a href="<a name="EqPrelude">(&#61;&#61;)</a>, <a href="#EqfltPrelude">(&#61;&#61;.)</a> |"></a>

<a name="LtfltPrelude"></a>
| _type:_ | (<.) :: Float -> Float -> Bool |
| _description:_ | returns <tt>True</tt> if its first argument is strictly less \
			than its second argument, and <tt>False</tt> otherwise. . |
| _usage:_ | <pre>Prelude> 1.0 <. 2.0
True</pre> |

<a name="LefltPrelude"></a>
| _type:_ | (<=.) :: Float -> Float -> Bool |
| _description:_ | returns <tt>True</tt> if its first argument is less than or \
			equal to its second argument, and <tt>False</tt> otherwise. |
| _usage:_ | <pre>Prelude> 3.0 <=. 4.0
True
Prelude> 4.0 <=. 4.0
True
Prelude> 5.0 <=. 4.0
False</pre> |

<a name="GtfltPrelude"></a>
| _type:_ | (>.) :: Float -> Float -> Bool |
| _description:_ | returns <tt>True</tt> if its first argument is strictly greater \
			than its second argument, and <tt>False</tt> otherwise. . |
| _usage:_ | <pre>Prelude> 2.0 >. 1.0
True</pre> |

<a name="GefltPrelude"></a>
| _type:_ | (>=.) :: Float -> Float -> Bool |
| _description:_ | returns <tt>True</tt> if its first argument is greater than or \
			equal to its second argument, and <tt>False</tt> otherwise. |
| _usage:_ | <pre>Prelude> 4.0 >=. 3.0
True
Prelude> 4.0 >=. 4.0
True
Prelude> 4.0 >=. 5.0
False</pre> |

