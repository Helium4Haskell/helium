-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- SimilarFunctionTable.hs : A table with functions that are very similar.
--
-------------------------------------------------------------------------------

module SimilarFunctionTable ( similarFunctionTable ) where

similarFunctionTable :: [[String]]
similarFunctionTable = 
   [ -- int versus float arithmatic
     [ "+"  , "+."  ]
   , [ "*"  , "*."  ]  
   , [ "-"  , "-."  ] 
   , [ "^"  , "^."  ]
   , [ "div" , "/." ]
     -- int versus float comparison functioons
   , [ ">=" , ">=." ]
   , [ "<=" , "<=." ]
   , [ "==" , "==." ]
   , [ "/=" , "/=." ]
   , [ "<"  , "<."  ]
   , [ ">"  , ">."  ]
     -- binary and n-ary operations 
   , [ "max" , "maximum" ]
   , [ "min" , "minimum" ] 
   , [ "sum" , "+"       ]
   , [ "product", "*"    ]
     -- maybe constructors
   , [ "Just", "Nothing"]
     -- either constructors
   , [ "Left", "Right" ]
     -- tuple functions 
   , [ "fst" , "snd" ]
   , [ "curry" , "uncurry" ]
   , [ "zip", "zip3", "unzip", "unzip3" ]
     -- list functions
   , [ ":"  , "++"  ]
   , [ "foldl", "foldl1", "scanl", "scanl1" ]
   , [ "foldr", "foldr1", "scanr", "scanr1" ]
   , [ "words", "unwords" ]
   , [ "lines", "unlines" ]
   , [ "map", "concatMap" ]
     -- Helium specific functions
   , [ "==", "eqChar", "eqMaybe", "eqBool", "eqList", "eqTuple2", "eqString" ]
   , [ "ordString", "ordChar", "ordInt", "ordList" ]
   , [ "showBool", "showChar", "showFloat", "showInt" 
     , "showString", "showList", "showMaybe", "showEither", "showOrdering"
     , "showUnit", "showTuple2", "showTuple3", "showTuple4", "showTuple5"
     , "showTuple6", "showTuple7", "showTuple8", "showTuple9", "showTuple10"
     ]
   ]
