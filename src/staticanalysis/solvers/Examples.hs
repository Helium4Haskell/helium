-------------------------------------------------------------------------------
--
--   *** The Helium Compiler : Static Analysis ***
--               ( Bastiaan Heeren )
--
-- Examples.hs : Examples of type constraint sets.
--
-------------------------------------------------------------------------------


module Examples where

import Constraints
import ConstraintInfo
import Types
import SolveGreedy

-------------------------------------------------------------------------------
-- Test functions

testAll :: IO ()
testAll = let f i = do putStrLn ("*** Set "++show i++" ***") >> setResults !! (i-1)
              setResults = [ testOne set1, testOne set2, testOne set3
                           , testOne set4, testOne set5, testOne set6
                           , testOne set7, testOne set8, testOne set9
                           ]
          in mapM_ f [1..9]

testOne :: (Show info, ConstraintInfo info) => Constraints info -> IO ()
testOne set = let unique  = maximum (ftv set) + 1
                  options = []
                  (uniqueAtTheEnd, substitution, errors, ioDebug) = 
                     solveGreedy unique options set
              in do putStrLn "--- Constraints ---"
                    putStrLn $ unlines (map show set)
                    putStrLn "--- Errors ---"
                    putStrLn $ unlines (map show errors)

-------------------------------------------------------------------------------
-- Two examples of constraint-information:
--    - String 
--    - MyTypeError 

instance ConstraintInfo String
instance Substitutable  String

data MyTypeError = MyTypeError Int Tp Tp

instance ConstraintInfo MyTypeError
instance Show MyTypeError where
   show (MyTypeError i t1 t2) = "#"++show i++" : "++show t1++" == "++show t2
instance Substitutable  MyTypeError where 
   ftv (MyTypeError i t1 t2)     = ftv [t1,t2]
   sub |-> (MyTypeError i t1 t2) = MyTypeError i (sub |-> t1) (sub |-> t2)

makeInfo :: Int -> (Tp,Tp) -> MyTypeError
makeInfo i (t1,t2) = MyTypeError i t1 t2

fun x xs = foldl TApp (TCon x) xs 
var      = TVar

---------------------------------------------------
--   Examples: ConstraintType sets                                           

set1 :: Constraints String        -- own example
set2 :: Constraints String        -- example from "A simple approach to finding the cause of non-unifiability: Graeme S. Port"
set3 :: Constraints MyTypeError   -- constraintTypes generated from a type-correct Haskell expression
set4 :: Constraints MyTypeError   -- constraintTypes generated from a ill-typed Haskell expression (small change compared to set3) 
set5 :: Constraints String        -- example from "Finding backtrack pointTypes for intTypeelligent backtracking: P.T.Cox"
set6 :: Constraints String        -- idem
set7 :: Constraints String        -- idem
set8 :: Constraints String        -- idem
set9 :: Constraints String        -- paper

set1 = 
   [ Equiv "#1" (var 0) (fun "f" [fun "a" []]) 
   , Equiv "#2" (var 1) (fun "f" [fun "b" []]) 
   , Equiv "#3" (var 2) (fun "f" [fun "a" []])     
   , Equiv "#4" (var 0) (var 1) 
   , Equiv "#5" (var 1) (var 2) 
   , Equiv "#6" (var 0) (var 2)
   ]
   
set2 = 
   [ Equiv "#1" (fun "p" [var 0,fun "h" [var 0]]) 
                (fun "p" [fun "f" [fun "a" [],var 2],fun "h" [var 2]])
   , Equiv "#2" (fun "q" [var 0,var 5]) 
                (fun "q" [var 1,fun "b" []])  
   , Equiv "#3" (fun "r" [fun "a" [],var 2]) 
                (fun "r" [var 4,var 1])
   , Equiv "#4" (fun "s" [var 1,var 3,var 3]) 
                (fun "s" [fun "f" [var 4,var 1],fun "g" [var 4],fun "g" [var 5]])        
   ]
 
set3 = 
   [ var 4  .==. var 1 .->. var 2 .->. var 3 $ makeInfo 0
   , var 8  .==. var 5 .->. var 6 .->. var 7 $ makeInfo 1
   , var 9  .==. var 10 .->. var 11 $ makeInfo 2
   , var 11 .==. var 12 .->. var 13 $ makeInfo 3
   , var 14 .==. var 15 .->. var 16 $ makeInfo 4
   , var 16 .==. var 17 .->. var 18 $ makeInfo 5
   , var 20 .==. var 21 .->. var 22 $ makeInfo 6
   , var 23 .==. var 24 .->. var 25 $ makeInfo 7
   , var 25 .==. var 26 .->. var 27 $ makeInfo 8
   , var 22 .==. var 27 .->. var 28 $ makeInfo 9
   , var 19 .==. var 28 .->. var 29 $ makeInfo 10
   , var 30 .==. var 31 .->. var 32 $ makeInfo 11
   , var 32 .==. var 33 .->. var 34 $ makeInfo 12
   , var 29 .==. var 34 .->. var 35 $ makeInfo 13
   , var 35 .==. var 36 $ makeInfo 14
   , var 18 .==. var 36 $ makeInfo 15
   , var 13 .==. boolType $ makeInfo 16
   , var 33 .==. var 6 $ makeInfo 17
   , var 17 .==. var 6 $ makeInfo 18
   , var 10 .==. var 5 $ makeInfo 19
   , var 31 .==. var 2 $ makeInfo 20
   , var 15 .==. var 2 $ makeInfo 21
   , var 21 .==. var 1 $ makeInfo 22
   , var 0  .==. var 3 .->. var 7 .->. var 36 $ makeInfo 23
   , var 30 .==. var 0 $ makeInfo 24
   , var 14 .==. var 0 $ makeInfo 25
   , var 24 .==. floatType $ makeInfo 26
   , var 12 .==. intType $ makeInfo 27
   , var 26 .==. listType (var 37) $ makeInfo 28
   , var 19 .==. listType (var 38) .->. listType (var 38) .->. listType (var 38) $ makeInfo 29
   , var 9  .==. intType .->. intType .->. boolType  $ makeInfo 30
   , var 8  .==. var 39 .->.  listType (var 39) .->. listType (var 39) $ makeInfo 31 
   , var 4  .==. var 40 .->.  listType (var 40) .->. listType (var 40) $ makeInfo 32 
   , var 23 .==. var 41 .->. listType (var 41) .->. listType (var 41) $ makeInfo 33
   , var 20 .==. var 42 .->. listType (var 42) .->. listType (var 42) $ makeInfo 34
   ] 

set4 = 
   [ var 4  .==. var 1 .->. var 2 .->. var 3 $ makeInfo 0
   , var 8  .==. var 5 .->. var 6 .->. var 7 $ makeInfo 1
   , var 9  .==. var 10 .->. var 11 $ makeInfo 2
   , var 11 .==. var 12 .->. var 13 $ makeInfo 3
   , var 14 .==. var 15 .->. var 16 $ makeInfo 4
   , var 16 .==. var 17 .->. var 18 $ makeInfo 5
   , var 20 .==. var 21 .->. var 22 $ makeInfo 6
   , var 23 .==. var 24 .->. var 25 $ makeInfo 7
   , var 25 .==. var 26 .->. var 27 $ makeInfo 8
   , var 22 .==. var 27 .->. var 28 $ makeInfo 9
   , var 19 .==. var 28 .->. var 29 $ makeInfo 10
   , var 30 .==. var 31 .->. var 32 $ makeInfo 11
   , var 32 .==. var 33 .->. var 34 $ makeInfo 12
   , var 29 .==. var 34 .->. var 35 $ makeInfo 13
   , var 35 .==. var 36 $ makeInfo 14
   , var 18 .==. var 36 $ makeInfo 15
   , var 13 .==. boolType $ makeInfo 16
   , var 31 .==. var 6 $ makeInfo 17
   , var 17 .==. var 6 $ makeInfo 18
   , var 10 .==. var 5 $ makeInfo 19
   , var 33 .==. var 2 $ makeInfo 20
   , var 15 .==. var 2 $ makeInfo 21
   , var 21 .==. var 1 $ makeInfo 22
   , var 0  .==. var 3 .->. var 7 .->. var 36 $ makeInfo 23
   , var 30 .==. var 0 $ makeInfo 24
   , var 14 .==. var 0 $ makeInfo 25
   , var 24 .==. floatType $ makeInfo 26
   , var 12 .==. intType $ makeInfo 27
   , var 26 .==. listType (var 37) $ makeInfo 28
   , var 19 .==. listType (var 38) .->. listType (var 38) .->. listType (var 38) $ makeInfo 29
   , var 9  .==. intType .->. intType .->. boolType $ makeInfo 30
   , var 8  .==. var 39 .->. listType (var 39) .->.  listType (var 39) $ makeInfo 31
   , var 4  .==. var 40 .->. listType (var 40) .->.  listType (var 40) $ makeInfo 32
   , var 23 .==. var 41 .->. listType (var 41) .->. listType (var 41) $ makeInfo 33
   , var 20 .==. var 42 .->. listType (var 42) .->. listType (var 42) $ makeInfo 34
   ]  
   
set5 = 
   [ Equiv "#1" (fun "P" [fun "A" []])  (fun "P" [var 0])
   , Equiv "#2" (fun "R" [var 0,var 1]) (fun "R" [var 3,var 3])
   , Equiv "#3" (fun "M" [var 1])       (fun "M" [var 2])
   , Equiv "#4" (fun "T" [var 2,var 5]) (fun "T" [var 4,var 4])
   , Equiv "#5" (fun "S" [var 5])       (fun "S" [fun "B" []])
   ]     	    
   
set6 = 
   [ Equiv "#1" (fun "F" [var 0]) (fun "G" [var 1])
   , Equiv "#2" (var 0)           (var 1)
   , Equiv "#3" (var 1)           (fun "H" [var 0])
   , Equiv "#4" (fun "A" [])      (fun "B" [])
   ]

set7 = 
   [ Equiv "#1" (fun "H" [fun "F" [var 1], fun "F" [var 1]]) 
                (fun "H" [var 0,fun "F" [fun "A" []]])
   , Equiv "#2" (fun "G" [var 1,var 2]) 
                (fun "G" [fun "K" [var 0],fun "F" [var 5]])
   , Equiv "#3" (fun "G" [fun "K" [var 0],fun "K" [var 2]]) 
                (fun "G" [var 4,var 4])
   , Equiv "#4" (fun "G" [var 1,var 5])
                (fun "G" [var 4,var 4])
   , Equiv "#5" (fun "G" [fun "F" [var 5],fun "K" [var 2]]) 
                (fun "G" [fun "F" [fun "B" []],var 5])
   , Equiv "#6" (fun "H" [var 0,fun "F" [fun "A" []]]) 
                (fun "H" [fun "F" [fun "B" []],fun "F" [var 5]])
   ]

set8 = 
   [ Equiv "#1" (fun "G" [var 7,var 2]) (fun "G" [var 4,fun "F" [var 1,var 1]])
   , Equiv "#2" (fun "F" [var 1,fun "G" [var 7,var 2]]) (var 3)
   , Equiv "#3" (var 3) (fun "F" [fun "H" [var 5],fun "G" [var 0,var 6]])
   , Equiv "#4" (var 3) (var 4)
   , Equiv "#5" (var 4) (fun "F" [var 1,var 1])
   ]   

set9 = 
   [ Equiv  "#1" (var 1)  (var 11)
   , Equiv  "#2" (var 0)  (var 1 .->. var 2)
   , Equiv  "#3" (var 3)  (var 13 .->. var 2)
   , Equiv  "#4" (var 13) (intType)
   , Equiv  "#5" (var 4)  (var 5 .->. var 3)
   , Equiv  "#6" (var 6)  (var 12 .->. var 5) 
   , Equiv  "#7" (var 12) (boolType)
   , Equiv  "#8" (var 7)  (var 10)
   , Equiv  "#9" (var 7)  (var 9)
   , Equiv "#10" (var 6)  (var 7 .->. var 8)
   , Equiv "#11" (var 11) (var 8)
   , Equiv "#12" (var 10) (var 8)
   , Equiv "#13" (var 9)  (boolType)
   , Equiv "#14" (var 4)  (intType .->. intType .->. intType)
   ]
