module Calendar where

type Year  = Int
type Month = Int
type Day   = Int

type Date  = (Day,Month,Year)
              
monthNames :: [String]
monthNames = [ "January"   , "February" , "March"    , "April"
             , "May"       , "June"     , "July"     , "August" 
             , "September" , "October"  , "November" , "December"
             ]        
             
isLeapYear :: Year -> Bool
isLeapYear year = year `mod` 4 == 0 
               && not ( year `mod` 100 == 0 && year `mod` 400 /= 0 )

daysInMonth :: Month -> Year -> Int
daysInMonth month year = list !! month
   where
      list :: [Int]
      list     = [31,february,31,30,31,30,31,31,30,31,30,31] 
                            
      february :: Int
      february = if isLeapYear year then 29 else 28
   
calenderMonth :: Month -> Year -> [String]
calenderMonth month year = title : body
   where   
      title :: String
      title = cjustify 22 (monthNames !! month ++ " " ++ showInt year)
      
      body :: [String]
      body = take 7 . map (concat . separateBy " ") . makeGroupsOf 7 
              $ (  ["su","mo","tu","we","th","fr","sa"] 
                ++ replicate firstDayOfMonth "  "
                ++ map (rjustify 2 . showInt) [1..daysInMonth month year] 
                ++ repeat "  "
                )
   
      firstDayOfMonth :: Int
      firstDayOfMonth = sum ( year            -- 365 `mod` 7 == 1
                            : nrOfLeapYears 
                            : [ daysInMonth m year | m <- [0..month-1] ]
                            ) `mod` 7
      
      nrOfLeapYears :: Int
      nrOfLeapYears = (year - 1) `div` 4 
                    - (year - 1) `div` 100 
                    + (year - 1) `div` 400 

showCalenderForYear :: Year -> String
showCalenderForYear year = unlines 
                         . concat 
                         . separateBy horizontal 
                         . map besides 
                         . makeGroupsOf 3 
                         $ map (\month -> calenderMonth month year) [0..11]
   where 
      besides :: [[String]] -> [String]
      besides xxs = foldr1 (zipWith (++)) $ separateBy vertical xxs

      horizontal :: [String]
      horizontal = [concat (separateBy "+" (replicate 3 (replicate 22 '-')))]
 
      vertical :: [String]
      vertical = repeat "|"

separateBy :: a -> [a] -> [a]
separateBy sep xs = sep : concatMap (\x -> [x,sep]) xs

makeGroupsOf :: Int -> [a] -> [[a]]
makeGroupsOf _ [] = []
makeGroupsOf i xs = take i xs : makeGroupsOf i (drop i xs)        

rjustify :: Int -> String -> String
rjustify i s = replicate (i - length s) ' ' ++ s

cjustify :: Int -> String -> String
cjustify i s = let sp :: String
                   sp = replicate ((i - length s) `div` 2) ' '
               in take i (sp ++ s ++ repeat ' ')

main :: IO ()
main = do putStr "See calendar for which year? "
          input <- getLine
          
          let year :: Int
              year = readUnsigned input
              
          if year > 1752            
            then putStrLn (showCalenderForYear year)
            else putStrLn "invalid year (should be >1752)"
