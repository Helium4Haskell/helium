module TicTacToe where

{- BORD -}

type Bord = [Veld]

-- een veld is leeg of bezet door een speler

data Veld = Leeg | Speler Speler

eqVeld :: Veld -> Veld -> Bool
eqVeld Leeg Leeg = True
eqVeld (Speler s1) (Speler s2) = s1 `eqSpeler` s2
eqVeld _ _ = False

-- twee spelers: de computer zet rondjes en de mens kruisjes

data Speler = Computer | Mens

eqSpeler :: Speler -> Speler -> Bool
eqSpeler Computer Computer = True
eqSpeler Mens Mens = True
eqSpeler _ _ = False

-- bekijk inhoud van een veld

inhoud :: Bord -> Int -> Veld
inhoud bord idx = bord !! (idx-1)

-- verander de inhoud van een veld

doeZet :: Bord -> Speler -> Int -> Bord
doeZet bord speler idx = bord `verander` (idx-1, Speler speler)

-- wissel van speler

andereSpeler :: Speler -> Speler
andereSpeler Mens = Computer
andereSpeler Computer = Mens

-- een leeg bord

leegBord :: Bord
leegBord = replicate 9 Leeg

-- zet het bord op het scherm

toonBord :: Bord -> IO ()
toonBord
  = putStr 
  . unlines
  . map (map toonVeld) 
  . groepjes 3

toonVeld :: Veld -> Char
toonVeld (Speler Mens)     = 'X'
toonVeld (Speler Computer) = 'O'
toonVeld Leeg              = '.'

-- bekijk welke zetten allemaal mogelijk zijn

alleZetten :: Bord -> [Int]
alleZetten bord 
  = map snd
  ( filter ((\x -> x `eqVeld` Leeg) . fst) 
  ( zip bord [1..9] ))
  
-- vraag wie er moet beginnen

wieBegint :: IO Speler
wieBegint =
  do { putStrLn "Wie begint? (M)ens of (C)omputer"
     ; tekst <- getLine
     ; let letter :: Char 
           letter = head (dropWhile isSpace tekst)
     ; case toUpper letter of
         'M' -> return Mens
         'C' -> return Computer
         _   -> wieBegint
     }

-- bepaal of de invoer een geldige veldaanduiding 
-- (1..9) bevat. Zo ja, dan wordt dat cijfer opgeleverd.

isGeldigVeld :: String -> Maybe Int
isGeldigVeld string
  | all isSpace string = Nothing
  | otherwise
      = if length zonderSpaties == 1 && 
           isDigit eersteTeken && cijfer /= 0
        then Just cijfer
        else Nothing        
  where
    zonderSpaties :: String
    zonderSpaties = filter (not . isSpace) string
    eersteTeken :: Char
    eersteTeken = head zonderSpaties
    cijfer :: Int
    cijfer = readInt [eersteTeken]

mensZet :: Bord -> IO Bord
mensZet bord = 
  do { putStrLn "Op welk veld (1..9) wil je zetten?"
     ; invoer <- getLine
     ; case isGeldigVeld invoer of
         Nothing -> 
           do { putStrLn "Verkeerde invoer" 
              ; mensZet bord
              }
         Just idx -> 
           do { if not (inhoud bord idx `eqVeld` Leeg)
                then do { putStrLn "Veld is al bezet"
                        ; mensZet bord
                        }
                else do { return (doeZet bord Mens idx) }
              }
     }

computerZet :: Bord -> IO Bord
computerZet bord = 
  do { idx <- return 0 -- randomRIO (0, length zetten-1)
     ; let zet :: Int
           zet =
             case bedenkZet bord of
               Nothing -> zetten !! idx 
               Just goedeZet -> goedeZet
     ; putStrLn ("Ik zet op " ++ showInt zet)
     ; return (doeZet bord Computer zet)
     }
  where
    zetten :: [Int]
    zetten = alleZetten bord

-- Bedenk een zet; als je kan winnen, doe die zet dan; als je 
-- winst van de mens kan voorkomen, doe dat dan. Anders wordt
-- Nothing opgeleverd en wordt een willekeurige zet gedaan

bedenkZet :: Bord -> Maybe Int
bedenkZet bord 
  | length zetten == 1 = Just (head zetten)
  | length gevenWinst > 0 = Just (head gevenWinst)
  | length verhinderenVerlies > 0 = Just (head verhinderenVerlies)
  | otherwise = Nothing
  where
    zetten, verhinderenVerlies, gevenWinst :: [Int]
    zetten = alleZetten bord
    verhinderenVerlies = filter (verhindertVerlies bord) zetten
    gevenWinst = filter (geeftWinst bord) zetten

geeftWinst :: Bord -> Int -> Bool
geeftWinst bord idx 
  = toestandSpel (doeZet bord Computer idx) `eqToestand` ComputerWint

verhindertVerlies :: Bord -> Int -> Bool
verhindertVerlies bord idx
  = toestandSpel (doeZet bord Mens idx) `eqToestand` MensWint

data Toestand = BordVol | MensWint | ComputerWint | NiksBijzonders

eqToestand :: Toestand -> Toestand -> Bool
eqToestand BordVol BordVol = True
eqToestand MensWint MensWint = True
eqToestand ComputerWint ComputerWint = True
eqToestand NiksBijzonders NiksBijzonders = True
eqToestand _ _ = False

toestandSpel :: Bord -> Toestand
toestandSpel bord
  | elemBy (eqMaybe eqSpeler) (Just Computer) allemaal
    = ComputerWint
  | elemBy (eqMaybe eqSpeler) (Just Mens) allemaal
    = MensWint
  | all (not . (eqVeld Leeg)) bord
    = BordVol
  | otherwise
    = NiksBijzonders
  where
    allemaal :: [Maybe Speler]
    allemaal = map (bekijkRijtje bord) alleRijtjes

-- kijkt of een rijtje door een van de spelers helemaal
-- bezet is

bekijkRijtje :: Bord -> [Int] -> Maybe Speler
bekijkRijtje bord rijtje
  | all (eqVeld (Speler Computer)) velden = Just Computer
  | all (eqVeld (Speler Mens))     velden = Just Mens
  | otherwise                       = Nothing
  where
    velden :: [Veld]
    velden = map (inhoud bord) rijtje

alleRijtjes :: [[Int]]
alleRijtjes = [ [1,2,3], [4,5,6], [7,8,9]
              , [1,4,7], [2,5,8], [3,6,9]
              , [1,5,9], [3,5,7]
              ]
  

hoofdLus :: Bord -> Speler -> IO ()
hoofdLus bord speler =
  do { putStrLn "Het bord:"
     ; toonBord bord
     ; case toestandSpel bord of
         BordVol -> do { putStrLn "Bord vol. Remise" }
         MensWint -> do { putStrLn "Je hebt gewonnen! Gefeliciteerd." }
         ComputerWint -> do { putStrLn "Ik heb gewonnen!" }
         NiksBijzonders ->
           do { nieuwBord <- case speler of
                               Mens -> mensZet bord
                               Computer -> computerZet bord
              ; hoofdLus nieuwBord (andereSpeler speler)
              }
     }

main :: IO ()  
main =
  do { putStrLn "Welkom bij boter, kaas en eieren"
     ; speler <- wieBegint
     ; return ()
     ; hoofdLus leegBord speler
     }

{- HULPFUNCTIES -}

-- groepjes 3 [1..10] = [[1,2,3],[4,5,6],[7,8,9], [10]]

groepjes :: Int -> [a] -> [[a]]
groepjes _ [] = []
groepjes n xs = ys : groepjes n zs
  where
    (ys, zs) = splitAt n xs 

-- "abcde" `verander` (1, 'z') = "azcde"

verander :: [a] -> (Int, a) -> [a]
verander xs (n, nieuw) = take n xs ++ [nieuw] ++ drop (n+1) xs
