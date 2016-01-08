module TestTypeSynonyms where

type Dier = String
type Beer = Dier
type IJsbeer = Beer
type IJsberen = [IJsbeer]
type Vogel  = Dier
type Kanarie = Vogel
type Vogels = [Vogel]

dier :: Dier
dier = "dier" 

beer :: Beer
beer = "beer"

ijsbeer :: IJsbeer
ijsbeer = "ijsbeer"

ijsberen :: IJsberen
ijsberen = [ijsbeer, ijsbeer]

vogel :: Vogel
vogel = "vogel"

kanarie :: Kanarie 
kanarie = "kanarie"

vogels :: Vogels
vogels = [ kanarie ]

noordpool    = beer : ijsberen           -- [Beer]
duo          = [ijsbeer, ijsbeer]        -- [IJsbeer]
trio         = beer : duo                -- [Beer]
artis        = [vogel, beer] ++ vogels   -- [Dier]
vreemdevogel = kanarie ++ vogel          -- [Char]
