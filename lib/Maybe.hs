-----------------------------------------------------------------------------
-- Standard Library: Operations on the Maybe datatype
--
-- Suitable for use with Helium (with overloading)
-----------------------------------------------------------------------------

module Maybe where

isJust            :: Maybe a -> Bool
isJust (Just _)        = True
isJust Nothing         = False

isNothing             :: Maybe a -> Bool
isNothing Nothing      = True
isNothing (Just _)     = False

fromJust              :: Maybe a -> a
fromJust (Just a)      = a
fromJust Nothing       = error "Maybe.fromJust: Nothing"

fromMaybe             :: a -> Maybe a -> a
fromMaybe d Nothing    = d
fromMaybe _ (Just a)   = a

maybeToList           :: Maybe a -> [a]
maybeToList Nothing    = []
maybeToList (Just a)   = [a]

listToMaybe           :: [a] -> Maybe a
listToMaybe []         = Nothing
listToMaybe (a:_)      = Just a
 
catMaybes             :: [Maybe a] -> [a]
catMaybes ms           = [ m | Just m <- ms ]

mapMaybe              :: (a -> Maybe b) -> [a] -> [b]
mapMaybe f             = catMaybes . map f

-----------------------------------------------------------------------------
