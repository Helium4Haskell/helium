
main :: Bool -> Bool -> Bool -> ()
main True  False _    = ()
main False _     True = ()
main _     False True = ()
main _     _     _    = ()
