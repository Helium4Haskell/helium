
main :: [Bool] -> ()
main []            = ()
main [True, False] = ()
main (False : _)   = ()
main (_     : _)   = ()