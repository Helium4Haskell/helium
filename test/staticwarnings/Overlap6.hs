
main :: [a] -> ()
main [_, _]    = ()
main (_ : _)   = ()
main [_, _, _] = ()
main _         = ()
