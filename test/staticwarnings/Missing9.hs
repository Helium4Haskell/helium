
data T = L | B T T

main :: T -> ()
main t = case t of B _ L             -> ()
                   L                 -> ()
                   B _ (B L       L) -> ()
                   B L _             -> ()
                   B _ (B (B _ _) _) -> ()
