
data T = L | B T T

main :: T -> ()
main (B _       L            ) = ()
main (B _       (B L       _)) = ()
main (B L       _            ) = ()
main (B _       (B (B _ _) _)) = ()
main (B L       (B _       L)) = ()
main (_                      ) = ()
main (B (B L L) (B (B L L) L)) = ()

