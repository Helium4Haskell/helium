exOr :: bool -> bool -> bool
exOr b1 b2 =
    (b1 && not b2) || (b2 && not b1)
