module RecordFail where

{--------------------------------
- Record declarations
--------------------------------}

{-
Multiple constructors same field, strict field
-}
data A = A { a :: Int, b :: !Char }
       | B { a :: Int, c :: Bool }

{-
Static check same label diff type
Should fail
-}
data A1 = A1 { a1 :: Int, b1 :: Char }
        | B1 { a1 :: Bool }

{-
Record with type arguments
-}
data A4 a b = A4 { a4 :: a, b4 :: !b }
            | B4 { a4 :: a }

{--------------------------------
- Selectors
--------------------------------}

{-
Selector should exist already at the toplevel
Should fail
-}
a :: A -> Int
a A{ a = x } = x

{--------------------------------
- Record construction
--------------------------------}
{-
Partial record construction using special method omitting strict field
Should fail
-}
e :: A
e = A { a = 1 }

{--------------------------------
- Record update
--------------------------------}

{-
Record update using fields present disjunctly in multuple constructors
Should fail
-}
i :: A -> A
i x = x { b = '1', c = False }

{-
Record update using fields present in other constructor
Should fail on runtime
-}
j :: A
j = (A 1 '1'){ c = False }

{-
Record update using fields present in neither constructor
Should fail
-}
k :: A -> A
k x = x { a = 1, a1 = False }

{-
Record update using duplicate fields
Should fail
-}
k :: A -> A
k x = x { a = 1, a = False }

{-
Record update without fields
Should fail
-}
k :: A -> A
k x = x {  }

{-
Record update with types more general than given
Should fail
-}
l :: c -> A4 c b
l c = (A4 1 1) { a4 = c }

{--------------------------------
- Record pattern matching
--------------------------------}

{--------------------------------
- Records with type arguments
--------------------------------}
