module RecordSuccess where

{--------------------------------
- Record declarations
--------------------------------}

{-
Multiple constructors same field, strict field
-}
data A = A { a :: Int, b :: !Char }
       | B { a :: Int, c :: Bool }

{-
Multiple constructors same field using type synonyms
-}
type Uint = Int
data A2 = A2 { a2 :: Int, b2 :: !Char }
        | B2 { a2 :: Uint }

{-
Record with datatype
-}
data A3 = A3 { a3 :: A, b3 :: !Char }

{-
Record with type arguments
-}
data A4 a b c = A4 { a4 :: a, b4 :: !b }
              | B4 { a4 :: a }

{--------------------------------
- Selectors
--------------------------------}

{-
Selector should exist already at the toplevel
-}
aSel :: A -> Int
aSel = a

{--------------------------------
- Record construction
--------------------------------}

{-
Record construction using regular method
-}
z :: A
z = A 1 '1'

{-
Record construction
-}
d :: A
d = A { a = 1, b = '1' }

{-
Partial record construction using strict field
-}
f :: A
f = A { b = '1' }

{--------------------------------
- Record update
--------------------------------}

{-
Record update using all fields
-}
g :: A -> A
g x = x { a = 1, b = '1' }

{-
Record update using field present in all constructors
-}
h :: A -> A
h x = x { a = 1 }

{--------------------------------
- Record pattern matching
--------------------------------}

{-
Record pattern match in function binding
-}
l :: A -> Int
l A{ a = a } = a

{-
Record nested pattern match in function binding
-}
m :: A3 -> Int
m A3{ a3 = A{ a = a } } = a

{--------------------------------
- Records with type arguments
--------------------------------}

{-
Record construction using record with type arguments
-}
o :: b -> A4 Int b c
o b = A4 { a4 = 1, b4 = b }

{-
Record update using record with type arguments
-}
p :: A4 a b d -> c -> A4 c b d
p x c = x { a4 = c }

{-
Record pattern match using record with type arguments
-}
q :: A4 a b c -> a
q A4{a4=x} = x

{-
Record pattern match using record with type arguments
-}
r :: A4 a b c -> a
r A4{a4=x} = x

{-
Record pattern match with type arguments
-}
n :: A4 a b c -> (a, b)
n A4{ a4 = a, b4 = b } = (a, b)
