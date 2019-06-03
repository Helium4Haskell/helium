Known issues as per June 2nd, 2019.

# Older issues/Failed tests

## Parser tests

* parser/ImportListError
* parser/ImportListError2

Both test files return syntax errors that are different from the expected syntax errors. The new output will have to be judged, and the expected test output might have to change accordingly.

## Static Errors

* staticerrors/DataDupTycon3
* staticerrors/DataDupTycon4

A different but similar error message is returned:

```
(6,11): The occurence of type constructor "Int" is ambiguous. It could refer to: 
	"Int" defined at (5,6)
	"Int" imported from module Prelude (originally defined in "LvmLang")

```

instead of

```
(5,6): Type constructor "Int" clashes with definition in imported module HeliumLang
```

## Type Errors

* typeerrors/Examples/NoInstance2
* typeerrors/Examples/NoInstance
* typeerrors/Examples/NoInstanceEq
* typeerrors/Heuristics/JavaStringConcat
* make/NoEqImport2
* typeClasses/ClassInstaneError1
* typeClasses/ClassInstaneError2

"No instance" error messages are printed twice. Once with type information, and once without type information:

```
Prelude is up to date
Compiling typeerrors/Examples/NoInstance.hs
(3,8): Type error in overloaded variable
 expression       : show
 problem          : A is not an instance of class Show
 hint             : valid instances of Show are Int, Bool, Float, Ordering,
                    Char, Either a b, Maybe a, [a] and tuples

(3,8): Type error in overloaded function
 function         : show
   type           : Show a => a -> String
   used as        :           A -> String
 problem          : A is not an instance of class Show
 hint             : valid instances of Show are Int, Bool, Float, Ordering,
                    Char, Either a b, Maybe a, [a] and tuples

Compilation failed with 2 errors
```

* typeerrors/Examples/TypeBug4
* typeerrors/Examples/TypeBug5
* typeerrors/Heuristics/AppInsert2
* typeerrors/Heuristics/BugReorderTuple
* typeerrors/Heuristics/OrdChr

The error messages have slightly changed, which causes the tests to fail.

## Make

* parser/ImportListError

The position of circular import error messages is displayed as "\<unknown position\>".

## Thompson

* thompson/Thompson23
* thompson/Thompson24

Thompson23 contains the following function

```haskell
empty :: [a] -> Bool
empty as = (as == [])
```

The use of `(==)` means that the type signature should actually be `Eq a => [a] -> Bool`. However, Helium does not recognize this and does not report errors. Thompson24 is very similar.

* thompson/Thompson27

The error message has changed.

## Correct

* correct/Anders

The shadowing of `(+)` is not handled correctly.

## Type classes

* typeClassesStatic/Import

Importing a module that is located in another directory, i.e. importing A.B, which should be located in A/B.hs, does not always seems to work.

## Exports

* exports/Export15
* exports/Export7
* exports/Qual3
* exports/Qual8
* exports/Qual9
* exports/Qual10

These tests all fail, but the causes are not clear at the time of writing.

# New issues

## Overloading

* typeerrors/Examples/Body
* typeerrors/Examples/StatVarBind
* typeerrors/Heuristics/AppNotEnough1
* typeerrors/Heuristics/AppReorder2
* typeerrors/Heuristics/FBHasTooMany1
* typeerrors/Heuristics/FBHasTooMany2
* typeerrors/Heuristics/UnaryMinus1
* thompson/Thompson14
* thompson/Thompson15
* thompson/Thompson28

When a type error occurs within an expression that contains a class member,
the overloading of this expression fails, which results in unsatisfactory error messages.

For example, take Body.hs

```haskell
f :: Int
f = (+)
```

This is obviously incorrect. The current error message looks like 

```
(4,5): Type error in right-hand side
 expression       : (+)
   type           : a -> a -> a
   does not match : Int
```

But we would like something similar to

```
   type           : Num a => a -> a -> a
   does not match : Int        
```

or

```
   type           : Int -> Int -> Int
   does not match : Int        
```

## `show []`

* correct/showFunctions

Helium cannot resolve `show []` if the type of the empty list is not known. Similarly, `show Nothing` does not work either.

## Infix declarations in classes

* typeClassesParse/Nonnesting3

The error message has changed.

## Module export parser

* exports/Export15
* exports/Export8
* exports/Export9

The parser cannot handle exported data types with no data constructors exported. For example:

```haskell
module A( Bool() )
```

causes problems later on, because Helium is now looking for a data type with the name `Bool()`, so including the parentheses.

## INTERNAL ERROR - don't know how to handle DeclCustom: Num

* exports/Export20
* exports/Export21
* exports/Export22
* exports/ExportBasic6

## Data types and classes with same name

* classesQualified/DataClassName

Consider the following two files:

ClassA.hs

```haskell
class A a where
  id2 :: a -> a

```

DataClassName.hs

```haskell
import ClassA

data A = A | B

instance A Int where
  id2 x = x
```

This should result in a static error, because `instance A` could refer to both the data type and the imported class. 
This does not happen, though, and Helium is able to differentiate between these two names, even though it shouldn't.

Likely issue: Helium only compares the qualified names, meaning `ClassA.A` and `DataClassName.A` are compared. Since these
are not equal, the ambiguity is not detected.

## Hiding Classes

* classesQualified/HidingClass

Importing a module but hiding a class currently throws an internal error.