Here is a list of differences between Helium (with overloading) and Haskell 98.

### Not supported

   * labeled fields in data types (a.k.a. records)
   * `newtype` declarations
   * qualified imports and renaming an imported module with `as`
   * import and export lists, such as `import Prelude(map)`
   * `class`, `instance` and `default` declarations
   * Strictness annotations
   * `n+k` patterns
   * `(,)` and `(,,)` etc. to construct a tuple (type), i.e. you cannot write `(,) 3 4`
   * `[]` as type constructor, i.e. you cannot write `x :: [] Int`
   * literate programming

### Supported but restricted

   * The layout rule is somewhat simpler. [more details](LAYOUTRULE.md)
   * There are five built-in type classes with the following instances:
      * `Num`: `Int`, `Float`
      * `Eq`: `Bool`, `Char`, `Either a b`, `Float`, `Int`, `Maybe a`, `[a]` and tuples
      * `Ord`: `Bool`, `Char`, `Float`, `Int`, `[a]` and tuples
      * `Show`: `Bool`, `Char`, `Either a b`, `Float`, `Int`, `Maybe a`, `Ordering`, `[a]` and tuples
      * `Enum`: `Bool`, `Char`, `Float`, `Int` and `()`
   * Instances for `Show` and `Eq` (and not for other classes) can be derived for data types. These instances are needed to use overloaded functions, such as `show` and <kbd>``</kbd>)
   * If your main function is not of type `IO`, then the value is printed with a `show` function. The show functions can print anything, e.g. functions are printed as `<function>`. Therefore, there is a difference between main ` expression and main ` show expression. In the latter case, the expression must be in the `Show` class.
   * The module system is simple, but powerful enough for the purpose of Helium:
      * Everything is always exported: data types, functions, synonyms, instances.
      * Everything that is imported is exported as well.
      * It is not allowed to import something via two (different) import declarations. This means that if you have a module A and both B and C import A, and then a fourth module D imports both B and C, then you will get clashes for all the names in A. from module A. However, it is not problem in case module A happens to be the Prelude.
      * You can hide functions in an import declaration with hiding, except for the show functions that are generated for a data type. Other entities, such as types and constructors, cannot be hidden.
      * The Prelude is always imported. You can hide functions from the Prelude by explicitly writing an import declaration: import Prelude hiding (map, filter)
   * The following character sequences are supported in characters and strings: \\, \n, \a, \b, \f, \r, \t, \v, \", \'. Other escape sequences, e.g., \030 are not supported.
   * Numeric literals are not overloaded (even when using the `--overloading` flag). Thus, `3` is of type `Int` and `3.0` of type `Float`. A consequence is that you can _never_ write `2 + 2.3`, although in overloaded mode you may write both `2 + 3` and `2.0 + 3.0`.
   * Type variables are always of kind star (*).
   * A more restrictive syntax exists for operator sections. For instance, `(+2*3)` is not allowed, this should be written as `(+(2*3))`.
   * A slightly more restrictive syntax exists for left-hand sides of function definitions. For example, in Helium the parentheses in the following definitions are necessary whereas in Haskell they are not:
<pre>(x:xs) ++ ys ` ... (x:xs) ` ... </pre>
Helium rejects a definition if operator precedence is necessary to understand the left-hand side. See the end of Section 4.4 of the Haskell 98 Report to see why we have done this.
   * Fixity declarations are only allowed at top-level.
   * `Integer` is simply a type synonym for `Int`. This makes programs with the explicit type `Integer` compile but, of course, this does not make them have arbitrary precision.
   * Tuples with more than ten elements are not supported.

### Not in Haskell 98, but available in Helium

   * A show function is generated for each data type and type synonym. For instance, the function `showMaybe` is automatically created for the data type `Maybe`. If the data type has parameters, then the show function gets the necessary additional arguments, e.g. `showMaybe showInt (Just 3)`.