Here is a list of differences between Helium (with overloading turned on) and Haskell 98.

### Not supported

   * labeled fields in data types (a.k.a. records)
   * `newtype` declarations
   * Strictness annotations
   * `(,)` and `(,,)` etc. to construct a tuple (type), i.e. you cannot write `(,) 3 4`
   * `[]` as type constructor, i.e. you cannot write `x :: [] Int`
   * literate programming
   * n+k patterns

### Supported but restricted

   * The layout rule is somewhat simpler. [more details](LAYOUTRULE.md)
   * If your main function is not of type `IO`, then the value is printed with a `show` function. The show functions can print anything, e.g. functions are printed as `<function>`. Therefore, there is a difference between main ` expression and main ` show expression. In the latter case, the expression must be in the `Show` class.
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
