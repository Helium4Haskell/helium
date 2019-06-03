# Changes

* Helium now also runs on GHC 8.4 and newer versions. Any `Monoid` instances now also have a `Semigroup` instance.
* `ImportEnvironment` has been extended with a new field:
    
    ```haskell
    classNameEnvironment   :: ClassNameEnvironment

    type ClassNameEnvironment = M.Map Name Name
    ```

    This field maps usable class names to their fully qualified names. an example ClassNameEnvironment could look like
    
    ```haskell
    Show            => Prelude.Show
    Prelude.Show    => Prelude.Show
    Num             => Prelude.Num
    Prelude.Num     => Prelude.Num
    ```

    This environment is used to export and import all classes and instances by their fully qualified names. That way, no ambiguity is possible.
* To convert a `Name` to a fully qualified version, `Helium.Utils.QualifiedTypes` now contains a function `convertClassNameToQualified :: ImportEnvironment -> Name -> Name`. 
* Dictionaries are now exported with fully qualified names. For example:

    ```
    $dictPrelude.Show$LvmLang.Int
    ```
* All classes and instances now have an origin included in the code generation. This way, Helium knows where they originated from when they're imported in another module.
* Deriving `Show` or `Eq` now generates fully qualified code.
* Type directives are now automatically qualified.
* Type error messages involving classes and/or instances get unqualified.

# Installation