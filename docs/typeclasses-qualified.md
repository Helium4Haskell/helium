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

Prerequistes: Have GHC >= 7.8, cabal and uuagc installed.

1. Open a terminal and navigate to a directory where you wish to clone this repository
2. `git clone git@github.com:Helium4Haskell/helium.git`
3. `git clone git@github.com:Helium4Haskell/Top.git`
4. `git clone git@github.com:Helium4Haskell/lvm.git`
5. `cd lvm/src/lib`
6. `cabal install`
7. `cd ../runtime`
8. `cabal install`
9. `cd ../../../helium`
10. `cabal sandbox init`
11. `cabal sandbox add-source ../Top/`
12. `cabal sandbox add-source ../lvm/src/lib/`
13. `./compile`
14. `cd lib`
15. `coreasm LvmLang`
16. `coreasm LvmIO`
17. `coreasm LvmException`
18. `coreasm HeliumLang`
19. `coreasm PreludePrim`
20. `../dist/dist-sandbox-*/build/helium/helium Prelude.hs`
21. `../dist/dist-sandbox-*/build/helium/helium List.hs`
22. `../dist/dist-sandbox-*/build/helium/helium Maybe.hs`
23. `../dist/dist-sandbox-*/build/helium/helium Char.hs`