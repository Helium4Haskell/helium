![Helium Logo](http://www.cs.uu.nl/people/jur/Helium_0300pix.jpg)

### Helium

Helium is a functional programming language (a subset of Haskell) and a
compiler designed especially for teaching. The main developers and
initiators are Arjan van IJzendoorn, Rijk Jan van Haaften, Bastiaan
Heeren and Daan Leijen. Currently, Jurriaan Hage, and Bastiaan Heeren
maintain the compiler and associated tools. For more information about
Helium contact [us](mailto:helium4haskell@gmail.com).

Helium and the runtime lvmrun are on
[Hackage](https://hackage.haskell.org/package/helium). This means that
you can install the latest version of Helium by running
    cabal install helium
    cabal install lvmrun

The former of the two is the compiler (which will probably install a few
more packages, like Top and lvmlib), the second is the run-time. You can
then test the installation by running the program *texthint* and
evaluating a few expressions. The system is known to install with GHC
7.6.3 and GHC 7.8.x.

Other kinds of downloads are not supported anymore, and we advise
against using them.

### LVM

The runtime for Helium is called LVM (the Lazy Virtual Machine), developed
by Daan Leijen and reported on in his PhD thesis. This repository also
includes lvmlib which is the library that is the glue betweene helium and lvmrun.

### Beyond the standard distributions

All software associated with Helium is available from a publicly
available git repository at <https://github.com/Helium4Haskell/>.

These source distributions are to be used at your own risk.

If you think you can do something for us on the above, please contact
[us](mailto:helium4haskell@gmail.com).
