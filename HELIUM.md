There are three ways of working with Helium, each with their own intended audience. First off, there is the standalone
Helium compiler, invoked by running the `helium` program. It's main purpose is to be called from
the more user-friendly interactive tools that are part of the Helium distribution, or to be called from other programs,
batch files, scripts or make files. It is not very user-friendly, because you have to tell it everything it needs to know about all
over again. To actually execute a program, you need to run `lvmrun` on the output of `helium`.

The two other possible ways of working with Helium are by means of `texthint` and `Hint`.
The former is a text-based interactive environment, much like `ghci` and `hugs`, although
with fewer capabilities. The advantage of `texthint` is that is can be used quite easily, and it will be built
along with the Helium compiler. We use `texthint` ourselves to quickly try out a few expressions.

`Hint`, on the other hand, is an interpreter with a graphical interface. It has buttons to be pushed, and pull-down menus.
For the ordinary user, `Hint` is the best choice. An additional advantage of `Hint` is that you can teach it to load
source files that you are working on into your favourite editor. In this way, you can jump directly to the place in your
source file where you made a mistake. The drawback of using `Hint` is that you need Java and Ant on your system to compile
and use it.

For each of the three ways we have a separate manual. The interpreters can pass along parameters of your choice
to the Helium compiler, so even if you are planning to use only the interpreters, it is best to start off by reading
The Basics of the Helium compiler manual first.

   * [The compiler user manual](COMPILERDOCS.md): how to use the Helium compiler.
   * [The texthint user manual](TEXTHINT.md): using the textual interpreter.
   * [The Hint user manual](HINT.md): using the graphical interpreter.

In all cases, the above documentation discuss Helium version 1.7 (including pre-releases). Version 1.7 and higher
differ in quite a few places from versions 1.6 and lower.

Other issues of note:
   * Nice features to have in an editor for Helium are:
      * Syntax colouring for Helium/Haskell
      * Command-line parameters for jumping to a column and line
      * Expand existing and new tab characters to spaces. 
   * [A tour of the Helium Prelude](http://www.staff.science.uu.nl/~hage0101/TOUROFTHEPRELUDE.html): an overview of almost all of the (non-overloaded) Prelude. Each function is clarified by at least its type, examples of its use and a description.
   * [Differences with Haskell '98](DIFFERENCESWITHHASKELL98.md)
