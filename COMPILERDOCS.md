### The basics

In this short manual, we describe how the Helium compiler can be used, and in particular, describe the parameters that can be
passed to Helium 1.7 (there are some notable differences with earlier versions of Helium).

For purposes of experimentation, start off by creating a file, say `Simple.hs` and enter:

<pre>module Simple where

main  = 2 + 4
</pre>

When you run `helium` from the prompt without any parameter you obtain a short description of the most
often used parameters (and it indicates that an error has occurred, because `helium` really expects a module to be compiled; from now on I shall omit this part of the message).

<pre>Error in invocation: the name of the module to be compiled seems to be missing.

Helium compiler 1.8.1 (... CEST 2015)
Usage: helium [options] file [options]
  -b          --build                 recompile module even if up to date
  -B          --build-all             recompile all modules even if up to date
  -i          --dump-information      show information about this module
  -I          --dump-all-information  show information about all imported modules
              --enable-logging        enable logging, overrides previous disable-logging
              --disable-logging       disable logging (default), overrides previous enable-logging flags
  -a MESSAGE  --alert`MESSAGE         compiles with alert flag in logging; MESSAGE specifies the reason for the alert.
              --overloading           turn overloading on (default), overrides all previous no-overloading flags
              --no-overloading        turn overloading off, overrides all previous overloading flags
  -P PATH     --lvmpath`PATH          use PATH as search path
  -v          --verbose               show the phase the compiler is in
  -w          --no-warnings           do notflag warnings
  -X          --moreoptions           show more compiler options
              --info`NAME             display information about NAME

</pre>

The compiler lists its most important options and its version number.
To compile the program you write:
<pre>helium Simple.hs
</pre>

which typically will result in:
<pre>Compiling Simple.hs
(3,1): Warning: Missing type signature: main :: Int
Compilation successful with 1 warning
</pre>

The default use (although it depends on whether the file hint.conf was modified at any time)
of `helium` allows overloading (ad hoc polymorphism) by means of type classes (like Haskell 98, but in a restricted form,
read [here](DIFFERENCESWITHHASKELL98.md)), so that you can use the same symbol (``) to compare values of different types.
Because of the complications that type classes may give when it comes to error messages, novice programmers can
disallow overloading (pass `--no-overloading` along with the options). To compile the `Simple` module without overloading you  write:
<pre>helium --no-overloading -B Simple.hs
</pre>

The `--no-overloading` flag does as told, and we'll get to the  `-B` option later.

This brings us to a number of useful things to know about the Helium compiler.
The first is that it compiles `.hs` files to `.lvm` files that can then be run
with an interpreter, actually one of two: `lvmrun` and `runhelium`.
In practice, the latter of the two is preferred since you do not need to pass any information
about where to find some Helium's libraries.
If you are familiar with programming Java, then `helium` is like `javac` and `lvmrun` and `runhelium` are
like `java`. If you want to run the result of the previous non-overloaded compilation, you write:
<pre>runhelium --no-overloading Simple.lvm
</pre>

This should print `6` in your terminal. If you forget to pass `--no-overloading` then you
probably get no output. Generally, the behaviour of the interpreter is undefined/unknown.

The interpreter `lvmrun` is more flexible than `runhelium`, so there might be situations where
you prefer to use `lvmrun`. For example,  `lvmrun` supports many parameters (run it
without any to see what they are) but they are typically of a rather technical nature, and we will not look into that here further.

Another thing to note, is that when you run `helium` on a correct Haskell source file twice in succession, without
changing it in the meantime, then it  will say:
<pre>Simple is up to date
</pre>

The reason is that `helium` sees that the `.hs` file is older than the corresponding
`.lvm` file, and therefore sees no need to compile it. However, when we recompiled
`Simple.hs` earlier, the file had not changed, but we wanted
to recompile it with different parameters. This is why we passed along the `-B` option
(`-b` would have worked as well in this case). When passed, the compiler does not perform the check to see
if recompilation is necessary, it simply recompiles. The additional feature of `-B` over `-b`, is that when your
source module also imports other modules, then under `-B` these will also be recompiled,
but not if you only pass `-b`.

The Helium compiler tends to be something of a wise guy. For example, in our compilation, it continues
to complain that `main` does not have a type signature, and it even tells you what it is, by means
of a warning that it provides. To get rid of this and all other possible warnings, write:
<pre>helium -b -w Simple.hs
</pre>

We *strongly* advise against turning the warnings off, and we also advise to write a type signature for every top-level
definition. Other useful warnings that `helium` gives are when you shadow an identifier (e.g., defining a local variable with exactly
the same name as a top-level identifier), when you introduce variables that you never use,
or when you omit a case in a pattern match. Many of these warnings point to real bugs in your code.

For example when you modify `Simple.hs` like so:
<pre>module Simple where

empty []  = 1
emty  xs  = 0

main  = 2 + 4

</pre>

and run
<pre>helium -b Simple.hs</pre>

then you obtain:
<pre>Compiling Simple.hs
(4,7): Warning: Variable "xs" is not used
(3,1): Warning: Missing type signature: empty :: [a] -&gt; Int
(3,1): Warning: Missing pattern in function bindings: 
  empty (_ : _) = ...
(4,1): Warning: Missing type signature: emty :: a -&gt; Int
(6,1): Warning: Missing type signature: main :: Int
Compilation successful with 5 warnings
</pre>

Note how the compiler implicitly informs us that we mispelled `empty`, because
it indicates that we forgot a signature for both `empty` and `emty` and
it says that we omitted the cons pattern case for `empty`.
It also says that `xs` is never used, but in this case that happened to be our intention.

Now, if we change the definition of `main` to `main = 2 ++ 4`, then we obtain:
<pre>Compiling Simple.hs
(4,7): Warning: Variable "xs" is not used
(6,11): Type error in variable
 expression       : ++
   type           : [a] -&gt; [a] -&gt; [a]
   expected type  : Int -&gt; Int -&gt; b  
 probable fix     : use + instead

Compilation failed with 1 error
</pre>

In other words, errors take precedence over warnings (in most cases). Only after
you fix the problem (by deleting the extra `+`) will the warnings come back.

If `helium` seems to behave erratically (you pass parameters to it, but it does not seem to listen) or you simply
want to know what it is up to, then pass the `-v` flag. First off, it will show you what settings
have been made from the command line, and it will show the passes in the compiler so that if things go wrong you get a first indication
of where things go wrong. For example, running `helium -P /usr/local/helium/lib/ -b -v Simple.hs` gives:
<pre>Options after simplification:
--lvmpath`"/usr/local/helium/lib/"
--disable-logging
--overloading
--build
--verbose
Argument: Just "Simple.hs"
Prelude is up to date
Compiling Simple.hs
Lexing...
Parsing...
Importing...
Resolving operators...
Static checking...
(4,7): Warning: Variable "xs" is not used
Type inference directives...
Type inferencing...
(6,11): Type error in variable
 expression       : ++
   type           : [a] -&gt; [a] -&gt; [a]
   expected type  : Int -&gt; Int -&gt; b  
 probable fix     : use + instead

Compilation failed with 1 error
</pre>

The first line shows which additional path is used to search for lvm files, that logging is disabled, overloading is on,
the file must be built, even if it already happens to seem up-to-date, and that the compilation is verbose (duh).
(Note that even if you pass in the abbreviated form of the commands, the long version of the compiler option
is displayed.) Then the compilation process starts as usual, but this time the compiler lists the phases that it is in.

Note that the compiler says `Prelude is up to date`. Why is that? Haskell uses a Prelude that contains many
often used function definitions, like `map` and such. These definitions also need to be compiled, and since
the Prelude is always implicitly imported, the compiler mentions that it is already up to date and does not
need to be recompiled. Typically, the Prelude will only be compiled the first time you run the compiler.

To continue, the type error message hints at replacing `++` with `+` to fix the problem. This is indeed one of the
strong points of `helium`, that it can add this kind of informed hints to the error messages it provides.

You might wonder what happens if you write:
<pre>helium -b -v --no-overloading --overloading Simple.hs
</pre>

In the case of the overloading flags, the last one wins. This rule also applies to other toggle/boolean
flags such as `--enable-logging_` and `--disable-logging`. The rule does _not_ apply to the `-P` option:
every occurrence of the `-P` option _adds_ to the list of known lvm paths. So you can write:
<pre>helium -P /usr/local/helium/lib -P . -b -v --no-overloading --overloading Simple.hs
</pre>

and it will look for additional `.lvm` files in both `.` and `/usr/local/helium/lib`.
Note that the space between the `-P` and the path is optional. If you separate them by a space, then
you can still use tab-completion to look for the right directory (if you happen to use a terminal that
supports tab-completion, of course).

There is one complication with having two modes for compilation: if you run an lvm file compiled
with, say, overloading turned on and run with the libraries with overloading turned off, then you may
obtain some obscure error messages like the following:
<pre>exception: unable to load module "Prelude":
  module doesn't export symbol "$dictNumInt".
</pre>

The solution is to force recompilation of your source modules (the criterium `helium` uses is whether
the `.lvm` file is newer than the source, not that you pass different parameters).

### The logging facility and the alert flag

One of the more innovative features is that every compile can be logged
by the _helium_ compiler to a (logging) server. We have such a server, implemented in Java, that can be obtained
from us on demand; it is not part of the standard Helium system.  The idea of logging is that enough
information is sent to the server, to be able to recreate exactly the logged compilation. This amounts to
sending by means of socket communication, the module, the modules it imports (and so on), a description
of the version of the compiler, and the parameters that were passed to the compiler. More details can be
found in the technical report on the Helium logger in the [publications section]Publications). Our purpose
in logging Helium programs was to be able, at some point, to validate the work we had done on improving
type error messages. Since then we have come to the conclusion that loggings can be used for many other
purposes besides. One of these directly relates to a flag of the compiler as of version 1.7: the `--alert`
flag (or `-a`). Consider the following program:
<pre>
main = 2 +. 4
</pre>

The output with overloading turned on, was at some point that it suggested to
replace `+.` with `++`. A user might consider this to be a bug, because replacing `+.` with `++`
will result in a type error. He can alert the person who manages the server by redoing the compilation
and adding the alert flag. Even if logging is turned off by default, the compiler will attempt to log the compile
this time, and will also make sure that that logging is tagged in a way to make it easy for
the person who manages the logger to find out whether somebody tried to make him aware of certain things.
Besides alerting us to (seemingly) bad error messages, the facility can also be used to alert the manager
to particularly good or clever error messages (by all means, do!).

To come back to the "bug" that the programmer thought he had observed.
Although his reasoning is correct, and we would prefer the type inferencer
to come up with a better suggestion, the type inferencer never comes into play, because `+.` is not
an operator in overloaded mode (it happens to be an operator in non-overloaded mode).
What happens instead is that when you write an identifier/operator that is not
in scope, the compiler will look for identifiers and operators with a similar
name. He will suggest possible replacements, unless these replacements are very
short identifiers (length less than or equal
to one; this is why `+` is not suggested as a replacement). In recent versions
of Helium this has been changed somewhat: the rule is currently that we report all identifiers that differ in
at most one position from the unknown identifier, unless there are too many candidates that qualify. Then no
suggestion is made. In the example this results in the following:
<pre>Compiling Simple.hs
(6,11): Undefined variable "+."
  Hint: Did you mean "+", "++" or "." ?
Compilation failed with 1 error
</pre>

### Advanced flags

Although we have not discussed all the flags that are listed when you run `helium`,
the flags we discussed thus far are likely to be used the most.
In this section, we consider the few remaining flags from the standard help
screen, and then move on to the real advanced flags.
The `-i (--dump-information)` and `-I (--dump-all-information)` flags are
mainly used by the interpreters. By means of these
flags, the interpreters can retrieve the identifiers provided/defined and imported
by a source file, e.g., when you invoke the browse option `:b` in one of the interpreters.
Note that if you already compiled the sources, and did not change them, you
need to pass `-b` in addition to `-i` or `-I` to get this information.
You can also request information about a particular identifier by passing
the option `--info`NAME`. It will tell then you where in the source file
a particular identifier was defined, and what its type is.

Running
<pre>helium -X</pre>

actually gives us a whole host of other flags to
pass to the compiler (all those listed after `--info`NAME`).
<pre>Error in invocation: the name of the module to be compiled seems to be missing.

Helium compiler ...
Usage: helium [options] file [options]
  -b          --build                        recompile module even if up to date
  -B          --build-all                    recompile all modules even if up to date
  -i          --dump-information             show information about this module
  -I          --dump-all-information         show information about all imported modules
              --enable-logging               enable logging, overrides previous disable-logging
              --disable-logging              disable logging (default), overrides previous enable-logging flags
  -a MESSAGE  --alert`MESSAGE                compiles with alert flag in logging; MESSAGE specifies the reason for the alert.
              --overloading                  turn overloading on (default), overrides all previous no-overloading flags
              --no-overloading               turn overloading off, overrides all previous overloading flags
  -P PATH     --lvmpath`PATH                 use PATH as search path
  -v          --verbose                      show the phase the compiler is in
  -w          --no-warnings                  do notflag warnings
  -X          --moreoptions                  show more compiler options
              --info`NAME                    display information about NAME
  -1          --stop-after-parsing           stop after parsing
  -2          --stop-after-static-analysis   stop after static analysis
  -3          --stop-after-type-inferencing  stop after type inferencing
  -4          --stop-after-desugaring        stop after desugaring into Core
  -t          --dump-tokens                  dump tokens to screen
  -u          --dump-uha                     pretty print abstract syntax tree
  -c          --dump-core                    pretty print Core program
  -C          --save-core                    write Core program to file
              --debug-logger                 show logger debug information
              --host`HOST                    specify which HOST to use for logging (default helium.zoo.cs.uu.nl)
              --port`PORT                    select the PORT number for the logger (default: 5010)
  -d          --type-debug                   debug constraint-based type inference
  -W          --algorithm-w                  use bottom-up type inference algorithm W
  -M          --algorithm-m                  use folklore top-down type inference algorithm M
              --no-directives                disable type inference directives
              --no-repair-heuristics         don't suggest program fixes
              --H-fullqualification          to determine fully qualified names for Holmes
</pre>

The options `-1`, `-2`, `-3`, and `-4` can be used to terminate the compilation
process before code is generated. Typically, these are used by people trying to
debug `helium`. The options `-t`, `-u`, `-c` are used for similar
purposes: the compilation process does not transform a program directly
to `lvm` code. Instead, a program is first desugared to `core`
(a slightly sugared lambda calculus), and then transformed to lvm code.
If you want to inspect this intermediate code, you can use the `-C` option.

An important debug option is `-d`, because it shows the internals
of the most innovative part of the compiler: it's type inferencer. By default,
the compiler use a fast and simple type inferencer that solves constraints as
it goes. When it finds an error, however, it reconsiders the part of the program
where inference failed.
It then uses a  type graph data structure to discover what might have caused the
error. This data structure  allows the use of various heuristics that can help
decide the cause of the error, and may suggest program fixes to overcome
the problem.

The `-d` option gives a lot of information to show which constraints are to be
solved, which heuristics have been applied, whether they made a difference,
and so on. To be able to observe the difference between using our type graph
solver and Damas-Milner's algorithm W or the folklore algorithm M, you can
explicitly tell the compiler to use it (by passing `-W` or `-M`).
Furthermore, you can instruct the compiler to never suggest a program
fix with `--no-repair-heuristics`, or to ignore
type inference directives.

One of the problems with the logging facility is that it, necessarily,
communicates with the outside world. For various reasons, the logging facility
may not be working right (there might be an unexpected firewall, the server might
not be turned on, the chosen port number might be taken by another process, and so on).
Therefore, a special debug flag has been provided to get more information about
what the logger is doing, `--debug-logger`.

While we are on the subject of logging: up to version 1.6, `helium` had the name
of the computer that runs the logging server and the port to which the compiler
should connect, hardwired into it. Not anymore. You can change the default
logger server host and the port number to whatever you like (but you might want
to experiment a bit with debugging turned on when you do). The default host to
which the programs are logged can found by looking at the defaults for the flags
`host` and `port` when you run `helium -X`. Note that internal errors of the
compiler are also logged to this combination of host and port.
