
*The text below still needs to be adapted to the Cabal version of Helium (1.8 and up).*

The Helium compiler was never meant to be used outright by programmers from a terminal.
Instead, it should be used from other programs, such as the textual interpreter `texthint`
that is described on this page, the graphical interpreter [Hint](HINT.md), or
from such remote places as make files and shell scripts.

If you have used `helium` from the prompt, you will have found that the main drawback of using
it from a terminal, is that you have to tell it everything and all over again: where are the libraries,
where do we log to and so on. Both `Hint` and `texthint` use a configuration file
to remember user defined settings, and make sure these are passed on to the compiler.
This allows us to keep the compiler lean and avoids certain dangers such as implicit settings
that influence the compilation process, e.g., environmental settings.

Below, we first describe the settings in the configuration files, and
then consider how `texthint` can typically be used. Although we have tried to make
the usage of `texthint` and `Hint` correspond as closely as possibly,
there are some differences, with `Hint` being the more powerful of the two.
For example, `texthint` does not allow you to change the configuration settings from
the program. You should do that by loading the configuration file into an editor and change it yourself. `Hint` on the other hand offers a menu to do the changing.

### The `.hint.conf` file

*This is out-dated. Currently config files are installed with Cabal.*

As part of the installation procedure of Helium, a configuration file is created
and copied to your home directory. Indeed, every version of Helium that you have
installed may have its own version of the configuration file, like
`.hint-1.7.conf` and the one to which the `.hint.conf` links is the one that
contains the settings the interpreters will use.

The following is a typical content for `.hint.conf`:
<pre>#Hint
#Fri Jun 27 15:17:21 CEST 2008
editorcommandlinetemplate=...
additionalheliumparameters=-v --debug-logger
port=5010
overloadingon=true
loggingon=false
browsercommandlinetemplate=...
basepath=/usr/local/helium-1.7
fontsize=14
temppath=/tmp
host=helium.zoo.cs.uu.nl
lvmpaths=.
</pre>

We shall now consider all settings except `fontsize`, `editorcommandlinetemplate` and
`browsercommandlinetemplate`. These are specific to `Hint` and will be discussed only there.

Comment lines start with `#`, that 's easy enough. All other lines consist of a name (or flag) followed by ``` (you may use spaces here or omit them),  and finally the value you want to set the name to.

The `basepath` is the most important setting. It specifies where the active version of
Helium can be found. This path is used to find the `.lvm` files for
the `Prelude` and other provided libraries. If you have any additional paths where
`.lvm` files may be found you can add them to `lvmpaths`. If you have more than one,
separate them by a `:`. Note that there are defaults for all possible
settings, but they may not be the same for the different interpreters, so it is wise to set them all
explicity by means of the configuration file.

On we go. Sometimes the interpreters need a directory to store some intermediate files. This directory is specified by `temppath`. The value given above is typically good enough, but you can change it if you must.
You can also specify the standard logging behaviour of the interpreters. Use `false` to disable logging, and `true` to enable it. Something similar holds for `overloading`. By changing the setting for `host` and
`port` you can change where you expect a logging server to be listening for compiles. It is typically
set to the standard location for the server hosted by the Helium team. When experimenting with a new host and port,
it is usually a good idea to use the `--debug-logger` setting to see whether logging proceeds correctly.

Any other `helium` compiler parameter can be set by specifying them like so

<pre>additionalheliumparameters=-v -b 
</pre>

As you can see, flags are separated by spaces. So what if you want to use a space in one of the parameters?
The solution is to escape it, by preceding with a backslash: `\` . This implies that backslashes also
need to be escaped and you should write `\\` to obtain a single backslash.

The additional helium parameter settings override any other setting made by the flags discussed above. So if you  enable overloading, but add `--no-overloading` to `additionalheliumparameters`,
then overloading will be turned off.

### Starting `texthint`

If you have installed `texthint` on your system, then probably all you need to
do is to type `texthint` in a terminal, or to locate the texthint executable and run it by clicking on it. (Allow for slight differences depending on your operating system.)

If you use a terminal, but invoking `texthint`  does not work, then
either `texthint` is not available, or the system does not know where it is.
If you do not know yourself where `texthint` is located, then try to locate it by
using facilities like Spotlight (MacOSX), locate (Linux systems) and so on.
Remember that ordinarily `texthint` is installed where the `helium` compiler itself
is installed.

Once you have located `texthint`, there are two options. Either type not just `texthint` but precede the invocation by the path that leads to the executable, e.g.,

<pre>/usr/local/bin/texthint Hello.hs 
</pre>

As you can see you can also pass along the name of a source file to be compiled and loaded on invocation. You can pass along any number of options, but only one file name.

A second option, is to add the path to the executable to your `$PATH` environment variable. Consult the manual of the terminal you are working with or the operating system you work under with to see how that may be done. From now on, I shall assume this is exactly what you have done.

`texthint` will load its settings from the `hint.conf`  file, located in your home
directory. Indeed this is only run-time dependency that needs to satisfied to let `texthint` work correctly. Contrary to versions of Helium before version 1.7, no
other environment settings need to be made.

As explained earlier, you can change the settings by editing the configuration. If you pass additional parameters to `texthint`, then the typical behaviours is that
these override the settings in the  `.hint.conf` file (so if you occassionally want
to use `texthint` differently you do not need to change the configuration file).  
Note that all but the `-P` parameter override the setting from the configuration
file: the `-P` parameter, on the other hand, accumulates its parameters. Please consult [the compiler user manual](COMPILERDOCS.md) for a description of the parameters that you
may pass.

### Using `texthint`

If you happen to be familiar with `ghci` or `hugs`, then using `texthint` should be a
breeze (a light one, because it doesn't have as many facilities and options, not by a
long shot).

First, edit a file called `Hello.hs` and copy the following text into it:
<pre>module Hello where

f :: Int -&gt; Int
f x = 2 * x

main = f 2 + 3
</pre>

Assuming that `texthint` can be located by the shell, we can now execute
<pre>texthint Hello.hs 
</pre>

Typically, the interpreter shows you this:
<pre> _          _ _                 
| |        | (_)                   
| |__   ___| |_ _   _ _ __ ___     -- Welcome to the Helium interpreter --
| '_ \ / _ \ | | | | | '_ ` _ \    ---------------------------------------
| | | |  __/ | | |_| | | | | | |   -- Type an expression to evaluate    --
|_| |_|\___|_|_|\__,_|_| |_| |_|   --    or a command (:? for a list)   --

Compiling ./Hello.hs
(6,1): Warning: Missing type signature: main :: Int
Compilation successful with 1 warning
Hello&gt; 
</pre>

A few things are worth noticing.
First, the prompt indicates the name of the module you have just loaded.
Note that if the filename does not match the module name, an error results; it is allowed to omit the line `module Hello where`, however. The first thing
to do, as you can see from the start screen, is to type `:?` (or `:h`, or, if you
have the time, `:help`) to see the list of available commands.
<pre>Hello&gt; :?
:h, :?           display this help screen
:l     load module
:l               unload module
:r               reload module
:a      alert to previous compile (message optional)
:t   show type of expression
:b               browse definitions in current module
:!      shell command
:q               quit
Hello&gt; 
</pre>

If the file with compiled code, `Hello.lvm` in this case, does not yet exist, or is out of date, the source file is compiled, resulting, in this particular case, in a warning that indicates that  the top-level identifier does not have an explicit type signature. It also says
that compilation was successful (note that an explicit signature is optional, but the
compiler wants to point out, to suggest even, to add the signature anyway).

Now, copy the above signature to the source file, right above the definition of `main`, and type `:r` to reload the module (in fact, and command that starts with
`:r` will initiate a reload, e.g. `:reload` or `:regurgitate`).
<pre>Hello&gt; :r
Compiling ./Hello.hs
Compilation successful
Hello&gt; 
</pre>

If you reload without first editing the file you obtain
<pre>Hello&gt; :r
Hello&gt; 
</pre>

instead, indicating that the interpreter has not done anything. Indeed, `helium`
only recompiles a module, if it finds that the `.lvm` file is out of date
(i.e., its modification date is older than that of the source file). To be precise,
`texthint` is not aware of this: it simply calls `helium` which makes the necessary
checks. In case you wonder about logging in this case: it happens only when
the compiler actually does something, so when a recompile is avoided, then so is
the logging.

The prompt `Hello&gt;` indicates that all the top-level identifiers defined in
`Hello.hs` are now in scope and can be used at will. For example,
<pre>Hello&gt; main
7
Hello&gt; f 8 + f 9
34
Hello&gt; map f [1,2,3,4]
[2,4,6,8]
Hello&gt; 
</pre>

Note that all the functions from the `Prelude` can be used as well.
Also note that it is not possible to store computed values in variables in the interpreter
and reuse them later. For that you have to copy and paste the previous computation.

If you want to switch to a different module, say `Hello2.hs`, then simply type
<pre>Hello&gt; :l Hello2
Hello2&gt;
</pre>

or `:l Hello2.hs` for that matter.
You can also unload a module, making the `Prelude` your main module,
by simply typing `:l`.

Various options of `texthint` can be used to inspect the contents of a module
that has been loaded. For example, the `:b` option lists the identifiers provided by the module and also their types. In this case, the module has to be recompiled, so
possible warnings and errors will be repeated.

When you type `:b` you obtain the following
<pre>Hello&gt; :b
Functions:
   f :: Int -&gt; Int
   main :: Int

Hello&gt; 
</pre>

If you just want the type of a particular identifier or expression, you can write
<pre>Hello&gt; :t 2 + f 2
2 + f 2 :: Int
Hello&gt;
</pre>

A command new to `texthint` is the alert command, executed by typing `:a`, optionally followed by a message. The  command can be used to alert Helium Team to a particular compilation you have just  observed. This can be for various reasons: you were surprised the module did or did not successfully compile, you were surprised (in either a good or bad way) to obtain a particular error message. Whatever you think
deserves our attention, make sure we learn about it by redoing the compile. The command redoes the most recent compilation (even if the file did not change in the meantime). It overrides any `--disable-logging` flag and the logging that is made in a way that makes it easy to distinguish it from the usual loggings. Of course, the host and port number that the compiler is going to use should point to a place where a logging server is actually running. We have arranged for such a server, which is the built-in default for the compiler, but it might be that your lecturer has his own server runing to collect loggings. In any case, using the alert facility can help us improve the compiler or simply make us feel very very good about ourselves.

From a programmer's point of view, using the `:a` command, is like redoing the previous compile and passing `-b` as an additional option to make sure compilation actually takes place. Of course, it may be that your reason for making us pay attention is due to a subsidiary module to be compiled. However, since all imported modules are passed along and passing `-B` does not help to decide which particular module you want us to pay attention to, we decided to choose the lazy approach. Then it is up to us to find out more. You can give us a bit more information about what you want to draw our attention to by adding a message to the alert command. Like
<pre>Hello&gt; :a Hey Helium Team, look at this weird error message.
</pre>

A final, but useful command  is `:!` which allows you to execute a terminal command
directly from the interpreter. For example,
<pre>Hello&gt; :! cat Hello.hs
module Hello where

f :: Int -&gt; Int
f x = 2 * x

main :: Int
main = f 2 + 3

Hello&gt; 
</pre>

If you get fed up with working with `texthint` you can terminate with the
`:q` command.

### Can I change `texthint`?

Sure you can, if you can program Haskell. The program itself can be found in a separate
directory, `texthint` in the source directory of the `helium` compiler. `texthint` is compiled
and installed along with the compiler.