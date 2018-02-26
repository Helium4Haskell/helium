
*The text below still needs to be adapted to the Cabal version of Helium (1.8 and up).*

The Helium compiler was never meant to be used outright by programmers from a terminal.
Instead, it should be used from other programs, such as the interpreter
that is described on this page, or from such remote places as make files and shell
scripts.

If you have used `helium` from the prompt, you will have found that the main drawback of using
it from a terminal, is that you have to tell it everything and all over again: where are
the libraries, where do we log to and so on. Both `Hint` and `texthint` use a configuration file
to remember user defined settings, and make sure these are passed on to the compiler.
This allows us to keep the compiler lean and avoids certain dangers such as implicit settings
that influence the compilation process, e.g., environmental settings.

Below, we first describe the settings in the configuration files, and
then consider how `Hint` can be used. If you have read through the manual
for `texthint`, you shall notice many similarities. However, `Hint`
offers a few more facilities. For example, `Hint` allows you to change the configuration
settings from `Hint` itself.

Before you go on, read the discussion on `hint.conf` over [here](TEXTHINT.md). 

### Invoking Hint

`Hint` is a Java application. First you need to make sure that `Hint`
has been compiled. You can do that by locating the source, and running
`ant dist` in the directory `heliumsystem/hint`. For this to work, you need
to have `ant` and the Sun java compiler installed. Alternatively, you might
try to import the whole thing into `Eclipse` and compile it with `ejc`, but
we never tried that.

When `ant dist` has run to completion, you should have a directory `dist`
in `heliumsystem/hint` that contains the `Hint` jar file, e.g.,
`Hint-1.7.jar`. You can invoke it by typing
`java -jar Hint-1.7.jar ` or whatever other way your operating system allows you
to execute Java jar files. Then you should obtain a window like this:

<img align="middle" alt="" border="0" height="496" src="http://www.cs.uu.nl/people/jur/images/HintStartup.png" width="559" />

If you want, you can move `Hint` to a different, more accessible location,
or you can write a small wrapper script in a location that is part of your
path environment (consult `$PATH` and the manual of your terminal/operating system
for more details).

### Using `Hint`: the basics

`Hint` and `texthint` have a similar repertoire of commands, although `Hint` is a bit more
versatile and advanced.
However, the interface works a bit differently: with `Hint` cannot pass in parameters from the
prompt, for example. On the other hand, it offers a mouse based interface with pull-down menu's,
shortcut keys, and quick buttons for most of the important commands and allows you to make the
compiler settings from inside `Hint` itself.
In `Hint` commands can be typed into the text field at the bottom of the window, the _command area_,
and output will be generated in the large middle window, the _main area_. If you type
`:?` in the command area and press enter, the main area shows

<pre>Prelude&gt; :?
List of commands:
:load   - loads the specified module
:reload             - reloads the current module
:alert [message]    - alert to previous compile (message optional)
:type               - print type of the expression
:info [function]    - view function in online documentation
:edit [row[:col]]   - edit the currently loaded module
:jump               - jump editor to last error location
:quit               - exit the interpreter
:help, :?           - shows available commands
:clear              - clears the screen
Prelude&gt; 
</pre>

All commands may be abbreviated to a colon `:` followed by the first letter of the command;  
additionally, `:?` is an alias for `:help`. In the examples below we always use the abbreviated
form.

Note that each command is displayed in the main area, followed by the result of executing.
This also holds for commands executed by clicking a button. For example, click the leftmost
button above the main area, which should display a browser window. If you take some time to
hover over the button, a helpful hint shall be displayed about its purpose.

Assuming you have a file `Hint.hs` present which contains

<pre>module Hint where

f :: Int -&gt; Int
f x = 2 * x

main = f 2 + 3
</pre>

and load it by choosing it in the file browser, you will see the following result:

<pre>Prelude&gt; :l /Users/jur/tools/heliumsystem/helium/docs/Hint1.hs
Compiling ./Hint1.hs
(6,1): Warning: Missing type signature: main :: Int
Compilation successful with 1 warning
Hint1&gt; 
</pre>

showing that you have just loaded the module `Hello`, that compilation was successful
(note that it might not be compiled if a corresponding, newer `Hello.lvm` was already
present), and that it generates a single warning to indicate that `main` in `Hello.hs`
does not have a type signature.

You can copy and paste the signature from the warning into your source file,
right above the definition of `main` to prevent the warning. Now you can either type

<pre>Hint&gt; :r
Hint&gt;
</pre>

or press the button which is second from the left. Both commands will reload
and, if necessary, recompile the module.

The prompt `Hint&gt;` indicates that all the top-level identifiers defined in
`Hint.hs` are now in scope and can be used at will. For example, typing `main`,
`f 8 + f 9`, and `map f [1,2,3,4]` respectively in the command area and pressing
enter in between yields

<pre>Hint&gt; main
7
Hint&gt; f 8 + f 9
34
Hint&gt; map f [1,2,3,4]
[2,4,6,8]
Hint&gt; 
</pre>

Note that all the functions from the `Prelude`, such as `map`, can be used as well.
Unfortunately, it is not possible to store computed values in variables in the interpreter
and reuse them later. For that you have to copy and paste the previous computation.

If you want to switch to a different module, say `Hint2.hs`, then simply type

<pre>Hint&gt; :l Hint2
Hint2&gt;
</pre>

or `:l Hint2.hs` for that matter. You can also unload the current module, making the `Prelude` your main
module, by simply typing `:l`.

If you want the type of a particular identifier or expression, you can write

<pre>Hint&gt; :t 2 + f 2
2 + f 2 :: Int
Hint&gt;
</pre>

A command new to `Hint` is the alert command, executed by typing `:a`, optionally followed by a message. The  command can be used to alert the people who control the logger to a particular compilation you have just observed. This can be for various reasons: you were surprised the module did or did not successfully compile, you were surprised (in either a good or bad way) to obtain a particular error message. Whatever you think deserves attention, make sure we learn about it by redoing the compile with alert. The command redoes the most recent compilation (even if the file did not change in the meantime). It overrides any `--disable-logging` flag and the logging that is made can be easily distinguished from the usual loggings. Of course, the host and port number that the compiler is going to use should point to a place where a logging server is actually running. We have arranged for such a server, which is the built-in default for the compiler, but it might be that a person who has provided you with this compiler, also has his own server running to collect loggings. In that case,
it is quite likely that the `.hint.conf` configuration supplied to you has different settings for the
logging host or portnumber. Whatever may be the case, remember that using the alert facility can help improve
the compiler (or simply make us feel very very good about ourselves).

From a programmer's point of view, using the `:a` command, is like redoing the previous compile and passing `-b` as an additional option to make sure compilation actually takes place. Of course, it may be that your reason for making us pay attention is due to a subsidiary module to be compiled. However, since all imported modules are passed along and passing `-B` does not help to decide which particular module you want us to pay attention to, we decided to choose the lazy approach. Then it is up to us to find out more. You can give us a bit more information about what you want to draw our attention to by adding a message to the alert command. Like

<pre>Hint&gt; :a Hey "Helium Team", is this right?
</pre>

The command `:e` is optionally followed by a line number, and even more optionally followed
by a column number on that line. The action taken is to start the configured external editor (see below)
and to jump to the given line number and column number in the file which is currently the main module.

If you need more information about a particular identifier from the `Prelude`, say `foldr`, then you can
ask for specific information by typing

<pre>:i foldr
</pre>

This even works for operators provided by the `Prelude`. Like so

<pre>:i +
</pre>

Note that you should not write `(+)` instead of `+`.

If you compiled a program and would like to jump to the last error in the list of errors for this module,
you can type `:j` or click on the right button (third from the right). For example, if you compiled
the following module

<pre>f :: Int
f = 2 3

g :: Int
g = 5 6

main :: Int
main = f + g
</pre>

then you get
<pre>Prelude&gt; :l /Users/jur/Double.hs
(3,5): Type error in application
 expression       : 2 3
 term             : 2
   type           : Int       
   does not match : Int -&gt; Int
 because          : it is not a function

(6,5): Type error in application
 expression       : 5 6
 term             : 5
   type           : Int       
   does not match : Int -&gt; Int
 because          : it is not a function

Compilation failed with 2 errors
</pre>

Then executing `:j` will start the external editor and move your cursor to the position
`(6,5)`. Alternatively, you can first use the right-most or one-but-rightmost button to cycle
to the error location that you actually want to visit. If the right position is highlighted, simply
press enter and the editor will be started and your cursor moved to the right location. Even quicker
might be to simply click on the (bold faced) location that you are interested in.

Note that getting more than one error message in a single compile is a special feature of Helium.
We take some care that these errors are in fact independent.

If you get fed up with working with `Hint` you can terminate with the `:q` command, or use the corresponding button. If you just want a clean slate, type `:c` to clear the screen.

### The configuration dialog

Many settings can be made from `Hint`, all of which will be stored in the `.hint.conf` configuration
file for Hint. Note that this configuration file is also used by `texthint`. On the other hand, `texthint`
does not support making changes to the configuration. Either use `Hint` or a text editor to
change the configuration directly. Below is a snapshot of the current menu.

<img align="middle" alt="" border="0" height="343" src="http://www.cs.uu.nl/people/jur/images/HintConfigureDialog.png" width="546" />

As you can see boolean flags are checkboxes and the all other fields are simple text fields
where you can type the text. As described earlier, if you need to include spaces in the text (some
people put spaces into their paths and filenames), then you need to escape these by preceding them
with a backslash. As a consequence, you also need to precede each backslash you want to type
with a backslash.

It still remains to discuss the three options specific to `Hint`: `fontsize`, `editorcommandlinetemplate` and
`browsercommandlinetemplate`. The first of these is easy: simply set it to an integer, which then specifies
how many pixels your font will be. Experiment if you will.

More complicated are `editorcommandlinetemplate` and `browsercommandlinetemplate`. These flags are used
by the editor to call and editor or browser outside itself. The latter is to display parts of the Helium
website as a helpfacility. The former is to edit the source files you are working on.
The easiest of these is the browser command line.

The idea is that the textfield contains the path to your favourite browser and indicates how an argument
url should be passed to it. The place where the url should be pasted into the text should be indicated
with `%u`. Typically though, it is simply the path to the browser (you may assume the path settings of
your machine) followed by `%u`. If you use Mac OSX, then it works to write

<pre>browsercommandlinetemplate=open -a Firefox %u
</pre>

where you may replace `Firefox` with the name of your favourite browser. Remember though that if the
name of the application contains a space, then you must precede that with a backslash, and similarly
backslashes should be doubled: for example, on a typical Windows machine you probably need something like

<pre>browsercommandlinetemplate=C:\\Program Files\\Internet\ Explorer\\iexplore.exe %u
</pre>

depending somewhat on the exact location and name of Internet Explorer.

The settings for an editor are somewhat more involved, because we have three parameters here:
the name of the source file, and the line and the column to which the editor should go in that file.
The latter two parameters can be used by `Hint` to immediately jump to an error location.

Usually, passing the module name is not a problem, but for each editor, passing in the
line and column information correctly needs to be determined and set. And not all editors
support it. Next for the various existing platforms we shall indicate the invocations
known to us. Feel free to tell us about any invocations that you tried and that worked
for editors not yet mentioned below. Please allow for variations in the name of directories.
Use the information below to more easily determine the exact way of calling your favourite editor.

#### Mac OSX

For invoking the editor `open` can only be used if you do not want `Hint` to jump directly
to locations, because `open` only allows you to pass the file name.

The following are known to work
<pre>open -a jEdit %f
open -a BBEdit %f
open -a TextEdit %f
open -a XCode %f
open -a Aquamacs\ Emacs %f
</pre>

I guess you get the picture.

If you want to jump to locations when invoking the editor, the following have been known
to work:

<pre>java -jar /Applications/jEdit\ 4.2/jedit.jar -reuseview -- %f +line:%r

bbedit +%r %f

/Applications/Aquamacs\ Emacs.app/Contents/MacOS/Aquamacs\ Emacs +%r:%c %f
</pre>

The following should be noted:
   * in case of `bbedit` you must have the commandline version of the editor installed as well \
(our installation of BBEdit asked this on first invocation and then the above works).
   * the drawback of using Aquamacs in this way, is that it opens a new window everytime you ask for an editor.\
This is fortunately not the case for the `jEdit` due to the `-reuseview` parameter.\
As far as we know, such an option does not exist for `Aquamacs`.

#### Linux and Windows


Send [us](mailto:haskell4helium@gmail.com) your findings. Use the above for inspiration.
