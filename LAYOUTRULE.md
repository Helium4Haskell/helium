The layout rule makes the braces and semi-colons you often see in other
languages superfluous. The layout of your program tells the compiler where
definitions and blocks of definitions end. Let us look at an example:</p>

<pre>main = let sieve (x:xs) = x : sieve
                            (filter ((/= 0).(`mod` x)) xs)
           allPrimes = sieve [2..]
       in take 100 allPrimes</pre>


The definitions for <kbd>sieve</kbd> and <kbd>allPrimes</kbd> are indented to
align vertically. This tells the compiler that these are definitions at the same
level. The argument to <kbd>sieve</kbd> on the second line is indented more than
the definition of <kbd>sieve</kbd>, telling the compiler that it is a
continuation of the first line. The keyword <kbd>in</kbd> is indented less than
the definitions and this tells the compiler that the block of definitions has
ended.&nbsp;

The layout rule starts working whenever it sees one of the following keywords: <kbd>do</kbd>,
<kbd>let</kbd>, <kbd>where</kbd>, <kbd>of</kbd>.&nbsp; It also works at
top-level when you don't have a module header. The first symbol it sees after it
is started (the underlined <kbd>sieve</kbd> in the example) determines the
column with which indentation of subsequent lines is compared.&nbsp;</p>

The layout rule in short:
   * same indentation as the first in the block means a new definition/statement/alternative
   * more indentation means that this line belongs to the last line
   * less indentation means end of a block of definitions/statements/alternatives

### The special case of Let-expressions

The layout rule has a special case for <kbd>let</kbd> expressions so that the
keyword <kbd>in</kbd> also ends the block of definitions. This means you can
write:

<pre>main = let divisible x y = x `mod` y == 0 in divisible 10 2</pre>

In the sieve example we could have used this special case and write &quot;<kbd>in
take 100 allPrimes</kbd>&quot; behind &quot;<kbd>sieve [2..]</kbd>&quot; but
that doesn't improve readability.</p>

### Some error messages about wrong layout

Since layout has a meaning in Helium you can also make mistakes that have to do
with layout. In languages where there is no layout, the layout is purely meant
to improve readibility for humans. In the case of Helium, the layout rule takes
over the role of braces and semi-colons and making a layout mistake is like
forgetting a semi-colon or writing too many closing braces. Let us see what
happens:

<pre>main = let sieve (x:xs) = x : sieve 
              (filter ((/= 0).(`mod` x)) xs)
         allPrimes = sieve [2..]
       in take 100 allPrimes
</pre>

In this example <kbd>allPrimes</kbd> is indented less than the first in the
block (<kbd>sieve</kbd>). This means that the block started by <kbd>let</kbd>
ends here. But when a <kbd>let</kbd> block ends there should be the keyword in
and not the name <kbd>allPrimes</kbd>. And that's exactly what Helium tells you:

<pre><font color="#FF0000">(3,10): Syntax error: 
    unexpected variable 'allPrimes'
    expecting keyword 'in'</font>
</pre>

Now the other way around. Let us indent <kbd>allPrimes</kbd> too much:

<pre>main = let sieve (x:xs) = x : sieve 
                            (filter ((/= 0).(`mod` x)) xs)
              allPrimes = sieve [2..]
       in take 100 allPrimes
</pre>

Indenting more means that the line belongs to the previous line, the definition
of <kbd>sieve</kbd> in this case. Therefore, the compiler looks at the
definition of sieve as:</p>

<pre>sieve (x:xs) = x : sieve (filter ((/= 0).(`mod` x)) xs) allPrimes = sieve [2..]</pre>

The variable <kbd>allPrimes</kbd> is okay in this context; it is seen as an
extra parameter to <kbd>sieve</kbd>. If the compiler would get to type checking
this would result in a type error, but the compiler doesn't get to that stage.
The next symbol, the equals sign, comes as a total surprise; it can not occur in
this context:

<pre><font color="#FF0000">(3,25): Syntax error: 
    unexpected '='
    expecting operator, constructor operator, '::', keyword 'where', 
              next in block (based on layout), ';' or 
              end of block (based on layout)</font>
</pre>

The Helium compiler tells you it doesn't expect the '<kbd>=</kbd>' and also
tells you all the things it considers acceptable in this context. You see that
it would consider a <kbd>next in block (based on layout)</kbd> acceptable; in
other words: a new definition that is indented the same. It would also be happy
with an end of block and some other things but not with the '<kbd>=</kbd>'.

### Tabs are Evil

In short, don't use tab characters in your Helium source files. Your editor and
the Helium compiler may interpret tab characters differently. In the Helium
compiler a tab takes you to the next tab stop and tab stops are 8 characters
apart. If your editor has differently sized tab stops, your program may look
okay in your editor, but still the Helium compiler gives layout-related
messages.

The solution is to configure your editor to convert existing and new tabs to
spaces. This way no tab characters will appear in your source code and the
Helium compiler sees the same layout as you do. 

### Differences with Haskell's Layout Rule

The Haskell layout rule is more powerful than the one in Helium. In Haskell, a 
block may also be terminated by a symbol that implies that the end of the block is
reached. Let us look at an example again:

<pre>main = ( case 3 of 4 -&gt; 5
                   3 -&gt; 5, 6 )
</pre>

The layout block started at <kbd>4</kbd> is ended at the comma because a comma
is unexpected here, but if the block is closed here, it is okay to be there. The
value of <kbd>main</kbd> is thus the tuple<kbd> (5, 6)</kbd>. In Helium, to end
a block you really have to start on a new line that is indented less. The
following syntax error is reported:

<pre><font color="#FF0000">(2,26): Syntax error: 
    unexpected ','
    expecting expression, operator, constructor operator, '::', 
              keyword 'where', next in block (based on layout), 
              ';' or end of block (based on layout)</font>
</pre>

The comma is unexpected and suggestions are made what can be expected as this
place. One of those suggestions is an end of block (based on layout) and that's
the one we meant:

<pre>main = ( case 3 of 4 -&gt; 5
                   3 -&gt; 5
       , 6 )
</pre>

Or you can use explicit layout.

### Explicit Layout

You can circumvent the layout rule and use explicit layout with braces and
semi-colons. After the keywords <kbd>do</kbd>, 
<kbd>let</kbd>, <kbd>where</kbd>, <kbd>of </kbd>and at the beginning of a module
you can write an opening brace. Definitions / alternatives / statements can then
be separated by semi-colons and the block is ended by a closing brace. You can
choose explicit layout locally:

<pre>main = ( case 3 of <font color="#008000"><b>{</b></font> 4 -&gt; 5
                   <font color="#008000"><b>;</b></font> 3 -&gt; 5 <font color="#008000"><b>}</b></font>, 6 )
</pre>

or for your whole program:

<pre>{  main = take 100 allPrimes;
sieve (x:xs) = x : sieve(filter ((/= 0).(`mod` x)) xs);
      allPrimes = sieve [2..]
  }
</pre>

As you can see, inside a context of braces layout doesn't matter anymore.

