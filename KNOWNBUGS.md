
Recent experiences have shown that the behaviour of the LVM runtime system is not as it should be
when it comes to file I/O. We are currently aware of two mistakes.
If you know of any other bugs, either in the compilation process, the functionality of the system,
or in the documentation, we seriously want to know, and would be extremely happy if you
could  [contact us](mail:helium4haskell@gmail.com).

We try to fix the bugs we discover, but we do not have the necessary expertise in our team to deal with
all of them, especially those that deal with the behaviour of the lvm runtime.

### Bug 1: segmentation fault when attempting to write "large" files.

The LVM runtime system will terminate with a segmentation fault  when you try to write files of more than
An example is `heliumsystem-X/helium/test/correct/PrintLargeFile.hs`. This program should print itself,
but terminates. The source of the bug might be in the garbage collector of `lvmrun` which was borrowed
from the OCaml runtime system when it was built.

Known work-around: pass the parameter `-h16m` to `lvmrun`. However, this might reveal
another bug, namely Bug 2 (see below).

### Bug 2: no writing occurs when attempting to write "small" files.

When the initial heap of `lvmrun` is set 8m or higher, then
it is possible that when writing small files, nothing is ever output.
The work-around in this case is to set the heap with `-h7m`, but then you might run into
Bug 1 (see above). We conjecture that this problem is caused by the omission of a flush at some point.

### Bug 3: type inferencer loops or leaks

There are situations in which the type inferencer seems to loop when it uses the type graph
solver. Some experimentation has shown that it simply takes a lot of memory to solve the
problem. The program is small, but not simple.

### Bug 4: type synonyms in warnings unfolded

We do our best not to unfold type synonyms in error messages, and we don't unless we have to.
However, this is, unexpectedly, not the case for warnings that involve type synonyms.
This is why the test for `staticwarnings/TestTypeSynonyms.hs` fails. Although not essential,
we would like to remedy this inconsistency.

### Bug 5: errors in dictionary passing/construction

Since Helium 1.9, this bug has been fixed (see resolved bugs listed at the bottom).

### Bug 6: UTF-8 encoding problems

Some versions of Helium have a problem reading UTF-8 encoded source files.

A typical error message you might get is

<pre>Compiling ./Hello.hs
(1,1): Unexpected character '•'
Compilation failed with 1 error
</pre>

This problem should go away by telling your editor to change the encoding to ANSI.

Thank you _Marvin Hernandez_ for pointing this out to us.

### Bug 7: can not fixup code references beyond a 4gb memory span.

If, after invoking lvmrun or using an interpreter such as Hint or texthint, you get the message

<pre>can not fixup code references beyond a 4gb memory span.
</pre>

then during compilation there is likely to have been an unobserved problem with gcc.
The problem is due to a mismatch between 32 bits and 64 bits lvmrun and helium
implementations.

As far as we know this problem only shows up under MacOSX, and the problem has
been fixed for that platform. Please retrieve from the website a version of Helium
dated later than Sep 30, 2010, or checkout the current head.
If you have the same problem on another platform, please let us know, and we can fix that too.

The above problem seems to have resurfaced, because recent versions of gcc on Macosx
refuse to compile for 32 bit at all.

## Older resolved bugs

### Bug 5: errors in dictionary passing/construction

The code generation for a program like the following was shown to be buggy by _Erik Mulder_.
<pre>test :: Ord a =&gt; a -&gt; a -&gt; String
test x y
   | x &lt; y = "smaller"
   | x == y = "equal"
   | x &gt; y = "larger"
   | otherwise = "buggy"
</pre>

Now, running `test [3] [3]` will actually return `"buggy"`.
