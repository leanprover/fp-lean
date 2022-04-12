According to tradition, a programming language should be introduced by
compiling and running a program that displays `"Hello, world!"` on the
console. This simple program ensures that the language tooling is
installed correctly and that the programmer is able to run the
compiled code.

Since the 1970s, however, programming has changed. Today, compilers
are typically integrated into text editors, and the programming
environment offers feedback as the program is written. Lean is no
exception: it implements an extended version of the Language Server
Protocol that allows it to communicate with a text editor and provide
feedback as the user types.

This chapter provides a short introduction to interacting with Lean in
an editor, while [Hello, World!]() describes how to use Lean traditionally
from the command line in batch mode. Many languages offer a
read-eval-print-loop (REPL), also known as an interactive toplevel, in
which expressions or statements can be entered. The language then
computes and displays the result of the user's input. Lean, on the
other hand, integrates these features into the interaction with the
editor, providing commands that cause the text editor to display
feedback in the program.

It is best if you read this book with Lean open in your editor,
following along and typing in each example. Please play with the
examples, and see what happens!

