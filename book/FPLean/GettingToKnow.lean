import VersoManual
import FPLean.Examples
import FPLean.GettingToKnow.Evaluating
import FPLean.GettingToKnow.Types
import FPLean.GettingToKnow.FunctionsDefinitions
import FPLean.GettingToKnow.Structures
import FPLean.GettingToKnow.DatatypesPatterns
import FPLean.GettingToKnow.Polymorphism
import FPLean.GettingToKnow.Conveniences
import FPLean.GettingToKnow.Summary

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Hello"


#doc (Manual) "Getting to Know Lean" =>
%%%
tag := "getting-to-know"
%%%

According to tradition, a programming language should be introduced by compiling and running a program that displays {moduleTerm}`"Hello, world!"` on the console.
This simple program ensures that the language tooling is installed correctly and that the programmer is able to run the compiled code.

Since the 1970s, however, programming has changed.
Today, compilers are typically integrated into text editors, and the programming environment offers feedback as the program is written.
Lean is no exception: it implements an extended version of the Language Server Protocol that allows it to communicate with a text editor and provide feedback as the user types.

Languages as varied as Python, Haskell, and JavaScript offer a read-eval-print-loop (REPL), also known as an interactive toplevel or a browser console, in which expressions or statements can be entered.
The language then computes and displays the result of the user's input.
Lean, on the other hand, integrates these features into the interaction with the editor, providing commands that cause the text editor to display feedback integrated into the program text itself.
This chapter provides a short introduction to interacting with Lean in an editor, while {ref "hello-world"}[Hello, World!] describes how to use Lean traditionally from the command line in batch mode.

It is best if you read this book with Lean open in your editor, following along and typing in each example. Please play with the
examples, and see what happens!

{include 1 FPLean.GettingToKnow.Evaluating}

{include 1 FPLean.GettingToKnow.Types}

{include 1 FPLean.GettingToKnow.FunctionsDefinitions}

{include 1 FPLean.GettingToKnow.Structures}

{include 1 FPLean.GettingToKnow.DatatypesPatterns}

{include 1 FPLean.GettingToKnow.Polymorphism}

{include 1 FPLean.GettingToKnow.Conveniences}

{include 1 FPLean.GettingToKnow.Summary}
