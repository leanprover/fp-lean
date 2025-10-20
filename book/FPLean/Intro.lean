import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "Introduction" =>
%%%
htmlSplit := .never
number := false
%%%

Lean is an interactive theorem prover based on dependent type theory.
Originally developed at Microsoft Research, development now takes place at the [Lean FRO](https://lean-fro.org).
Dependent type theory unites the worlds of programs and proofs; thus, Lean is also a programming language.
Lean takes its dual nature seriously, and it is designed to be suitable for use as a general-purpose programming language—Lean is even implemented in itself.
This book is about writing programs in Lean.

When viewed as a programming language, Lean is a strict pure functional language with dependent types.
A large part of learning to program with Lean consists of learning how each of these attributes affects the way programs are written, and how to think like a functional programmer.
_Strictness_ means that function calls in Lean work similarly to the way they do in most languages: the arguments are fully computed before the function's body begins running.
_Purity_ means that Lean programs cannot have side effects such as modifying locations in memory, sending emails, or deleting files without the program's type saying so.
Lean is a _functional_ language in the sense that functions are first-class values like any other and that the execution model is inspired by the evaluation of mathematical expressions.
_Dependent types_, which are the most unusual feature of Lean, make types into a first-class part of the language, allowing types to contain programs and programs to compute types.

This book is intended for programmers who want to learn Lean, but who have not necessarily used a functional programming language before.
Familiarity with functional languages such as Haskell, OCaml, or F# is not required.
On the other hand, this book does assume knowledge of concepts like loops, functions, and data structures that are common to most programming languages.
While this book is intended to be a good first book on functional programming, it is not a good first book on programming in general.

Mathematicians who are using Lean as a proof assistant will likely need to write custom proof automation tools at some point.
This book is also for them.
As these tools become more sophisticated, they begin to resemble programs in functional languages, but most working mathematicians are trained in languages like Python and Mathematica.
This book can help bridge the gap, empowering more mathematicians to write maintainable and understandable proof automation tools.

This book is intended to be read linearly, from the beginning to the end.
Concepts are introduced one at a time, and later sections assume familiarity with earlier sections.
Sometimes, later chapters will go into depth on a topic that was only briefly addressed earlier on.
Some sections of the book contain exercises.
These are worth doing, in order to cement your understanding of the section.
It is also useful to explore Lean as you read the book, finding creative new ways to use what you have learned.

# Getting Lean
%%%
tag := "getting-lean"
%%%

Before writing and running programs written in Lean, you'll need to set up Lean on your own computer.
The Lean tooling consists of the following:

 * {lit}`elan` manages the Lean compiler toolchains, similarly to {lit}`rustup` or {lit}`ghcup`.
 * {lit}`lake` builds Lean packages and their dependencies, similarly to {lit}`cargo`, {lit}`make`, or Gradle.
 * {lit}`lean` type checks and compiles individual Lean files as well as providing information to programmer tools about files that are currently being written.
   Normally, {lit}`lean` is invoked by other tools rather than directly by users.
 * Plugins for editors, such as Visual Studio Code or Emacs, that communicate with {lit}`lean` and present its information conveniently.

Please refer to the [Lean manual](https://lean-lang.org/lean4/doc/quickstart.html) for up-to-date instructions for installing Lean.

# Typographical Conventions
%%%
tag := "typographical-conventions"
%%%

Code examples that are provided to Lean as _input_ are formatted like this:

```anchor add1
def add1 (n : Nat) : Nat := n + 1
```

```anchorTerm add1_7
#eval add1 7
```

The last line above (beginning with {kw}`#eval`) is a command that instructs Lean to calculate an answer.
Lean's replies are formatted like this:

```anchorInfo add1_7
8
```

Error messages returned by Lean are formatted like this:

```anchorError add1_string
Application type mismatch: The argument
  "seven"
has type
  String
but is expected to have type
  Nat
in the application
  add1 "seven"
```

Warnings are formatted like this:

```anchorWarning add1_warn
declaration uses 'sorry'
```

# Unicode
%%%
tag := "unicode"
%%%


Idiomatic Lean code makes use of a variety of Unicode characters that are not part of ASCII.
For instance, Greek letters like {lit}`α` and {lit}`β` and the arrow {lit}`→` both occur in the first chapter of this book.
This allows Lean code to more closely resemble ordinary mathematical notation.

With the default Lean settings, both Visual Studio Code and Emacs allow these characters to be typed with a backslash ({lit}`\`) followed by a name.
For example, to enter {lit}`α`, type {lit}`\alpha`.
To find out how to type a character in Visual Studio Code, point the mouse at it and look at the tooltip.
In Emacs, use {lit}`C-c C-k` with point on the character in question.



# Release history
%%%
tag := "release-history"
number := false
htmlSplit := .never
%%%

## October, 2025
%%%
tag := none
%%%

The book has been updated to the latest stable Lean release (version 4.23.0), and now describes functional induction and the {tactic}`grind` tactic.

## August, 2025
%%%
tag := none
%%%

This is a maintenance release to resolve an issue with copy-pasting code from the book.

## July, 2025
%%%
tag := none
%%%

The book has been updated for version 4.21 of Lean.

## June, 2025
%%%
tag := none
%%%

The book has been reformatted with Verso.

## April, 2025
%%%
tag := none
%%%

The book has been extensively updated and now describes Lean version 4.18.

## January, 2024
%%%
tag := none
%%%

This is a minor bugfix release that fixes a regression in an example program.

## October, 2023
%%%
tag := none
%%%

In this first maintenance release, a number of smaller issues were fixed and the text was brought up to date with the latest release of Lean.

## May, 2023
%%%
tag := none
%%%

The book is now complete! Compared to the April pre-release, many small details have been improved and minor mistakes have been fixed.

## April, 2023
%%%
tag := none
%%%

This release adds an interlude on writing proofs with tactics as well as a final chapter that combines discussion of performance and cost models with proofs of termination and program equivalence.
This is the last release prior to the final release.

## March, 2023
%%%
tag := none
%%%

This release adds a chapter on programming with dependent types and indexed families.

## January, 2023
%%%
tag := none
%%%

This release adds a chapter on monad transformers that includes a description of the imperative features that are available in {kw}`do`-notation.

## December, 2022
%%%
tag := none
%%%

This release adds a chapter on applicative functors that additionally describes structures and type classes in more detail.
This is accompanied with improvements to the description of monads.
The December 2022 release was delayed until January 2023 due to winter holidays.

## November, 2022
%%%
tag := none
%%%
This release adds a chapter on programming with monads. Additionally, the example of using JSON in the coercions section has been updated to include the complete code.

## October, 2022
%%%
tag := none
%%%
This release completes the chapter on type classes. In addition, a short interlude introducing propositions, proofs, and tactics has been added just before the chapter on type classes, because a small amount of familiarity with the concepts helps to understand some of the standard library type classes.

## September, 2022
%%%
tag := none
%%%
This release adds the first half of a chapter on type classes, which are Lean's mechanism for overloading operators and an important means of organizing code and structuring libraries. Additionally, the second chapter has been updated to account for changes in Lean's stream API.

## August, 2022
%%%
tag := none
%%%
This third public release adds a second chapter, which describes compiling and running programs along with Lean's model for side effects.

## July, 2022
%%%
tag := none
%%%
The second public release completes the first chapter.

## June, 2022
%%%
tag := none
%%%
This was the first public release, consisting of an introduction and part of the first chapter.


# About the Author
%%%
tag := "about-the-author"
%%%

David Thrane Christiansen has been using functional languages for twenty years, and dependent types for ten.
Together with Daniel P. Friedman, he wrote [_The Little Typer_](https://thelittletyper.com/), an introduction to the key ideas of dependent type theory.
He has a Ph.D. from the IT University of Copenhagen.
During his studies, he was a major contributor to the first version of the Idris language.
Since leaving academia, he has worked as a software developer at Galois in Portland, Oregon and Deon Digital in Copenhagen, Denmark, and he was the Executive Director of the Haskell Foundation.
At the time of writing, he is employed at the [Lean Focused Research Organization](https://lean-fro.org) working full-time on Lean.

# License
%%%
tag := "license"
%%%

{creativeCommons}

The original version of the book was written by David Thrane Christiansen on contract to Microsoft Corporation, who generously released it under a Creative Commons Attribution 4.0 International License.
The current version has been modified by the author from the original version to account for changes in newer versions of Lean.
A detailed account of the changes can be found in the book's [source code repository](https://github.com/leanprover/fp-lean/).
