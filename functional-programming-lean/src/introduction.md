

Lean is an interactive theorem prover developed at Microsoft Research, based on dependent type theory.
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

Before writing and running programs written in Lean, you'll need to set up Lean on your own computer.
The Lean tooling consists of the following:

 * `elan` manages the Lean compiler toolchains, similarly to `rustup` or `ghcup`.
 * `lake` builds Lean packages and their dependencies, similarly to `cargo`, `make`, or Gradle.
 * `lean` type checks and compiles individual Lean files as well as providing information to programmer tools about files that are currently being written.
   Normally, `lean` is invoked by other tools rather than directly by users.
 * Plugins for editors, such as Visual Studio Code or Emacs, that communicate with `lean` and present its information conveniently.

Please refer to the [Lean manual](https://leanprover.github.io/lean4/doc/quickstart.html) for up-to-date instructions for installing Lean.

# Typographical Conventions

Code examples that are provided to Lean as _input_ are formatted like this:
```lean
{{#example_decl Examples/Intro.lean add1}}

{{#example_in Examples/Intro.lean add1_7}}
```
The last line above (beginning with `#eval`) is a command that instructs Lean to calculate an answer.
Lean's replies are formatted like this:
```output info
{{#example_out Examples/Intro.lean add1_7}}
```
Error messages returned by Lean are formatted like this:
```output error
{{#example_out Examples/Intro.lean add1_string}}
```

# Unicode

Idiomatic Lean code makes use of a variety of Unicode characters that are not part of ASCII.
For instance, Greek letters like `α` and `β` and the arrow `→` both occur in the first chapter of this book.
This allows Lean code to more closely resemble ordinary mathematical notation.

With the default Lean settings, both Visual Studio Code and Emacs allow these characters to be typed with a backslash (`\`) followed by a name.
For example, to enter `α`, type `\alpha`.
To find out how to type a character in Visual Studio Code, point the mouse at it and look at the tooltip.
In Emacs, use `C-c C-k` with point on the character in question.
