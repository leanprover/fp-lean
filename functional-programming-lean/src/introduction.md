Lean is an interactive theorem prover developed at Microsoft
Research, based on dependent type theory. Dependent type theory unites
the worlds of programs and proofs; thus, Lean is also a programming
language. Lean is even implemented in itself.

When viewed as a programming language, Lean is a strict pure
functional language with dependent types. A large part of learning to
program with Lean consists of learning how each of these attributes
affects the way programs are written, and how to think like a
functional programmer. Strictness means that function calls in Lean
work similarly to the way they do in most languages: the arguments are
fully computed before the function's body begins running. Purity means
that Lean programs cannot have side effects such as modifying
locations in memory, sending emails, or deleting files without the
program's type saying so. Lean is a functional language in the sense
that functions are first-class values like any other and that the
execution model is inspired by the evaluation of mathematical
expressions. Dependent types, which are the most unusual feature of
Lean, make types into a first-class part of the language, allowing
types to contain programs and programs to compute types.

# Getting Lean

Before writing and running programs written in Lean, you'll need to
set up Lean on your own computer. The Lean tooling consists of the
following:

 * `elan` manages the Lean compiler toolchains, similarly to `rustup`
   or `ghcup`.
 * `lake` builds Lean packages and their dependencies, similarly to
   `cargo` or `cabal`.
 * `lean` type checks and compiles individual Lean files as well as
   providing information about files that currently being written
   using LSP.

# About the Book

This book builds concepts linearly.

Every chapter contains enough information to build and run example
code, and there are always exercises that can be completed using only
the information provided in the book so far.
