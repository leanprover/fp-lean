Lean is an interactive theorem prover developed at Microsoft
Research, based on dependent type theory. Dependent type theory unites
the worlds of programs and proofs; thus, Lean is also a programming
language. Lean is even implemented in itself.

This book is about using Lean for programming, rather than for
mathematics.

# Getting Lean

Before writing and running programs written in Lean, you'll need to
set up Lean on your own computer. The Lean tooling consists of the
following:

 * `elan` manages the Lean compiler toolchains, similarly to =rustup=
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
