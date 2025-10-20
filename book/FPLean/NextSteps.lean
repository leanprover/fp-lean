import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

#doc (Manual) "Next Steps" =>
%%%
tag := "next-steps"
htmlSplit := .never
%%%

This book introduces the very basics of functional programming in Lean, including a tiny amount of interactive theorem proving.
Using dependently-typed functional languages like Lean is a deep topic, and much can be said.
Depending on your interests, the following resources might be useful for learning Lean 4.

# Learning Lean
%%%
tag := "learning-lean"
%%%

Lean 4 itself is described in the following resources:

 * [Theorem Proving in Lean 4](https://lean-lang.org/theorem_proving_in_lean4/) is a tutorial on writing proofs using Lean.
 * [The Lean 4 Manual](https://lean-lang.org/doc/reference/latest/) provides a detailed description of the language and its features.
 * [How To Prove It With Lean](https://djvelleman.github.io/HTPIwL/) is a Lean-based accompaniment to the well-regarded textbook [_How To Prove It_](https://www.cambridge.org/highereducation/books/how-to-prove-it/6D2965D625C6836CD4A785A2C843B3DA) that provides an introduction to writing paper-and-pencil mathematical proofs.
 * [Metaprogramming in Lean 4](https://github.com/arthurpaulino/lean4-metaprogramming-book) provides an overview of Lean's extension mechanisms, from infix operators and notations to macros, custom tactics, and full-on custom embedded languages.
 * [Functional Programming in Lean](https://lean-lang.org/functional_programming_in_lean/) may be interesting to readers who enjoy jokes about recursion.

However, the best way to continue learning Lean is to start reading and writing code, consulting the documentation when you get stuck.
Additionally, the [Lean Zulip](https://leanprover.zulipchat.com/) is an excellent place to meet other Lean users, ask for help, and help others.

# Mathematics in Lean
%%%
tag := none
%%%

A wide selection of learning resources for mathematicians are available at [the community site](https://leanprover-community.github.io/learn.html).

# Using Dependent Types in Computer Science
%%%
tag := none
%%%

Rocq is a language that has a lot in common with Lean.
For computer scientists, the [Software Foundations](https://softwarefoundations.cis.upenn.edu/) series of interactive textbooks provides an excellent introduction to applications of Rocq in computer science.
The fundamental ideas of Lean and Rocq are very similar, and skills are readily transferable between the systems.

# Programming with Dependent Types
%%%
tag := none
%%%

For programmers who are interested in learning to use indexed families and dependent types to structure programs, Edwin Brady's [_Type Driven Development with Idris_](https://www.manning.com/books/type-driven-development-with-idris) provides an excellent introduction.
Like Rocq, Idris is a close cousin of Lean, though it lacks tactics.

# Understanding Dependent Types
%%%
tag := none
%%%

[_The Little Typer_](https://thelittletyper.com/) is a book for programmers who haven't formally studied logic or the theory of programming languages, but who want to build an understanding of the core ideas of dependent type theory.
While all of the above resources aim to be as practical as possible, _The Little Typer_ presents an approach to dependent type theory where the very basics are built up from scratch, using only concepts from programming.
Disclaimer: the author of _Functional Programming in Lean_ is also an author of _The Little Typer_.
