# Next Steps

This book introduces the very basics of functional programming in Lean, including a tiny amount of interactive theorem proving.
Using dependently-typed functional languages like Lean is a deep topic, and much can be said.
Depending on your interests, the following resources might be useful for learning Lean 4.

## Learning Lean

Lean 4 itself is described in the following resources:

 * [Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/) is a tutorial on writing proofs using Lean.
 * [The Lean 4 Manual](https://leanprover.github.io/lean4/doc/) provides a reference for the language and its features. At the time of writing, it is still incomplete, but it describes many aspects of Lean in greater detail than this book.
 * [How To Prove It With Lean](https://djvelleman.github.io/HTPIwL/) is a Lean-based accompaniment to the well-regarded textbook [_How To Prove It_](https://www.cambridge.org/highereducation/books/how-to-prove-it/6D2965D625C6836CD4A785A2C843B3DA#overview) that provides an introduction to writing paper-and-pencil mathematical proofs.
 * [Metaprogramming in Lean 4](https://github.com/arthurpaulino/lean4-metaprogramming-book) provides an overview of Lean's extension mechanisms, from infix operators and notations to macros, custom tactics, and full-on custom embedded languages.

However, the best way to continue learning Lean is to start reading and writing code, consulting the documentation when you get stuck.
Additionally, the [Lean Zulip](https://leanprover.zulipchat.com/) is an excellent place to meet other Lean users, ask for help, and help others.

## The Standard Library

Out of the box, Lean itself includes a fairly minimal library.
Lean is self-hosted, and the included code is just enough to implement Lean itself.
For many applications, a larger standard library is needed.

[std4](https://github.com/leanprover/std4) is an in-progress standard library that includes many data structures, tactics, type class instances, and functions that are out of scope for the Lean compiler itself.
To use `std4`, add the following to the top level of your `lakefile.lean`:
```lean
require std from git "https://github.com/leanprover/std4" @ "main"
```


## Mathematics in Lean

Most resources for mathematicians are now available in Lean 4, now that the port of mathlib from Lean 3 is complete.
A wide selection are available at [the community site](https://leanprover-community.github.io/learn.html).

## Using Dependent Types in Computer Science

Coq is a language that has a lot in common with Lean.
For computer scientists, the [Software Foundations](https://softwarefoundations.cis.upenn.edu/) series of interactive textbooks provides an excellent introduction to applications of Coq in computer science.
The fundamental ideas of Lean and Coq are very similar, and skills are readily transferable between the systems.

## Programming with Dependent Types

For programmers who are interested in learning to use indexed families and dependent types to structure programs, Edwin Brady's [_Type Driven Development with Idris_](https://www.manning.com/books/type-driven-development-with-idris) provides an excellent introduction.
Like Coq, Idris is a close cousin of Lean, though it lacks tactics.

## Understanding Dependent Types

[_The Little Typer_](https://thelittletyper.com/) is a book for programmers who haven't formally studied logic or the theory of programming languages, but who want to build an understanding of the core ideas of dependent type theory.
While all of the above resources aim to be as practical as possible, _The Little Typer_ presents an approach to dependent type theory where the very basics are built up from scratch, using only concepts from programming.
Disclaimer: the author of _Functional Programming in Lean_ is also an author of _The Little Typer_.
