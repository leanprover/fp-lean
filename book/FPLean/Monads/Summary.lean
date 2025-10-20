import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Class"

#doc (Manual) "Summary" =>
%%%
tag := "monads-summary"
%%%

# Encoding Side Effects
%%%
tag := none
%%%

Lean is a pure functional language.
This means that it does not include side effects such as mutable variables, logging, or exceptions.
However, most side effects can be _encoded_ using a combination of functions and inductive types or structures.
For example, mutable state can be encoded as a function from an initial state to a pair of a final state and a result, and exceptions can be encoded as an inductive type with constructors for successful termination and errors.

Each set of encoded effects is a type.
As a result, if a program uses these encoded effects, then this is apparent in its type.
Functional programming does not mean that programs can't use effects, it simply requires that they be _honest_ about which effects they use.
A Lean type signature describes not only the types of arguments that a function expects and the type of result that it returns, but also which effects it may use.

# The Monad Type Class
%%%
tag := none
%%%

It's possible to write purely functional programs in languages that allow effects anywhere.
For example, {python}`2 + 3` is a valid Python program that has no effects at all.
Similarly, combining programs that have effects requires a way to state the order in which the effects must occur.
It matters whether an exception is thrown before or after modifying a variable, after all.

The type class {anchorName FakeMonad}`Monad` captures these two important properties.
It has two methods: {anchorName FakeMonad}`pure` represents programs that have no effects, and {anchorName FakeMonad}`bind` sequences effectful programs.
The contract for {anchorName FakeMonad}`Monad` instances ensures that {anchorName FakeMonad}`bind` and {anchorName FakeMonad}`pure` actually capture pure computation and sequencing.

# {kw}`do`-Notation for Monads
%%%
tag := none
%%%

Rather than being limited to {moduleName}`IO`, {kw}`do`-notation works for any monad.
It allows programs that use monads to be written in a style that is reminiscent of statement-oriented languages, with statements sequenced after one another.
Additionally, {kw}`do`-notation enables a number of additional convenient shorthands, such as nested actions.
A program written with {kw}`do` is translated to applications of {lit}`>>=` behind the scenes.

# Custom Monads
%%%
tag := none
%%%

Different languages provide different sets of side effects.
While most languages feature mutable variables and file I/O, not all have features like exceptions.
Other languages offer effects that are rare or unique, like Icon's search-based program execution, Scheme and Ruby's continuations, and Common Lisp's resumable exceptions.
An advantage to encoding effects with monads is that programs are not limited to the set of effects that are provided by the language.
Because Lean is designed to make programming with any monad convenient, programmers are free to choose exactly the set of side effects that make sense for any given application.

# The {lit}`IO` Monad
%%%
tag := none
%%%

Programs that can affect the real world are written as {moduleName}`IO` actions in Lean.
{moduleName}`IO` is one monad among many.
The {moduleName}`IO` monad encodes state and exceptions, with the state being used to keep track of the state of the world and the exceptions modeling failure and recovery.
