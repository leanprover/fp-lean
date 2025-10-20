import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad.ActualDefs"

#doc (Manual) "Summary" =>
%%%
tag := "structure-applicative-monad-summary"
%%%

# Type Classes and Structures
%%%
tag := none
%%%

Behind the scenes, type classes are represented by structures.
Defining a class defines a structure, and additionally creates an empty table of instances.
Defining an instance creates a value that either has the structure as its type or is a function that can return the structure, and additionally adds an entry to the table.
Instance search consists of constructing an instance by consulting the instance tables.
Both structures and classes may provide default values for fields (which are default implementations of methods).

# Structures and Inheritance
%%%
tag := none
%%%

Structures may inherit from other structures.
Behind the scenes, a structure that inherits from another structure contains an instance of the original structure as a field.
In other words, inheritance is implemented with composition.
When multiple inheritance is used, only the unique fields from the additional parent structures are used to avoid a diamond problem, and the functions that would normally extract the parent value are instead organized to construct one.
Record dot notation takes structure inheritance into account.

Because type classes are just structures with some additional automation applied, all of these features are available in type classes.
Together with default methods, this can be used to create a fine-grained hierarchy of interfaces that nonetheless does not impose a large burden on clients, because the small classes that the large classes inherit from can be automatically implemented.

# Applicative Functors
%%%
tag := none
%%%

An applicative functor is a functor with two additional operations:
 * {anchorName Applicative}`pure`, which is the same operator as that for {anchorName Monad}`Monad`
 * {anchorName Seq}`seq`, which allows a function to be applied in the context of the functor.

While monads can represent arbitrary programs with control flow, applicative functors can only run function arguments from left to right.
Because they are less powerful, they provide less control to programs written against the interface, while the implementor of the method has a greater degree of freedom.
Some useful types can implement {anchorName Applicative}`Applicative` but not {anchorName Monad}`Monad`.

In fact, the type classes {anchorName HonestFunctor}`Functor`, {anchorName Applicative}`Applicative`, and {anchorName Monad}`Monad` form a hierarchy of power.
Moving up the hierarchy, from {anchorName HonestFunctor}`Functor` towards {anchorName Monad}`Monad`, allows more powerful programs to be written, but fewer types implement the more powerful classes.
Polymorphic programs should be written to use as weak of an abstraction as possible, while datatypes should be given instances that are as powerful as possible.
This maximizes code re-use.
The more powerful type classes extend the less powerful ones, which means that an implementation of {anchorName Monad}`Monad` provides implementations of {anchorName HonestFunctor}`Functor` and {anchorName Applicative}`Applicative` for free.

Each class has a set of methods to be implemented and a corresponding contract that specifies additional rules for the methods.
Programs that are written against these interfaces expect that the additional rules are followed, and may be buggy if they are not.
The default implementations of {anchorName HonestFunctor}`Functor`'s methods in terms of {anchorName Applicative}`Applicative`'s, and of {anchorName Applicative}`Applicative`'s in terms of {anchorName Monad}`Monad`'s, will obey these rules.

# Universes
%%%
tag := none
%%%

To allow Lean to be used as both a programming language and a theorem prover, some restrictions on the language are necessary.
This includes restrictions on recursive functions that ensure that they all either terminate or are marked as {kw}`partial` and written to return types that are not uninhabited.
Additionally, it must be impossible to represent certain kinds of logical paradoxes as types.

One of the restrictions that rules out certain paradoxes is that every type is assigned to a _universe_.
Universes are types such as {anchorTerm extras}`Prop`, {anchorTerm extras}`Type`, {anchorTerm extras}`Type 1`, {anchorTerm extras}`Type 2`, and so forth.
These types describe other types—just as {anchorTerm extras}`0` and {anchorTerm extras}`17` are described by {anchorName extras}`Nat`, {anchorName extras}`Nat` is itself described by {anchorTerm extras}`Type`, and {anchorTerm extras}`Type` is described by {anchorTerm extras}`Type 1`.
The type of functions that take a type as an argument must be a larger universe than the argument's universe.

Because each declared datatype has a universe, writing code that uses types like data would quickly become annoying, requiring each polymorphic type to be copy-pasted to take arguments from {anchorTerm extras}`Type 1`.
A feature called _universe polymorphism_ allows Lean programs and datatypes to take universe levels as arguments, just as ordinary polymorphism allows programs to take types as arguments.
Generally speaking, Lean libraries should use universe polymorphism when implementing libraries of polymorphic operations.
