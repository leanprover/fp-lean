import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean


set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

#doc (Manual) "Summary" =>
%%%
tag := "getting-to-know-summary"
%%%

# Evaluating Expressions
%%%
tag := none
%%%

In Lean, computation occurs when expressions are evaluated.
This follows the usual rules of mathematical expressions: sub-expressions are replaced by their values following the usual order of operations, until the entire expression has become a value.
When evaluating an {kw}`if` or a {kw}`match`, the expressions in the branches are not evaluated until the value of the condition or the match subject has been found.

Once they have been given a value, variables never change.
Similarly to mathematics but unlike most programming languages, Lean variables are simply placeholders for values, rather than addresses to which new values can be written.
Variables' values may come from global definitions with {kw}`def`, local definitions with {kw}`let`, as named arguments to functions, or from pattern matching.

# Functions
%%%
tag := none
%%%

Functions in Lean are first-class values, meaning that they can be passed as arguments to other functions, saved in variables, and used like any other value.
Every Lean function takes exactly one argument.
To encode a function that takes more than one argument, Lean uses a technique called currying, where providing the first argument returns a function that expects the remaining arguments.
To encode a function that takes no arguments, Lean uses the {moduleName}`Unit` type, which is the least informative possible argument.

There are three primary ways of creating functions:
1. Anonymous functions are written using {kw}`fun`.
   For instance, a function that swaps the fields of a {anchorName fragments}`Point` can be written {anchorTerm swapLambda}`fun (point : Point) => { x := point.y, y := point.x : Point }`
2. Very simple anonymous functions are written by placing one or more centered dots {anchorTerm subOneDots}`·` inside of parentheses.
   Each centered dot becomes an argument to the function, and the parentheses delimit its body.
   For instance, a function that subtracts one from its argument can be written as {anchorTerm subOneDots}`(· - 1)` instead of as {anchorTerm subOneDots}`fun x => x - 1`.
3. Functions can be defined using {kw}`def` or {kw}`let` by adding an argument list or by using pattern-matching notation.

# Types
%%%
tag := none
%%%

Lean checks that every expression has a type.
Types, such as {anchorName fragments}`Int`, {anchorName fragments}`Point`, {anchorTerm fragments}`{α : Type} → Nat → α → List α`, and {anchorTerm fragments}`Option (String ⊕ (Nat × String))`, describe the values that may eventually be found for an expression.
Like other languages, types in Lean can express lightweight specifications for programs that are checked by the Lean compiler, obviating the need for certain classes of unit test.
Unlike most languages, Lean's types can also express arbitrary mathematics, unifying the worlds of programming and theorem proving.
While using Lean for proving theorems is mostly out of scope for this book, _[Theorem Proving in Lean 4](https://leanprover.github.io/theorem_proving_in_lean4/)_ contains more information on this topic.

Some expressions can be given multiple types.
For instance, {lit}`3` can be an {anchorName fragments}`Int` or a {anchorName fragments}`Nat`.
In Lean, this should be understood as two separate expressions, one with type {anchorName fragments}`Nat` and one with type {anchorName fragments}`Int`, that happen to be written in the same way, rather than as two different types for the same thing.

Lean is sometimes able to determine types automatically, but types must often be provided by the user.
This is because Lean's type system is so expressive.
Even when Lean can find a type, it may not find the desired type—{lit}`3` could be intended to be used as an {anchorName fragments}`Int`, but Lean will give it the type {anchorName fragments}`Nat` if there are no further constraints.
In general, it is a good idea to write most types explicitly, only letting Lean fill out the very obvious types.
This improves Lean's error messages and helps make programmer intent more clear.

Some functions or datatypes take types as arguments.
They are called _polymorphic_.
Polymorphism allows programs such as one that calculates the length of a list without caring what type the entries in the list have.
Because types are first class in Lean, polymorphism does not require any special syntax, so types are passed just like other arguments.
Naming an argument in a function type allows later types to mention that name, and when the function is applied to an argument, the type of the resulting term is found by replacing the argument's name with the actual value it was applied to.

# Structures and Inductive Types
%%%
tag := none
%%%

Brand new datatypes can be introduced to Lean using the {kw}`structure` or {kw}`inductive` features.
These new types are not considered to be equivalent to any other type, even if their definitions are otherwise identical.
Datatypes have _constructors_ that explain the ways in which their values can be constructed, and each constructor takes some number of arguments.
Constructors in Lean are not the same as constructors in object-oriented languages: Lean's constructors are inert holders of data, rather than active code that initializes an allocated object.

Typically, {kw}`structure` is used to introduce a product type (that is, a type with just one constructor that takes any number of arguments), while {kw}`inductive` is used to introduce a sum type (that is, a type with many distinct constructors).
Datatypes defined with {kw}`structure` are provided with one accessor function for each field.
Both structures and inductive datatypes may be consumed with pattern matching, which exposes the values stored inside of constructors using a subset of the syntax used to call said constructors.
Pattern matching means that knowing how to create a value implies knowing how to consume it.

# Recursion
%%%
tag := none
%%%

A definition is recursive when the name being defined is used in the definition itself.
Because Lean is an interactive theorem prover in addition to being a programming language, there are certain restrictions placed on recursive definitions.
In Lean's logical side, circular definitions could lead to logical inconsistency.

In order to ensure that recursive definitions do not undermine the logical side of Lean, Lean must be able to prove that all recursive functions terminate, no matter what arguments they are called with.
In practice, this means either that recursive calls are all performed on a structurally-smaller piece of the input, which ensures that there is always progress towards a base case, or that users must provide some other evidence that the function always terminates.
Similarly, recursive inductive types are not allowed to have a constructor that takes a function _from_ the type as an argument, because this would make it possible to encode non-terminating functions.
