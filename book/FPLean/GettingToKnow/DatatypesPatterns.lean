import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

#doc (Manual) "Datatypes and Patterns" =>
%%%
tag := "datatypes-and-patterns"
%%%

Structures enable multiple independent pieces of data to be combined into a coherent whole that is represented by a brand new type.
Types such as structures that group together a collection of values are called _product types_.
Many domain concepts, however, can't be naturally represented as structures.
For instance, an application might need to track user permissions, where some users are document owners, some may edit documents, and others may only read them.
A calculator has a number of binary operators, such as addition, subtraction, and multiplication.
Structures do not provide an easy way to encode multiple choices.

Similarly, while a structure is an excellent way to keep track of a fixed set of fields, many applications require data that may contain an arbitrary number of elements.
Most classic data structures, such as trees and lists, have a recursive structure, where the tail of a list is itself a list, or where the left and right branches of a binary tree are themselves binary trees.
In the aforementioned calculator, the structure of expressions themselves is recursive.
The summands in an addition expression may themselves be multiplication expressions, for instance.

Datatypes that allow choices are called _sum types_ and datatypes that can include instances of themselves are called _recursive datatypes_.
Recursive sum types are called _inductive datatypes_, because mathematical induction may be used to prove statements about them.
When programming, inductive datatypes are consumed through pattern matching and recursive functions.

:::paragraph
Many of the built-in types are actually inductive datatypes in the standard library.
For instance, {term}`fakeBool` is an inductive datatype:

{exampleDecl Bool}

This definition has two main parts.
The first line provides the name of the new type ({term}`fakeBool`), while the remaining lines each describe a constructor.
As with constructors of structures, constructors of inductive datatypes are mere inert receivers of and containers for other data, rather than places to insert arbitrary initialization and validation code.
Unlike structures, inductive datatypes may have multiple constructors.
Here, there are two constructors, {term}`fakeTrue` and {term}`fakeFalse`, and neither takes any arguments.
Just as a structure declaration places its names in a namespace named after the declared type, an inductive datatype places the names of its constructors in a namespace.
In the Lean standard library, {term}`fakeTrue` and {term}`fakeFalse` are re-exported from this namespace so that they can be written alone, rather than as {term}`fakeBool.true` and {term}`fakeBool.false`, respectively.
:::

:::paragraph
From a data modeling perspective, inductive datatypes are used in many of the same contexts where a sealed abstract class might be used in other languages.
In languages like C# or Java, one might write a similar definition of {term}`fakeBool`:
```CSharp
abstract class Bool {}
class True : Bool {}
class False : Bool {}
```
However, the specifics of these representations are fairly different. In particular, each non-abstract class creates both a new type and new ways of allocating data. In the object-oriented example, `True` and `False` are both types that are more specific than `Bool`, while the Lean definition introduces only the new type {term}`fakeBool`.
:::

The type `Nat` of non-negative integers is an inductive datatype:

{exampleDecl Nat}

Here, {term}`fakeZero` represents 0, while {term}`fakeSucc` represents the successor of some other number.
The {term}`fakeNat` mentioned in {term}`fakeSucc`'s declaration is the very type {term}`fakeNat` that is in the process of being defined.
_Successor_ means “one greater than”, so the successor of five is six and the successor of 32,185 is 32,186.
Using this definition, {exampleEval 1}`four` is represented as {exampleEval 0}`four`.
This definition is almost like the definition of {term}`Bool.name` with slightly different names.
The only real difference is that {term}`fakeSucc` is followed by `(n : Nat)`, which specifies that the constructor {term}`fakeSucc` takes an argument of type {term}`fakeNat` which happens to be named `n`.
The names {term}`fakeZero` and {term}`fakeSucc` are in a namespace named after their type, so they must be referred to as {term}`Nat.fakeZero` and {term}`Nat.fakeSucc`, respectively.

Argument names, such as `n`, may occur in Lean's error messages and in feedback provided when writing mathematical proofs.
Lean also has an optional syntax for providing arguments by name.
Generally, however, the choice of argument name is less important than the choice of a structure field name, as it does not form as large a part of the API.

In C# or Java, `Nat` could be defined as follows:
```CSharp
abstract class Nat {}
class Zero : Nat {}
class Succ : Nat {
  public Nat n;
  public Succ(Nat pred) {
	n = pred;
  }
}
```
Just as in the {term}`fakeBool` example above, this defines more types than the Lean equivalent.
Additionally, this example highlights how Lean datatype constructors are much more like subclasses of an abstract class than they are like constructors in C# or Java, as the constructor shown here contains initialization code to be executed.

Sum types are also similar to using a string tag to encode discriminated unions in TypeScript.
In TypeScript, `Nat` could be defined as follows:
```typescript
interface Zero {
    tag: "zero";
}

interface Succ {
    tag: "succ";
    predecessor: Nat;
}

type Nat = Zero | Succ;
```
Just like C# and Java, this encoding ends up with more types than in Lean, because `Zero` and `Succ` are each a type on their own.
It also illustrates that Lean constructors correspond to objects in JavaScript or TypeScript that include a tag that identifies the contents.

# Pattern Matching

In many languages, these kinds of data are consumed by first using an instance-of operator to check which subclass has been received and then reading the values of the fields that are available in the given subclass.
The instance-of check determines which code to run, ensuring that the data needed by this code is available, while the fields themselves provide the data.
In Lean, both of these purposes are simultaneously served by _pattern matching_.

An example of a function that uses pattern matching is {term}`isZero.name`, which is a function that returns {term}`true` when its argument is {term}`Nat.zero.name`, or false otherwise.

{exampleDecl isZero}

The {kw}`match` expression is provided the function's argument {term}`isZero.n` for destructuring.
If {term}`isZero.n` was constructed by {term}`Nat.zero.name`, then the first branch of the pattern match is taken, and the result is {term}`true`.
If {term}`isZero.n` was constructed by {term}`Nat.succ.name`, then the second branch is taken, and the result is {term}`false`.

Step-by-step, evaluation of {exampleEval 0}`isZeroZeroSteps` proceeds as follows:

{exampleEval isZeroZeroSteps}


Evaluation of {exampleEval 0}`isZeroFiveSteps` proceeds similarly:

{exampleEval isZeroFiveSteps}


The {term}`isZero.k` in the second branch of the pattern in {term}`isZero.name` is not decorative.
It makes the {term}`Nat.name` that is the argument to {term}`succ.name` visible, with the provided name.
That smaller number can then be used to compute the final result of the expression.

Just as the successor of some number $`n` is one greater than $`n` (that is, $`n + 1`), the predecessor of a number is one less than it.
If {term}`pred.name` is a function that finds the predecessor of a {term}`Nat`, then it should be the case that the following examples find the expected result:

{exampleIn predFive}


{exampleInfo predFive}


{exampleIn predBig}


{exampleInfo predBig}

:::paragraph
Because {term}`Nat.name` cannot represent negative numbers, {term}`zero` is a bit of a conundrum.
Usually, when working with {term}`Nat.name`, operators that would ordinarily produce a negative number are redefined to produce {term}`zero` itself:

{exampleIn predZero}

{exampleInfo predZero}

:::

To find the predecessor of a {term}`Nat.name`, the first step is to check which constructor was used to create it.
If it was {term}`Nat.zero.name`, then the result is {term}`Nat.zero.name`.
If it was {term}`Nat.succ.name`, then the name {term}`pred.k` is used to refer to the {term}`Nat.name` underneath it.
And this {term}`Nat.name` is the desired predecessor, so the result of the {term}`Nat.succ.name` branch is {term}`pred.k`.

{exampleDecl pred}

:::paragraph
Applying this function to {term}`5` yields the following steps:

{exampleEval predFiveSteps}

:::

:::paragraph
Pattern matching can be used with structures as well as with sum types.
For instance, a function that extracts the third dimension from a {term}`Point3D.name` can be written as follows:

{exampleDecl depth}

In this case, it would have been much simpler to just use the {term}`Point3D.z.name` accessor, but structure patterns are occasionally the simplest way to write a function.
:::

# Recursive Functions

Definitions that refer to the name being defined are called _recursive definitions_.
Inductive datatypes are allowed to be recursive; indeed, {term}`Nat.name` is an example of such a datatype because {term}`succ.name` demands another {term}`Nat.name`.
Recursive datatypes can represent arbitrarily large data, limited only by technical factors like available memory.
Just as it would be impossible to write down one constructor for each natural number in the datatype definition, it is also impossible to write down a pattern match case for each possibility.

:::paragraph
Recursive datatypes are nicely complemented by recursive functions.
A simple recursive function over {term}`Nat.name` checks whether its argument is even.
In this case, {term}`zero.name` is even.
Non-recursive branches of the code like this one are called _base cases_.
The successor of an odd number is even, and the successor of an even number is odd.
This means that a number built with {term}`succ.name` is even if and only if its argument is not even.

{exampleDecl even}

:::


This pattern of thought is typical for writing recursive functions on {term}`Nat.name`.
First, identify what to do for {term}`zero.name`.
Then, determine how to transform a result for an arbitrary {term}`Nat.name` into a result for its successor, and apply this transformation to the result of the recursive call.
This pattern is called _structural recursion_.

:::paragraph
Unlike many languages, Lean ensures by default that every recursive function will eventually reach a base case.
From a programming perspective, this rules out accidental infinite loops.
But this feature is especially important when proving theorems, where infinite loops cause major difficulties.
A consequence of this is that Lean will not accept a version of `even` that attempts to invoke itself recursively on the original number:

{exampleIn evenLoops}

The important part of the error message is that Lean could not determine that the recursive function always reaches a base case (because it doesn't).

{exampleError evenLoops}

:::

:::paragraph
Even though addition takes two arguments, only one of them needs to be inspected.
To add zero to a number $`n`, just return $`n`.
To add the successor of $`k` to $`n`, take the successor of the result of adding $`k` to $`n`.

{exampleDecl plus}

:::

:::paragraph
In the definition of {term}`plus.name`, the name {term}`plus.k'` is chosen to indicate that it is connected to, but not identical with, the argument {term}`plus.k`.
For instance, walking through the evaluation of {exampleEval 0}`plusThreeTwo` yields the following steps:

{exampleEval plusThreeTwo}

:::

:::paragraph
One way to think about addition is that $`n + k` applies {term}`Nat.succ.name` $`k` times to $`n`.
Similarly, multiplication $`n × k` adds $`n` to itself $`k` times and subtraction $`n - k` takes $`n`'s predecessor $`k` times.

{exampleDecl times}

{exampleDecl minus}

:::

:::paragraph
Not every function can be easily written using structural recursion.
The understanding of addition as iterated {term}`Nat.succ.name`, multiplication as iterated addition, and subtraction as iterated predecessor suggests an implementation of division as iterated subtraction.
In this case, if the numerator is less than the divisor, the result is zero.
Otherwise, the result is the successor of dividing the numerator minus the divisor by the divisor.

{exampleIn div}

:::

:::paragraph
As long as the second argument is not {term}`0`, this program terminates, as it always makes progress towards the base case.
However, it is not structurally recursive, because it doesn't follow the pattern of finding a result for zero and transforming a result for a smaller {term}`Nat.name` into a result for its successor.
In particular, the recursive invocation of the function is applied to the result of another function call, rather than to an input constructor's argument.
Thus, Lean rejects it with the following message:

{exampleError div}

This message means that {term}`div.name` requires a manual proof of termination.
This topic is explored in [the final chapter](../programs-proofs/inequalities.md#division-as-iterated-subtraction).

:::
