import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

example_module Examples.Intro

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Intro"

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
For instance, {anchorName Bool}`Bool` is an inductive datatype:

```anchor Bool
inductive Bool where
  | false : Bool
  | true : Bool
```

This definition has two main parts.
The first line provides the name of the new type ({anchorName Bool}`Bool`), while the remaining lines each describe a constructor.
As with constructors of structures, constructors of inductive datatypes are mere inert receivers of and containers for other data, rather than places to insert arbitrary initialization and validation code.
Unlike structures, inductive datatypes may have multiple constructors.
Here, there are two constructors, {anchorName Bool}`true` and {anchorName Bool}`false`, and neither takes any arguments.
Just as a structure declaration places its names in a namespace named after the declared type, an inductive datatype places the names of its constructors in a namespace.
In the Lean standard library, {anchorName BoolNames}`true` and {anchorName BoolNames}`false` are re-exported from this namespace so that they can be written alone, rather than as {anchorName BoolNames}`Bool.true` and {anchorName BoolNames}`Bool.false`, respectively.
:::

:::paragraph
From a data modeling perspective, inductive datatypes are used in many of the same contexts where a sealed abstract class might be used in other languages.
In languages like C# or Java, one might write a similar definition of {anchorName Bool}`Bool`:
```CSharp
abstract class Bool {}
class True : Bool {}
class False : Bool {}
```
However, the specifics of these representations are fairly different. In particular, each non-abstract class creates both a new type and new ways of allocating data. In the object-oriented example, {CSharp}`True` and {CSharp}`False` are both types that are more specific than {CSharp}`Bool`, while the Lean definition introduces only the new type {anchorName Bool}`Bool`.
:::

The type {anchorName Nat}`Nat` of non-negative integers is an inductive datatype:

```anchor Nat
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
```

Here, {anchorName NatNames}`zero` represents 0, while {anchorName NatNames}`succ` represents the successor of some other number.
The {anchorName Nat}`Nat` mentioned in {anchorName NatNames}`succ`'s declaration is the very type {anchorName Nat}`Nat` that is in the process of being defined.
_Successor_ means “one greater than”, so the successor of five is six and the successor of 32,185 is 32,186.
Using this definition, {anchorEvalStep four 1}`4` is represented as {anchorEvalStep four 0}`Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))`.
This definition is almost like the definition of {anchorName even}`Bool` with slightly different names.
The only real difference is that {anchorName NatNames}`succ` is followed by {anchorTerm Nat}`(n : Nat)`, which specifies that the constructor {anchorName NatNames}`succ` takes an argument of type {anchorName Nat}`Nat` which happens to be named {anchorName Nat}`n`.
The names {anchorName NatNames}`zero` and {anchorName NatNames}`succ` are in a namespace named after their type, so they must be referred to as {anchorName NatNames}`Nat.zero` and {anchorName NatNames}`Nat.succ`, respectively.

Argument names, such as {anchorName Nat}`n`, may occur in Lean's error messages and in feedback provided when writing mathematical proofs.
Lean also has an optional syntax for providing arguments by name.
Generally, however, the choice of argument name is less important than the choice of a structure field name, as it does not form as large a part of the API.

In C# or Java, {CSharp}`Nat` could be defined as follows:
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
Just as in the {anchorName Bool}`Bool` example above, this defines more types than the Lean equivalent.
Additionally, this example highlights how Lean datatype constructors are much more like subclasses of an abstract class than they are like constructors in C# or Java, as the constructor shown here contains initialization code to be executed.

Sum types are also similar to using a string tag to encode discriminated unions in TypeScript.
In TypeScript, {typescript}`Nat` could be defined as follows:
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
Just like C# and Java, this encoding ends up with more types than in Lean, because {typescript}`Zero` and {typescript}`Succ` are each a type on their own.
It also illustrates that Lean constructors correspond to objects in JavaScript or TypeScript that include a tag that identifies the contents.

# Pattern Matching
%%%
tag := "pattern-matching"
%%%

In many languages, these kinds of data are consumed by first using an instance-of operator to check which subclass has been received and then reading the values of the fields that are available in the given subclass.
The instance-of check determines which code to run, ensuring that the data needed by this code is available, while the fields themselves provide the data.
In Lean, both of these purposes are simultaneously served by _pattern matching_.

An example of a function that uses pattern matching is {anchorName isZero}`isZero`, which is a function that returns {anchorName isZero}`true` when its argument is {anchorName isZero}`Nat.zero`, or false otherwise.

```anchor isZero
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false
```

The {kw}`match` expression is provided the function's argument {anchorName isZero}`n` for destructuring.
If {anchorName isZero}`n` was constructed by {anchorName isZero}`Nat.zero`, then the first branch of the pattern match is taken, and the result is {anchorName isZero}`true`.
If {anchorName isZero}`n` was constructed by {anchorName isZero}`Nat.succ`, then the second branch is taken, and the result is {anchorName isZero}`false`.

:::paragraph
Step-by-step, evaluation of {anchorEvalStep isZeroZeroSteps 0}`isZero Nat.zero` proceeds as follows:

```anchorEvalSteps  isZeroZeroSteps
isZero Nat.zero
===>
match Nat.zero with
| Nat.zero => true
| Nat.succ k => false
===>
true
```
:::

:::paragraph
Evaluation of {anchorEvalStep isZeroFiveSteps 0}`isZero 5` proceeds similarly:

```anchorEvalSteps  isZeroFiveSteps
isZero 5
===>
isZero (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
===>
match Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) with
| Nat.zero => true
| Nat.succ k => false
===>
false
```
:::

The {anchorName isZero}`k` in the second branch of the pattern in {anchorName isZero}`isZero` is not decorative.
It makes the {anchorName isZero}`Nat` that is the argument to {anchorName isZero}`Nat.succ` visible, with the provided name.
That smaller number can then be used to compute the final result of the expression.


:::paragraph
Just as the successor of some number $`n` is one greater than $`n` (that is, $`n + 1`), the predecessor of a number is one less than it.
If {anchorName pred}`pred` is a function that finds the predecessor of a {anchorName pred}`Nat`, then it should be the case that the following examples find the expected result:

```anchor  predFive
#eval pred 5
```

```anchorInfo predFive
4
```

```anchor predBig
#eval pred 839
```

```anchorInfo predBig
838
```
:::

:::paragraph
Because {anchorName Nat}`Nat` cannot represent negative numbers, {anchorName NatNames}`Nat.zero` is a bit of a conundrum.
Usually, when working with {anchorName Nat}`Nat`, operators that would ordinarily produce a negative number are redefined to produce {anchorName NatNames}`zero` itself:

```anchor predZero
#eval pred 0
```
```anchorInfo predZero
0
```
:::


To find the predecessor of a {anchorName pred}`Nat`, the first step is to check which constructor was used to create it.
If it was {anchorName pred}`Nat.zero`, then the result is {anchorName pred}`Nat.zero`.
If it was {anchorName pred}`Nat.succ`, then the name {anchorName pred}`k` is used to refer to the {anchorName plus}`Nat` underneath it.
And this {anchorName pred}`Nat` is the desired predecessor, so the result of the {anchorName pred}`Nat.succ` branch is {anchorName pred}`k`.

```anchor pred
def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k
```

:::paragraph
Applying this function to {anchorTerm predFiveSteps}`5` yields the following steps:

```anchorEvalSteps  predFiveSteps
pred 5
===>
pred (Nat.succ 4)
===>
match Nat.succ 4 with
| Nat.zero => Nat.zero
| Nat.succ k => k
===>
4
```
:::

:::paragraph
Pattern matching can be used with structures as well as with sum types.
For instance, a function that extracts the third dimension from a {anchorName depth}`Point3D` can be written as follows:

```anchor depth
def depth (p : Point3D) : Float :=
  match p with
  | { x:= h, y := w, z := d } => d
```

In this case, it would have been much simpler to just use the {anchorName fragments}`Point3D.z` accessor, but structure patterns are occasionally the simplest way to write a function.
:::

# Recursive Functions
%%%
tag := "recursive-functions"
%%%

Definitions that refer to the name being defined are called _recursive definitions_.
Inductive datatypes are allowed to be recursive; indeed, {anchorName Nat}`Nat` is an example of such a datatype because {anchorName Nat}`succ` demands another {anchorName Nat}`Nat`.
Recursive datatypes can represent arbitrarily large data, limited only by technical factors like available memory.
Just as it would be impossible to write down one constructor for each natural number in the datatype definition, it is also impossible to write down a pattern match case for each possibility.

:::paragraph
Recursive datatypes are nicely complemented by recursive functions.
A simple recursive function over {anchorName even}`Nat` checks whether its argument is even.
In this case, {anchorName even}`Nat.zero` is even.
Non-recursive branches of the code like this one are called _base cases_.
The successor of an odd number is even, and the successor of an even number is odd.
This means that a number built with {anchorName even}`Nat.succ` is even if and only if its argument is not even.

```anchor even
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
```

:::


This pattern of thought is typical for writing recursive functions on {anchorName even}`Nat`.
First, identify what to do for {anchorName even}`Nat.zero`.
Then, determine how to transform a result for an arbitrary {anchorName even}`Nat` into a result for its successor, and apply this transformation to the result of the recursive call.
This pattern is called _structural recursion_.

:::paragraph
Unlike many languages, Lean ensures by default that every recursive function will eventually reach a base case.
From a programming perspective, this rules out accidental infinite loops.
But this feature is especially important when proving theorems, where infinite loops cause major difficulties.
A consequence of this is that Lean will not accept a version of {anchorName even}`even` that attempts to invoke itself recursively on the original number:

```anchor evenLoops
def evenLoops (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (evenLoops n)
```
The important part of the error message is that Lean could not determine that the recursive function always reaches a base case (because it doesn't).

```anchorError evenLoops
fail to show termination for
  evenLoops
with errors
failed to infer structural recursion:
Not considering parameter n of evenLoops:
  it is unchanged in the recursive calls
no parameters suitable for structural recursion

well-founded recursion cannot be used, 'evenLoops' does not take any (non-fixed) arguments
```

:::

:::paragraph
Even though addition takes two arguments, only one of them needs to be inspected.
To add zero to a number $`n`, just return $`n`.
To add the successor of $`k` to $`n`, take the successor of the result of adding $`k` to $`n`.

```anchor plus
def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')
```

:::

:::paragraph
In the definition of {anchorName plus}`plus`, the name {anchorName plus}`k'` is chosen to indicate that it is connected to, but not identical with, the argument {anchorName plus}`k`.
For instance, walking through the evaluation of {anchorEvalStep plusThreeTwo 0}`plus 3 2` yields the following steps:

```anchorEvalSteps  plusThreeTwo
plus 3 2
===>
plus 3 (Nat.succ (Nat.succ Nat.zero))
===>
match Nat.succ (Nat.succ Nat.zero) with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k')
===>
Nat.succ (plus 3 (Nat.succ Nat.zero))
===>
Nat.succ (match Nat.succ Nat.zero with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k'))
===>
Nat.succ (Nat.succ (plus 3 Nat.zero))
===>
Nat.succ (Nat.succ (match Nat.zero with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k')))
===>
Nat.succ (Nat.succ 3)
===>
5
```
:::

:::paragraph
One way to think about addition is that $`n + k` applies {anchorName times}`Nat.succ` $`k` times to $`n`.
Similarly, multiplication $`n × k` adds $`n` to itself $`k` times and subtraction $`n - k` takes $`n`'s predecessor $`k` times.

```anchor times
def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')
```

```anchor minus
def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')
```

:::

:::paragraph
Not every function can be easily written using structural recursion.
The understanding of addition as iterated {anchorName plus}`Nat.succ`, multiplication as iterated addition, and subtraction as iterated predecessor suggests an implementation of division as iterated subtraction.
In this case, if the numerator is less than the divisor, the result is zero.
Otherwise, the result is the successor of dividing the numerator minus the divisor by the divisor.

```anchor div
def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)
```
:::

:::paragraph
As long as the second argument is not {anchorTerm div}`0`, this program terminates, as it always makes progress towards the base case.
However, it is not structurally recursive, because it doesn't follow the pattern of finding a result for zero and transforming a result for a smaller {anchorName div}`Nat` into a result for its successor.
In particular, the recursive invocation of the function is applied to the result of another function call, rather than to an input constructor's argument.
Thus, Lean rejects it with the following message:

```anchorError div
fail to show termination for
  div
with errors
failed to infer structural recursion:
Not considering parameter k of div:
  it is unchanged in the recursive calls
Cannot use parameter k:
  failed to eliminate recursive application
    div (n - k) k


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
k n : Nat
h✝ : ¬n < k
⊢ n - k < n
```

This message means that {anchorName div}`div` requires a manual proof of termination.
This topic is explored in {ref "division-as-iterated-subtraction"}[the final chapter].
:::
