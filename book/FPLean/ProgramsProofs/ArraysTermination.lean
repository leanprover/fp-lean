import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Arrays"

#doc (Manual) "Arrays and Termination" =>
%%%
tag := "array-termination"
%%%

To write efficient code, it is important to select appropriate data structures.
Linked lists have their place: in some applications, the ability to share the tails of lists is very important.
However, most use cases for a variable-length sequential collection of data are better served by arrays, which have both less memory overhead and better locality.

Arrays, however, have two drawbacks relative to lists:
 1. Arrays are accessed through indexing, rather than by pattern matching, which imposes {ref "props-proofs-indexing"}[proof obligations] in order to maintain safety.
 2. A loop that processes an entire array from left to right is a tail-recursive function, but it does not have an argument that decreases on each call.

Making effective use of arrays requires knowing how to prove to Lean that an array index is in bounds, and how to prove that an array index that approaches the size of the array also causes the program to terminate.
Both of these are expressed using an inequality proposition, rather than propositional equality.

# Inequality
%%%
tag := "inequality"
%%%

Because different types have different notions of ordering, inequality is governed by two type classes, called {anchorName ordSugarClasses (module := Examples.Classes)}`LE` and {anchorName ordSugarClasses (module := Examples.Classes)}`LT`.
The table in the section on {ref "equality-and-ordering"}[standard type classes] describes how these classes relate to the syntax:

:::table +header
*
  * Expression
  * Desugaring
  * Class Name

*
  * {anchorTerm ltDesugar (module := Examples.Classes)}`x < y`
  * {anchorTerm ltDesugar (module := Examples.Classes)}`LT.lt x y`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LT`

*
  * {anchorTerm leDesugar (module := Examples.Classes)}`x ≤ y`
  * {anchorTerm leDesugar (module := Examples.Classes)}`LE.le x y`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LE`

*
  * {anchorTerm gtDesugar (module := Examples.Classes)}`x > y`
  * {anchorTerm gtDesugar (module := Examples.Classes)}`LT.lt y x`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LT`

*
  * {anchorTerm geDesugar (module := Examples.Classes)}`x ≥ y`
  * {anchorTerm geDesugar (module := Examples.Classes)}`LE.le y x`
  * {anchorName ordSugarClasses (module := Examples.Classes)}`LE`

:::

In other words, a type may customize the meaning of the {anchorTerm ltDesugar (module:=Examples.Classes)}`<` and {anchorTerm leDesugar (module:=Examples.Classes)}`≤` operators, while {anchorTerm gtDesugar (module:=Examples.Classes)}`>` and {anchorTerm geDesugar (module:=Examples.Classes)}`≥` derive their meanings from {anchorTerm ltDesugar (module:=Examples.Classes)}`<` and {anchorTerm leDesugar (module:=Examples.Classes)}`≤`.
The classes {anchorName ordSugarClasses (module := Examples.Classes)}`LT` and {anchorName ordSugarClasses (module := Examples.Classes)}`LE` have methods that return propositions rather than {anchorName CoeBoolProp (module:=Examples.Classes)}`Bool`s:

```anchor less
class LE (α : Type u) where
  le : α → α → Prop

class LT (α : Type u) where
  lt : α → α → Prop
```

The instance of {anchorName LENat}`LE` for {anchorName LENat}`Nat` delegates to {anchorName LENat}`Nat.le`:

```anchor LENat
instance : LE Nat where
  le := Nat.le
```
Defining {anchorName LENat}`Nat.le` requires a feature of Lean that has not yet been presented: it is an inductively-defined relation.

## Inductively-Defined Propositions, Predicates, and Relations
%%%
tag := "inductive-props"
%%%

{anchorName LENat}`Nat.le` is an _inductively-defined relation_.
Just as {kw}`inductive` can be used to create new datatypes, it can be used to create new propositions.
When a proposition takes an argument, it is referred to as a _predicate_ that may be true for some, but not all, potential arguments.
Propositions that take multiple arguments are called _relations_.

Each constructor of an inductively defined proposition is a way to prove it.
In other words, the declaration of the proposition describes the different forms of evidence that it is true.
A proposition with no arguments that has a single constructor can be quite easy to prove:

```anchor EasyToProve
inductive EasyToProve : Prop where
  | heresTheProof : EasyToProve
```
The proof consists of using its constructor:

```anchor fairlyEasy
theorem fairlyEasy : EasyToProve := by
  constructor
```
In fact, the proposition {anchorName True}`True`, which should always be easy to prove, is defined just like {anchorName EasyToProve}`EasyToProve`:

```anchor True
inductive True : Prop where
  | intro : True
```

Inductively-defined propositions that don't take arguments are not nearly as interesting as inductively-defined datatypes.
This is because data is interesting in its own right—the natural number {anchorTerm IsThree}`3` is different from the number {lit}`35`, and someone who has ordered 3 pizzas will be upset if 35 arrive at their door 30 minutes later.
The constructors of a proposition describe ways in which the proposition can be true, but once a proposition has been proved, there is no need to know _which_ underlying constructors were used.
This is why most interesting inductively-defined types in the {anchorTerm IsThree}`Prop` universe take arguments.

:::paragraph
The inductively-defined predicate {anchorName IsThree}`IsThree` states that its argument is three:

```anchor IsThree
inductive IsThree : Nat → Prop where
  | isThree : IsThree 3
```
The mechanism used here is just like {ref "column-pointers"}[indexed families such as {moduleName (module := Examples.DependentTypes.DB)}`HasCol`], except the resulting type is a proposition that can be proved rather than data that can be used.
:::

Using this predicate, it is possible to prove that three is indeed three:

```anchor threeIsThree
theorem three_is_three : IsThree 3 := by
  constructor
```
Similarly, {anchorName IsFive}`IsFive` is a predicate that states that its argument is {anchorTerm IsFive}`5`:

```anchor IsFive
inductive IsFive : Nat → Prop where
  | isFive : IsFive 5
```

If a number is three, then the result of adding two to it should be five.
This can be expressed as a theorem statement:
```anchor threePlusTwoFive0
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  skip
```
The resulting goal has a function type:
```anchorError threePlusTwoFive0
unsolved goals
n : Nat
⊢ IsThree n → IsFive (n + 2)
```
Thus, the {anchorTerm threePlusTwoFive1}`intro` tactic can be used to convert the argument into an assumption:
```anchor threePlusTwoFive1
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
```
```anchorError threePlusTwoFive1
unsolved goals
n : Nat
three : IsThree n
⊢ IsFive (n + 2)
```
Given the assumption that {anchorName threePlusTwoFive1a}`n` is three, it should be possible to use the constructor of {anchorName threePlusTwoFive1a}`IsFive` to complete the proof:
```anchor threePlusTwoFive1a
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  constructor
```
However, this results in an error:
```anchorError threePlusTwoFive1a
Tactic `constructor` failed: no applicable constructor found

n : Nat
three : IsThree n
⊢ IsFive (n + 2)
```
This error occurs because {anchorTerm threePlusTwoFive2}`n + 2` is not definitionally equal to {anchorTerm IsFive}`5`.
In an ordinary function definition, dependent pattern matching on the assumption {anchorName threePlusTwoFive2}`three` could be used to refine {anchorName threePlusTwoFive2}`n` to {anchorTerm threeIsThree}`3`.
The tactic equivalent of dependent pattern matching is {anchorTerm threePlusTwoFive2}`cases`, which has a syntax similar to that of {kw}`induction`:
```anchor threePlusTwoFive2
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => skip
```
In the remaining case, {anchorName threePlusTwoFive2}`n` has been refined to {anchorTerm IsThree}`3`:
```anchorError threePlusTwoFive2
unsolved goals
case isThree
⊢ IsFive (3 + 2)
```
Because {anchorTerm various}`3 + 2` is definitionally equal to {anchorTerm IsFive}`5`, the constructor is now applicable:

```anchor threePlusTwoFive3
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => constructor
```

The standard false proposition {anchorName various}`False` has no constructors, making it impossible to provide direct evidence for.
The only way to provide evidence for {anchorName various}`False` is if an assumption is itself impossible, similarly to how {kw}`nomatch` can be used to mark code that the type system can see is unreachable.
As described in {ref "connectives"}[the initial Interlude on proofs], the negation {anchorTerm various}`Not A` is short for {anchorTerm various}`A → False`.
{anchorTerm various}`Not A` can also be written {anchorTerm various}`¬A`.

It is not the case that four is three:
```anchor fourNotThree0
theorem four_is_not_three : ¬ IsThree 4 := by
  skip
```
The initial proof goal contains {anchorName fourNotThree1}`Not`:
```anchorError fourNotThree0
unsolved goals
⊢ ¬IsThree 4
```
The fact that it's actually a function type can be exposed using {anchorTerm fourNotThree1}`unfold`:
```anchor fourNotThree1
theorem four_is_not_three : ¬ IsThree 4 := by
  unfold Not
```
```anchorError fourNotThree1
unsolved goals
⊢ IsThree 4 → False
```
Because the goal is a function type, {anchorTerm fourNotThree2}`intro` can be used to convert the argument into an assumption.
There is no need to keep {anchorTerm fourNotThree1}`unfold`, as {anchorTerm fourNotThree2}`intro` can unfold the definition of {anchorName fourNotThree1}`Not` itself:
```anchor fourNotThree2
theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
```
```anchorError fourNotThree2
unsolved goals
h : IsThree 4
⊢ False
```
In this proof, the {anchorTerm fourNotThreeDone}`cases` tactic solves the goal immediately:

```anchor fourNotThreeDone
theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
  cases h
```
Just as a pattern match on a {anchorTerm otherEx (module:=Examples.DependentTypes)}`Vect String 2` doesn't need to include a case for {anchorName otherEx (module:=Examples.DependentTypes)}`Vect.nil`, a proof by cases over {anchorTerm fourNotThreeDone}`IsThree 4` doesn't need to include a case for {anchorName IsThree}`isThree`.

## Inequality of Natural Numbers
%%%
tag := "inequality-of-natural-numbers"
%%%

The definition of {anchorName NatLe}`Nat.le` has a parameter and an index:

```anchor NatLe
inductive Nat.le (n : Nat) : Nat → Prop
  | refl : Nat.le n n
  | step : Nat.le n m → Nat.le n (m + 1)
```
The parameter {anchorName NatLe}`n` is the number that should be smaller, while the index is the number that should be greater than or equal to {anchorName NatLe}`n`.
The {anchorName NatLe}`refl` constructor is used when both numbers are equal, while the {anchorName NatLe}`step` constructor is used when the index is greater than {anchorName NatLe}`n`.

From the perspective of evidence, a proof that $`n \leq k` consists of finding some number $`d` such that $`n + d = m`.
In Lean, the proof then consists of a {anchorName leNames}`Nat.le.refl` constructor wrapped by $`d` instances of {anchorName leNames}`Nat.le.step`.
Each {anchorName NatLe}`step` constructor adds one to its index argument, so $`d` {anchorName NatLe}`step` constructors adds $`d` to the larger number.
For example, evidence that four is less than or equal to seven consists of three {anchorName NatLe}`step`s around a {anchorName NatLe}`refl`:

```anchor four_le_seven
theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  step (step (step refl))
```

The strict less-than relation is defined by adding one to the number on the left:

```anchor NatLt
def Nat.lt (n m : Nat) : Prop :=
  Nat.le (n + 1) m

instance : LT Nat where
  lt := Nat.lt
```
Evidence that four is strictly less than seven consists of two {anchorName four_lt_seven}`step`'s around a {anchorName four_lt_seven}`refl`:

```anchor four_lt_seven
theorem four_lt_seven : 4 < 7 :=
  open Nat.le in
  step (step refl)
```
This is because {anchorTerm four_lt_seven}`4 < 7` is equivalent to {anchorTerm four_lt_seven_alt}`5 ≤ 7`.

# Proving Termination
%%%
tag := "proving-termination"
%%%

The function {anchorName ArrayMap}`Array.map` transforms an array with a function, returning a new array that contains the result of applying the function to each element of the input array.
Writing it as a tail-recursive function follows the usual pattern of delegating to a function that passes the output array in an accumulator.
The accumulator is initialized with an empty array.
The accumulator-passing helper function also takes an argument that tracks the current index into the array, which starts at {anchorTerm ArrayMap}`0`:

```anchor ArrayMap
def Array.map (f : α → β) (arr : Array α) : Array β :=
  arrayMapHelper f arr Array.empty 0
```

The helper should, at each iteration, check whether the index is still in bounds.
If so, it should loop again with the transformed element added to the end of the accumulator and the index incremented by {anchorTerm mapHelperIndexIssue}`1`.
If not, then it should terminate and return the accumulator.
An initial implementation of this code fails because Lean is unable to prove that the array index is valid:
```anchor mapHelperIndexIssue
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
```
```anchorError mapHelperIndexIssue
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.1811
β : Type ?u.1814
f : α → β
arr : Array α
soFar : Array β
i : Nat
⊢ i < arr.size
```
However, the conditional expression already checks the precise condition that the array index's validity demands (namely, {anchorTerm arrayMapHelperTermIssue}`i < arr.size`).
Adding a name to the {kw}`if` resolves the issue, because it adds an assumption that the array indexing tactic can use:

```anchor arrayMapHelperTermIssue
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
```
Lean accepts the modified program, even though the recursive call is not made on an argument to one of the input constructors.
In fact, both the accumulator and the index grow, rather than shrinking.

Behind the scenes, Lean's proof automation constructs a termination proof.
Reconstructing this proof can make it easier to understand the cases that Lean cannot automatically recognize.

Why does {anchorName arrayMapHelperTermIssue}`arrayMapHelper` terminate?
Each iteration checks whether the index {anchorName arrayMapHelperTermIssue}`i` is still in bounds for the array {anchorName arrayMapHelperTermIssue}`arr`.
If so, {anchorName arrayMapHelperTermIssue}`i` is incremented and the loop repeats.
If not, the program terminates.
Because {anchorTerm arrayMapHelperTermIssue}`arr.size` is a finite number, {anchorName arrayMapHelperTermIssue}`i` can be incremented only a finite number of times.
Even though no argument to the function decreases on each call, {anchorTerm ArrayMapHelperOk}`arr.size - i` decreases toward zero.

The value that decreases at each recursive call is called a _measure_.
Lean can be instructed to use a specific expression as the measure of termination by providing a {kw}`termination_by` clause at the end of a definition.
For {anchorName ArrayMapHelperOk}`arrayMapHelper`, the explicit measure looks like this:

```anchor ArrayMapHelperOk
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
termination_by arr.size - i
```

A similar termination proof can be used to write {anchorName ArrayFind}`Array.find`, a function that finds the first element in an array that satisfies a Boolean function and returns both the element and its index:

```anchor ArrayFind
def Array.find (arr : Array α) (p : α → Bool) :
    Option (Nat × α) :=
  findHelper arr p 0
```
Once again, the helper function terminates because {lit}`arr.size - i` decreases as {lit}`i` increases:

```anchor ArrayFindHelper
def findHelper (arr : Array α) (p : α → Bool)
    (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
```

Adding a question mark to {kw}`termination_by` (that is, using {kw}`termination_by?`) causes Lean to explicitly suggest the measure that it chose:
```anchor ArrayFindHelperSugg
def findHelper (arr : Array α) (p : α → Bool)
    (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
termination_by?
```
```anchorInfo ArrayFindHelperSugg
Try this: termination_by arr.size - i
```

Not all termination arguments are as quite as simple as this one.
However, the basic structure of identifying some expression based on the function's arguments that will decrease in each call occurs in all termination proofs.
Sometimes, creativity can be required in order to figure out just why a function terminates, and sometimes Lean requires additional proofs in order to accept that the measure in fact decreases.



# Exercises
%%%
tag := "array-termination-exercises"
%%%

 * Implement a {anchorTerm ForMArr}`ForM m (Array α)` instance on arrays using a tail-recursive accumulator-passing function and a {kw}`termination_by` clause.
 * Reimplement {anchorName ArrayMap}`Array.map`, {anchorName ArrayFind}`Array.find`, and the {anchorName ForMArr}`ForM` instance using {kw}`for`{lit}` ... `{kw}`in`{lit}` ...` loops in the identity monad and compare the resulting code.
 * Reimplement array reversal using a {kw}`for`{lit}` ... `{kw}`in`{lit}` ...` loop in the identity monad. Compare it to the tail-recursive function.
