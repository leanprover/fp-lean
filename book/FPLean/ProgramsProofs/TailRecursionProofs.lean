import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.TCO"

#doc (Manual) "Proving Equivalence" =>
%%%
tag := "proving-tail-rec-equiv"
%%%

Programs that have been rewritten to use tail recursion and an accumulator can look quite different from the original program.
The original recursive function is often much easier to understand, but it runs the risk of exhausting the stack at run time.
After testing both versions of the program on examples to rule out simple bugs, proofs can be used to show once and for all that the programs are equivalent.

# Proving {lit}`sum` Equal
%%%
tag := "proving-sum-equal"
%%%

To prove that both versions of {lit}`sum` are equal, begin by writing the theorem statement with a stub proof:
```anchor sumEq0
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  skip
```
As expected, Lean describes an unsolved goal:
```anchorError sumEq0
unsolved goals
⊢ NonTail.sum = Tail.sum
```

The {kw}`rfl` tactic cannot be applied here because {anchorName sumEq0}`NonTail.sum` and {anchorName sumEq0}`Tail.sum` are not definitionally equal.
Functions can be equal in more ways than just definitional equality, however.
It is also possible to prove that two functions are equal by proving that they produce equal outputs for the same input.
In other words, $`f = g` can be proved by proving that $`f(x) = g(x)` for all possible inputs $`x`.
This principle is called _function extensionality_.
Function extensionality is exactly the reason why {anchorName sumEq0}`NonTail.sum` equals {anchorName sumEq0}`Tail.sum`: they both sum lists of numbers.

In Lean's tactic language, function extensionality is invoked using {anchorTerm sumEq1}`funext`, followed by a name to be used for the arbitrary argument.
The arbitrary argument is added as an assumption to the context, and the goal changes to require a proof that the functions applied to this argument are equal:
```anchor sumEq1
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
```
```anchorError sumEq1
unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sum xs
```

This goal can be proved by induction on the argument {anchorName sumEq1}`xs`.
Both {lit}`sum` functions return {anchorTerm TailSum}`0` when applied to the empty list, which serves as a base case.
Adding a number to the beginning of the input list causes both functions to add that number to the result, which serves as an induction step.
Invoking the {anchorTerm sumEq2a}`induction` tactic results in two goals:
```anchor sumEq2a
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => skip
  | cons y ys ih => skip
```
```anchorError sumEq2a
unsolved goals
case h.nil
⊢ NonTail.sum [] = Tail.sum []
```
```anchorError sumEq2b
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ NonTail.sum (y :: ys) = Tail.sum (y :: ys)
```

The base case for {anchorName sumEq3}`nil` can be solved using {anchorTerm sumEq3}`rfl`, because both functions return {anchorTerm TailSum}`0` when passed the empty list:
```anchor sumEq3
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih => skip
```

The first step in solving the induction step is to simplify the goal, asking {anchorTerm sumEq4}`simp` to unfold {anchorName sumEq4}`NonTail.sum` and {anchorName sumEq4}`Tail.sum`:
```anchor sumEq4
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum]
```
```anchorError sumEq4
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + NonTail.sum ys = Tail.sumHelper 0 (y :: ys)
```
Unfolding {anchorName sumEq5}`Tail.sum` revealed that it immediately delegates to {anchorName sumEq5}`Tail.sumHelper`, which should also be simplified:
```anchor sumEq5
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]
```
In the resulting goal, {anchorName TailSum}`sumHelper` has taken a step of computation and added {anchorName sumEq5}`y` to the accumulator:
```anchorError sumEq5
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + NonTail.sum ys = Tail.sumHelper y ys
```
Rewriting with the induction hypothesis removes all mentions of {anchorName sumEq6}`NonTail.sum` from the goal:
```anchor sumEq6
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]
    rw [ih]
```
```anchorError sumEq6
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + Tail.sum ys = Tail.sumHelper y ys
```
This new goal states that adding some number to the sum of a list is the same as using that number as the initial accumulator in {anchorName TailSum}`sumHelper`.
For the sake of clarity, this new goal can be proved as a separate theorem:
```anchor sumEqHelperBad0
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  skip
```
```anchorError sumEqHelperBad0
unsolved goals
xs : List Nat
n : Nat
⊢ n + Tail.sum xs = Tail.sumHelper n xs
```
Once again, this is a proof by induction where the base case uses {anchorTerm sumEqHelperBad1}`rfl`:
```anchor sumEqHelperBad1
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => skip
```
```anchorError sumEqHelperBad1
unsolved goals
case cons
n y : Nat
ys : List Nat
ih : n + Tail.sum ys = Tail.sumHelper n ys
⊢ n + Tail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
Because this is an inductive step, the goal should be simplified until it matches the induction hypothesis {anchorName sumEqHelperBad2}`ih`.
Simplifying, using the definitions of {anchorName sumEqHelperBad2}`Tail.sum` and {anchorName sumEqHelperBad2}`Tail.sumHelper`, results in the following:
```anchor sumEqHelperBad2
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [Tail.sum, Tail.sumHelper]
```
```anchorError sumEqHelperBad2
unsolved goals
case cons
n y : Nat
ys : List Nat
ih : n + Tail.sum ys = Tail.sumHelper n ys
⊢ n + Tail.sumHelper y ys = Tail.sumHelper (y + n) ys
```
Ideally, the induction hypothesis could be used to replace {lit}`Tail.sumHelper (y + n) ys`, but they don't match.
The induction hypothesis can be used for {lit}`Tail.sumHelper n ys`, not {lit}`Tail.sumHelper (y + n) ys`.
In other words, this proof is stuck.

# A Second Attempt
%%%
tag := "proving-sum-equal-again"
%%%

Rather than attempting to muddle through the proof, it's time to take a step back and think.
Why is it that the tail-recursive version of the function is equal to the non-tail-recursive version?
Fundamentally speaking, at each entry in the list, the accumulator grows by the same amount as would be added to the result of the recursion.
This insight can be used to write an elegant proof.
Crucially, the proof by induction must be set up such that the induction hypothesis can be applied to _any_ accumulator value.

Discarding the prior attempt, the insight can be encoded as the following statement:
```anchor nonTailEqHelper0
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  skip
```
In this statement, it's very important that {anchorName nonTailEqHelper0}`n` is part of the type that's after the colon.
The resulting goal begins with {lit}`∀ (n : Nat)`, which is short for “For all {lit}`n`”:
```anchorError nonTailEqHelper0
unsolved goals
xs : List Nat
⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
```
Using the induction tactic results in goals that include this “for all” statement:
```anchor nonTailEqHelper1a
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => skip
  | cons y ys ih => skip
```
In the {anchorName nonTailEqHelper1a}`nil` case, the goal is:
```anchorError nonTailEqHelper1a
unsolved goals
case nil
⊢ ∀ (n : Nat), n + NonTail.sum [] = Tail.sumHelper n []
```
For the induction step for {anchorName nonTailEqHelper1a}`cons`, both the induction hypothesis and the specific goal contain the “for all {lit}`n`”:
```anchorError nonTailEqHelper1b
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
In other words, the goal has become more challenging to prove, but the induction hypothesis is correspondingly more useful.

A mathematical proof for a statement that beings with “for all $`x`” should assume some arbitrary $`x`, and prove the statement.
“Arbitrary” means that no additional properties of $`x` are assumed, so the resulting statement will work for _any_ $`x`.
In Lean, a “for all” statement is a dependent function: no matter which specific value it is applied to, it will return evidence of the proposition.
Similarly, the process of picking an arbitrary $`x` is the same as using {lit}`fun x => ...`.
In the tactic language, this process of selecting an arbitrary $`x` is performed using the {kw}`intro` tactic, which produces the function behind the scenes when the tactic script has completed.
The {kw}`intro` tactic should be provided with the name to be used for this arbitrary value.

Using the {kw}`intro` tactic in the {anchorName nonTailEqHelper2}`nil` case removes the {lit}`∀ (n : Nat),` from the goal, and adds an assumption {lit}`n : Nat`:
```anchor nonTailEqHelper2
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => intro n
  | cons y ys ih => skip
```
```anchorError nonTailEqHelper2
unsolved goals
case nil
n : Nat
⊢ n + NonTail.sum [] = Tail.sumHelper n []
```
Both sides of this propositional equality are definitionally equal to {anchorName nonTailEqHelper3}`n`, so {anchorTerm nonTailEqHelper3}`rfl` suffices:
```anchor nonTailEqHelper3
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih => skip
```
The {anchorName nonTailEqHelper3}`cons` goal also contains a “for all”:
```anchorError nonTailEqHelper3
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
This suggests the use of {kw}`intro`.
```anchor nonTailEqHelper4
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
```
```anchorError nonTailEqHelper4
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
The proof goal now contains both {anchorName nonTailEqHelper5}`NonTail.sum` and {anchorName nonTailEqHelper5}`Tail.sumHelper` applied to {lit}`y :: ys`.
The simplifier can make the next step more clear:
```anchor nonTailEqHelper5
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
```
```anchorError nonTailEqHelper5
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + (y + NonTail.sum ys) = Tail.sumHelper (y + n) ys
```
This goal is very close to matching the induction hypothesis.
There are two ways in which it does not match:
 * The left-hand side of the equation is {lit}`n + (y + NonTail.sum ys)`, but the induction hypothesis needs the left-hand side to be a number added to {lit}`NonTail.sum ys`.
   In other words, this goal should be rewritten to {lit}`(n + y) + NonTail.sum ys`, which is valid because addition of natural numbers is associative.
 * When the left side has been rewritten to {lit}`(y + n) + NonTail.sum ys`, the accumulator argument on the right side should be {lit}`n + y` rather than {lit}`y + n` in order to match.
   This rewrite is valid because addition is also commutative.

The associativity and commutativity of addition have already been proved in Lean's standard library.
The proof of associativity is named {anchorTerm NatAddAssoc}`Nat.add_assoc`, and its type is {anchorTerm NatAddAssoc}`(n m k : Nat) → (n + m) + k = n + (m + k)`, while the proof of commutativity is called {anchorTerm NatAddComm}`Nat.add_comm` and has type {anchorTerm NatAddComm}`(n m : Nat) → n + m = m + n`.
Normally, the {kw}`rw` tactic is provided with an expression whose type is an equality.
However, if the argument is instead a dependent function whose return type is an equality, it attempts to find arguments to the function that would allow the equality to match something in the goal.
There is only one opportunity to apply associativity, though the direction of the rewrite must be reversed because the right side of the equality in {anchorTerm NatAddAssoc}`(n + m) + k = n + (m + k)` is the one that matches the proof goal:
```anchor nonTailEqHelper6
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
```
```anchorError nonTailEqHelper6
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + y + NonTail.sum ys = Tail.sumHelper (y + n) ys
```
Rewriting directly with {anchorTerm nonTailEqHelper7}`rw [Nat.add_comm]`, however, leads to the wrong result.
The {kw}`rw` tactic guesses the wrong location for the rewrite, leading to an unintended goal:
```anchor nonTailEqHelper7
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm]
```
```anchorError nonTailEqHelper7
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ NonTail.sum ys + (n + y) = Tail.sumHelper (y + n) ys
```
This can be fixed by explicitly providing {anchorName nonTailEqHelper8}`y` and {anchorName nonTailEqHelper8}`n` as arguments to {anchorName nonTailEqHelper8}`Nat.add_comm`:
```anchor nonTailEqHelper8
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm y n]
```
```anchorError nonTailEqHelper8
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + y + NonTail.sum ys = Tail.sumHelper (n + y) ys
```
The goal now matches the induction hypothesis.
In particular, the induction hypothesis's type is a dependent function type.
Applying {anchorName nonTailEqHelperDone}`ih` to {anchorTerm nonTailEqHelperDone}`n + y` results in exactly the desired type.
The {kw}`exact` tactic completes a proof goal if its argument has exactly the desired type:

```anchor nonTailEqHelperDone
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => intro n; rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm y n]
    exact ih (n + y)
```

The actual proof requires only a little additional work to get the goal to match the helper's type.
The first step is still to invoke function extensionality:
```anchor nonTailEqReal0
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
```
```anchorError nonTailEqReal0
unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sum xs
```
The next step is unfold {anchorName nonTailEqReal1}`Tail.sum`, exposing {anchorName TailSum}`Tail.sumHelper`:
```anchor nonTailEqReal1
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
```
```anchorError nonTailEqReal1
unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sumHelper 0 xs
```
Having done this, the types almost match.
However, the helper has an additional addend on the left side.
In other words, the proof goal is {lit}`NonTail.sum xs = Tail.sumHelper 0 xs`, but applying {anchorName nonTailEqHelper0}`non_tail_sum_eq_helper_accum` to {anchorName nonTailEqReal2}`xs` and {anchorTerm NatZeroAdd}`0` yields the type {lit}`0 + NonTail.sum xs = Tail.sumHelper 0 xs`.
Another standard library proof, {anchorTerm NatZeroAdd}`Nat.zero_add`, has type {anchorTerm NatZeroAdd}`(n : Nat) → 0 + n = n`.
Applying this function to {anchorTerm nonTailEqReal2}`NonTail.sum xs` results in an expression with type {anchorTerm NatZeroAddApplied}`0 + NonTail.sum xs = NonTail.sum xs`, so rewriting from right to left results in the desired goal:
```anchor nonTailEqReal2
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
```
```anchorError nonTailEqReal2
unsolved goals
case h
xs : List Nat
⊢ 0 + NonTail.sum xs = Tail.sumHelper 0 xs
```
Finally, the helper can be used to complete the proof:

```anchor nonTailEqRealDone
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0
```

This proof demonstrates a general pattern that can be used when proving that an accumulator-passing tail-recursive function is equal to the non-tail-recursive version.
The first step is to discover the relationship between the starting accumulator argument and the final result.
For instance, beginning {anchorName TailSum}`Tail.sumHelper` with an accumulator of {anchorName accum_stmt}`n` results in the final sum being added to {anchorName accum_stmt}`n`, and beginning {anchorName accum_stmt}`Tail.reverseHelper` with an accumulator of {anchorName accum_stmt}`ys` results in the final reversed list being prepended to {anchorName accum_stmt}`ys`.
The second step is to write down this relationship as a theorem statement and prove it by induction.
While the accumulator is always initialized with some neutral value in practice, such as {anchorTerm TailSum}`0` or {anchorTerm accum_stmt}`[]`, this more general statement that allows the starting accumulator to be any value is what's needed to get a strong enough induction hypothesis.
Finally, using this helper theorem with the actual initial accumulator value results in the desired proof.
For example, in {anchorName nonTailEqRealDone}`non_tail_sum_eq_tail_sum`, the accumulator is specified to be {anchorTerm TailSum}`0`.
This may require rewriting the goal to make the neutral initial accumulator values occur in the right place.

# Functional Induction
%%%
tag := "fun-induction"
%%%

The proof of {anchorName nonTailEqRealDone}`non_tail_sum_eq_helper_accum` follows the implementation of {anchorName TailSum}`Tail.sumHelper` closely.
There is not, however, a perfect match between the implementation and the structure expected by mathematical induction, which makes it necessary to manage the assumption {anchorName nonTailEqHelperDone}`n` carefully.
This is a small amount of work in the case of {anchorName nonTailEqHelperDone}`non_tail_sum_eq_helper_accum`, but proofs about functions whose definitions are further from the structure expected by {tactic}`induction` require more bookkeeping.

In addition to proving theorems about recursive functions by induction on one of the arguments, Lean supports proofs by induction on the recursive call structure of functions.
This {deftech}_functional induction_ results in a base case for each branch of the function's control flow that does not include a recursive call, and inductive steps for each branch that does.
A proof by functional induction should demonstrate that the theorem holds for the non-recursive branches, and that if the theorem holds for the result of each recursive call, then it also holds for the result of the recursive branch.

:::paragraph
Using functional induction simplifies {anchorName nonTailEqHelperFunInd1}`non_tail_sum_eq_helper_accum`:
```anchor nonTailEqHelperFunInd1
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper with
  | case1 n => skip
  | case2 n y ys ih => skip
```
Each branch of the proof matches the corresponding branch of {anchorName TailSum}`Tail.sumHelper`:
```anchorTerm TailSum
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs
```
In the first, {anchorTerm nonTailEqHelperFunInd1}`case1`, the right side of the equality is the accumulator value, called {anchorName nonTailEqHelperFunInd1}`n` in the proof:
```anchorError nonTailEqHelperFunInd1
unsolved goals
case case1
n : Nat
⊢ n + NonTail.sum [] = n
```
In the second, {anchorTerm nonTailEqHelperFunInd1}`case2`, the right side of the equality is the next step in the tail-recursive loop:
```anchorError nonTailEqHelperFunInd1
unsolved goals
case case2
n y : Nat
ys : List Nat
ih : y + n + NonTail.sum ys = Tail.sumHelper (y + n) ys
⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper (y + n) ys
```
:::

:::paragraph
The resulting proof can be simpler.
The fundamentals of the argument, including the properties of addition that are used, are the same; however, the bookkeeping has been removed.
It is no longer necessary to manually juggle the accumulator value, and the induction hypothesis can be used directly instead of requiring instantiation:
```anchor nonTailEqHelperFunInd2
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper with
  | case1 n => simp [NonTail.sum]
  | case2 n y ys ih =>
    simp [NonTail.sum]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm n y]
    assumption
```
:::

:::paragraph
The {tactic}`grind` tactic is very well suited to this kind of goal.
Unlike {tactic}`simp` and {tactic}`rw`, it is not directional; internally, it accumulates a collection of facts until it either proves the goal completely or fails to do so.
It is preconfigured to use basic facts about arithmetic, such as the associativity and commutativity of addition, and it automatically uses local assumptions such as the induction hypothesis.
Using {tactic}`grind`, this proof becomes short and to-the-point:
```anchor nonTailEqHelperFunInd3
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper <;> grind [NonTail.sum]
```
This proof also matches the way the proof might be explained to a skilled programmer: “Just check both branches of {anchorName nonTailEqHelperFunInd3}`Tail.sumHelper`!”
:::

# Exercise
%%%
tag := "tail-recursion-proof-exercises"
%%%

## Warming Up
%%%
tag := none
%%%

Write your own proofs for {anchorName NatZeroAdd}`Nat.zero_add`, {anchorName NatAddAssoc}`Nat.add_assoc`, and {anchorName NatAddComm}`Nat.add_comm` using the {kw}`induction` tactic.

## More Accumulator Proofs
%%%
tag := none
%%%

### Reversing Lists
%%%
tag := none
%%%

Adapt the proof for {anchorName NonTailSum}`sum` into a proof for {anchorName NonTailReverse}`NonTail.reverse` and {anchorName TailReverse}`Tail.reverse`.
The first step is to think about the relationship between the accumulator value being passed to {anchorName TailReverse}`Tail.reverseHelper` and the non-tail-recursive reverse.
Just as adding a number to the accumulator in {anchorName TailSum}`Tail.sumHelper` is the same as adding it to the overall sum, using {anchorName names}`List.cons` to add a new entry to the accumulator in {anchorName TailReverse}`Tail.reverseHelper` is equivalent to some change to the overall result.
Try three or four different accumulator values with pencil and paper until the relationship becomes clear.
Use this relationship to prove a suitable helper theorem.
Try proving this helper theorem both using induction on lists and via functional induction.
Then, write down the overall theorem.
Because {anchorName reverseEqStart}`NonTail.reverse` and {anchorName TailReverse}`Tail.reverse` are polymorphic, stating their equality requires the use of {lit}`@` to stop Lean from trying to figure out which type to use for {anchorName reverseEqStart}`α`.
Once {anchorName reverseEqStart}`α` is treated as an ordinary argument, {kw}`funext` should be invoked with both {anchorName reverseEqStart}`α` and {anchorName reverseEqStart}`xs`:
```anchor reverseEqStart
theorem non_tail_reverse_eq_tail_reverse :
    @NonTail.reverse = @Tail.reverse := by
  funext α xs
```
This results in a suitable goal:
```anchorError reverseEqStart
unsolved goals
case h.h
α : Type u_1
xs : List α
⊢ NonTail.reverse xs = Tail.reverse xs
```


### Factorial
%%%
tag := none
%%%


Prove that {anchorName NonTailFact}`NonTail.factorial` from the exercises in the previous section is equal to your tail-recursive solution by finding the relationship between the accumulator and the result and proving a suitable helper theorem.
