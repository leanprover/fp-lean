import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.TCO"

#doc (Manual) "Proving Equivalence" =>

Programs that have been rewritten to use tail recursion and an accumulator can look quite different from the original program.
The original recursive function is often much easier to understand, but it runs the risk of exhausting the stack at run time.
After testing both versions of the program on examples to rule out simple bugs, proofs can be used to show once and for all that the programs are equivalent.

# Proving `sum` Equal

To prove that both versions of `sum` are equal, begin by writing the theorem statement with a stub proof:
```anchor sumEq0
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  skip
```
As expected, Lean describes an unsolved goal:
```anchorError sumEq0
unsolved goals
⊢ NonTail.sum = Tail.sum
```

The `rfl` tactic cannot be applied here, because `NonTail.sum` and `Tail.sum` are not definitionally equal.
Functions can be equal in more ways than just definitional equality, however.
It is also possible to prove that two functions are equal by proving that they produce equal outputs for the same input.
In other words, $`f = g` can be proved by proving that $`f(x) = g(x)` for all possible inputs $`x`.
This principle is called _function extensionality_.
Function extensionality is exactly the reason why `NonTail.sum` equals `Tail.sum`: they both sum lists of numbers.

In Lean's tactic language, function extensionality is invoked using `funext`, followed by a name to be used for the arbitrary argument.
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

This goal can be proved by induction on the argument `xs`.
Both `sum` functions return `0` when applied to the empty list, which serves as a base case.
Adding a number to the beginning of the input list causes both functions to add that number to the result, which serves as an induction step.
Invoking the `induction` tactic results in two goals:
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

The base case for `nil` can be solved using `rfl`, because both functions return `0` when passed the empty list:
```anchor sumEq3
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih => skip
```

The first step in solving the induction step is to simplify the goal, asking `simp` to unfold `NonTail.sum` and `Tail.sum`:
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
Unfolding `Tail.sum` revealed that it immediately delegates to `Tail.sumHelper`, which should also be simplified:
```anchor sumEq5
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]
```
In the resulting goal, `sumHelper` has taken a step of computation and added `y` to the accumulator:
```anchorError sumEq5
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + NonTail.sum ys = Tail.sumHelper y ys
```
Rewriting with the induction hypothesis removes all mentions of `NonTail.sum` from the goal:
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
This new goal states that adding some number to the sum of a list is the same as using that number as the initial accumulator in `sumHelper`.
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
Once again, this is a proof by induction where the base case uses `rfl`:
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
Because this is an inductive step, the goal should be simplified until it matches the induction hypothesis `ih`.
Simplifying, using the definitions of `Tail.sum` and `Tail.sumHelper`, results in the following:
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
Ideally, the induction hypothesis could be used to replace `Tail.sumHelper (y + n) ys`, but they don't match.
The induction hypothesis can be used for `Tail.sumHelper n ys`, not `Tail.sumHelper (y + n) ys`.
In other words, this proof is stuck.

# A Second Attempt

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
In this statement, it's very important that `n` is part of the type that's after the colon.
The resulting goal begins with `∀ (n : Nat)`, which is short for "For all `n`":
```anchorError nonTailEqHelper0
unsolved goals
xs : List Nat
⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
```
Using the induction tactic results in goals that include this "for all" statement:
```anchor nonTailEqHelper1a
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => skip
  | cons y ys ih => skip
```
In the `nil` case, the goal is:
```anchorError nonTailEqHelper1a
unsolved goals
case nil
⊢ ∀ (n : Nat), n + NonTail.sum [] = Tail.sumHelper n []
```
For the induction step for `cons`, both the induction hypothesis and the specific goal contain the "for all `n`":
```anchorError nonTailEqHelper1b
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
In other words, the goal has become more challenging to prove, but the induction hypothesis is correspondingly more useful.

A mathematical proof for a statement that beings with "for all $`x`" should assume some arbitrary $`x`, and prove the statement.
"Arbitrary" means that no additional properties of $`x` are assumed, so the resulting statement will work for _any_ $`x`.
In Lean, a "for all" statement is a dependent function: no matter which specific value it is applied to, it will return evidence of the proposition.
Similarly, the process of picking an arbitrary $`x` is the same as using ``fun x => ...``.
In the tactic language, this process of selecting an arbitrary $`x` is performed using the `intro` tactic, which produces the function behind the scenes when the tactic script has completed.
The `intro` tactic should be provided with the name to be used for this arbitrary value.

Using the `intro` tactic in the `nil` case removes the `∀ (n : Nat),` from the goal, and adds an assumption `n : Nat`:
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
Both sides of this propositional equality are definitionally equal to `n`, so `rfl` suffices:
```anchor nonTailEqHelper3
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih => skip
```
The `cons` goal also contains a "for all":
```anchorError nonTailEqHelper3
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
```
This suggests the use of `intro`.
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
The proof goal now contains both `NonTail.sum` and `Tail.sumHelper` applied to `y :: ys`.
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
 * The left-hand side of the equation is `n + (y + NonTail.sum ys)`, but the induction hypothesis needs the left-hand side to be a number added to `NonTail.sum ys`.
   In other words, this goal should be rewritten to `(n + y) + NonTail.sum ys`, which is valid because addition of natural numbers is associative.
 * When the left side has been rewritten to `(y + n) + NonTail.sum ys`, the accumulator argument on the right side should be `n + y` rather than `y + n` in order to match.
   This rewrite is valid because addition is also commutative.

The associativity and commutativity of addition have already been proved in Lean's standard library.
The proof of associativity is named {anchorTerm NatAddAssoc}`Nat.add_assoc`, and its type is {anchorTerm NatAddAssoc}`(n m k : Nat) → (n + m) + k = n + (m + k)`, while the proof of commutativity is called {anchorTerm NatAddComm}`Nat.add_comm` and has type {anchorTerm NatAddComm}`(n m : Nat) → n + m = m + n`.
Normally, the `rw` tactic is provided with an expression whose type is an equality.
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
The `rw` tactic guesses the wrong location for the rewrite, leading to an unintended goal:
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
This can be fixed by explicitly providing `y` and `n` as arguments to `Nat.add_comm`:
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
Applying `ih` to `n + y` results in exactly the desired type.
The `exact` tactic completes a proof goal if its argument has exactly the desired type:

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
The next step is unfold `Tail.sum`, exposing `Tail.sumHelper`:
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
In other words, the proof goal is `NonTail.sum xs = Tail.sumHelper 0 xs`, but applying `non_tail_sum_eq_helper_accum` to `xs` and `0` yields the type `0 + NonTail.sum xs = Tail.sumHelper 0 xs`.
Another standard library proof, {anchorTerm NatZeroAdd}`Nat.zero_add`, has type {anchorTerm NatZeroAdd}`(n : Nat) → 0 + n = n`.
Applying this function to `NonTail.sum xs` results in an expression with type {anchorTerm NatZeroAddApplied}`0 + NonTail.sum xs = NonTail.sum xs`, so rewriting from right to left results in the desired goal:
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
For instance, beginning `Tail.sumHelper` with an accumulator of `n` results in the final sum being added to `n`, and beginning `Tail.reverseHelper` with an accumulator of `ys` results in the final reversed list being prepended to `ys`.
The second step is to write down this relationship as a theorem statement and prove it by induction.
While the accumulator is always initialized with some neutral value in practice, such as `0` or `[]`, this more general statement that allows the starting accumulator to be any value is what's needed to get a strong enough induction hypothesis.
Finally, using this helper theorem with the actual initial accumulator value results in the desired proof.
For example, in `non_tail_sum_eq_tail_sum`, the accumulator is specified to be `0`.
This may require rewriting the goal to make the neutral initial accumulator values occur in the right place.



# Exercise

## Warming Up

Write your own proofs for `Nat.zero_add`, `Nat.add_assoc`, and `Nat.add_comm` using the `induction` tactic.

## More Accumulator Proofs

### Reversing Lists

Adapt the proof for `sum` into a proof for `NonTail.reverse` and `Tail.reverse`.
The first step is to think about the relationship between the accumulator value being passed to `Tail.reverseHelper` and the non-tail-recursive reverse.
Just as adding a number to the accumulator in `Tail.sumHelper` is the same as adding it to the overall sum, using `List.cons` to add a new entry to the accumulator in `Tail.reverseHelper` is equivalent to some change to the overall result.
Try three or four different accumulator values with pencil and paper until the relationship becomes clear.
Use this relationship to prove a suitable helper theorem.
Then, write down the overall theorem.
Because `NonTail.reverse` and `Tail.reverse` are polymorphic, stating their equality requires the use of `@` to stop Lean from trying to figure out which type to use for `α`.
Once `α` is treated as an ordinary argument, `funext` should be invoked with both `α` and `xs`:
```anchor reverseEqStart
theorem non_tail_reverse_eq_tail_reverse : @NonTail.reverse = @Tail.reverse := by
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

Prove that `NonTail.factorial` from the exercises in the previous section is equal to your tail-recursive solution by finding the relationship between the accumulator and the result and proving a suitable helper theorem.
