# Proving Equivalence

Programs that have been rewritten to use tail recursion and an accumulator can look quite different from the original program.
The original recursive function is often much easier to understand, but it runs the risk of exhausting the stack at run time.
After testing both versions of the program on examples to rule out simple bugs, proofs can be used to show once and for all that the programs are equivalent.

## Proving `sum` Equal

To prove that both versions of `sum` are equal, begin by writing the theorem statement with a stub proof:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean sumEq0}}
```
As expected, Lean describes an unsolved goal:
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean sumEq0}}
```

The `rfl` tactic cannot be applied here, because `NonTail.sum` and `Tail.sum` are not definitionally equal.
Functions can be equal in more ways than just definitional equality, however.
It is also possible to prove that two functions are equal by proving that they produce equal outputs for the same input.
In other words, \\( f = g \\) can be proved by proving that \\( f(x) = g(x) \\) for all possible inputs \\( x \\).
This principle is called _function extensionality_.
Function extensionality is exactly the reason why `NonTail.sum` equals `Tail.sum`: they both sum lists of numbers.

In Lean's tactic language, function extensionality is invoked using `funext`, followed by a name to be used for the arbitrary argument.
The arbitrary argument is added as an assumption to the context, and the goal changes to require a proof that the functions applied to this argument are equal:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean sumEq1}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean sumEq1}}
```

This goal can be proved by induction on the argument `xs`.
Both `sum` functions return `0` when applied to the empty list, which serves as a base case.
Adding a number to the beginning of the input list causes both functions to add that number to the result, which serves as an induction step.
Invoking the `induction` tactic results in two goals:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean sumEq2a}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean sumEq2a}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean sumEq2b}}
```

The base case for `nil` can be solved using `rfl`, because both functions return `0` when passed the empty list:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean sumEq3}}
```

The first step in solving the induction step is to simplify the goal, asking `simp` to unfold `NonTail.sum` and `Tail.sum`:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean sumEq4}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean sumEq4}}
```
Unfolding `Tail.sum` revealed that it immediately delegates to `Tail.sumHelper`, which should also be simplified:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean sumEq5}}
```
In the resulting goal, `sumHelper` has taken a step of computation and added `y` to the accumulator:
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean sumEq5}}
```
Rewriting with the induction hypothesis removes all mentions of `NonTail.sum` from the goal:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean sumEq6}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean sumEq6}}
```
This new goal states that adding some number to the sum of a list is the same as using that number as the initial accumulator in `sumHelper`.
For the sake of clarity, this new goal can be proved as a separate theorem:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean sumEqHelperBad0}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean sumEqHelperBad0}}
```
Once again, this is a proof by induction where the base case uses `rfl`:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean sumEqHelperBad1}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean sumEqHelperBad1}}
```
Because this is an inductive step, the goal should be simplified until it matches the induction hypothesis `ih`.
Simplifying, using the definitions of `Tail.sum` and `Tail.sumHelper`, results in the following:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean sumEqHelperBad2}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean sumEqHelperBad2}}
```
Ideally, the induction hypothesis could be used to replace `Tail.sumHelper (y + n) ys`, but they don't match.
The induction hypothesis can be used for `Tail.sumHelper n ys`, not `Tail.sumHelper (y + n) ys`.
In other words, this proof is stuck.

## A Second Attempt

Rather than attempting to muddle through the proof, it's time to take a step back and think.
Why is it that the tail-recursive version of the function is equal to the non-tail-recursive version?
Fundamentally speaking, at each entry in the list, the accumulator grows by the same amount as would be added to the result of the recursion.
This insight can be used to write an elegant proof.
Crucially, the proof by induction must be set up such that the induction hypothesis can be applied to _any_ accumulator value.

Discarding the prior attempt, the insight can be encoded as the following statement:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqHelper0}}
```
In this statement, it's very important that `n` is part of the type that's after the colon.
The resulting goal begins with `∀ (n : Nat)`, which is short for "For all `n`":
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqHelper0}}
```
Using the induction tactic results in goals that include this "for all" statement:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqHelper1a}}
```
In the `nil` case, the goal is:
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqHelper1a}}
```
For the induction step for `cons`, both the induction hypothesis and the specific goal contain the "for all `n`":
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqHelper1b}}
```
In other words, the goal has become more challenging to prove, but the induction hypothesis is correspondingly more useful.

A mathematical proof for a statement that beings with "for all \\( x \\)" should assume some arbitrary \\( x \\), and prove the statement.
"Arbitrary" means that no additional properties of \\( x \\) are assumed, so the resulting statement will work for _any_ \\( x \\).
In Lean, a "for all" statement is a dependent function: no matter which specific value it is applied to, it will return evidence of the proposition.
Similarly, the process of picking an arbitrary \\( x \\) is the same as using ``fun x => ...``.
In the tactic language, this process of selecting an arbitrary \\( x \\) is performed using the `intro` tactic, which produces the function behind the scenes when the tactic script has completed.
The `intro` tactic should be provided with the name to be used for this arbitrary value.

Using the `intro` tactic in the `nil` case removes the `∀ (n : Nat),` from the goal, and adds an assumption `n : Nat`:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqHelper2}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqHelper2}}
```
Both sides of this propositional equality are definitionally equal to `n`, so `rfl` suffices:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqHelper3}}
```
The `cons` goal also contains a "for all":
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqHelper3}}
```
This suggests the use of `intro`.
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqHelper4}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqHelper4}}
```
The proof goal now contains both `NonTail.sum` and `Tail.sumHelper` applied to `y :: ys`.
The simplifier can make the next step more clear:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqHelper5}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqHelper5}}
```
This goal is very close to matching the induction hypothesis.
There are two ways in which it does not match:
 * The left-hand side of the equation is `n + (y + NonTail.sum ys)`, but the induction hypothesis needs the left-hand side to be a number added to `NonTail.sum ys`.
   In other words, this goal should be rewritten to `(n + y) + NonTail.sum ys`, which is valid because addition of natural numbers is associative.
 * When the left side has been rewritten to `(y + n) + NonTail.sum ys`, the accumulator argument on the right side should be `n + y` rather than `y + n` in order to match.
   This rewrite is valid because addition is also commutative.

The associativity and commutativity of addition have already been proved in Lean's standard library.
The proof of associativity is named `{{#example_in Examples/ProgramsProofs/TCO.lean NatAddAssoc}}`, and its type is `{{#example_out Examples/ProgramsProofs/TCO.lean NatAddAssoc}}`, while the proof of commutativity is called `{{#example_in Examples/ProgramsProofs/TCO.lean NatAddComm}}` and has type `{{#example_out Examples/ProgramsProofs/TCO.lean NatAddComm}}`.
Normally, the `rw` tactic is provided with an expression whose type is an equality.
However, if the argument is instead a dependent function whose return type is an equality, it attempts to find arguments to the function that would allow the equality to match something in the goal.
There is only one opportunity to apply associativity, though the direction of the rewrite must be reversed because the right side of the equality in `{{#example_in Examples/ProgramsProofs/TCO.lean NatAddAssoc}}` is the one that matches the proof goal:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqHelper6}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqHelper6}}
```
Rewriting directly with `{{#example_in Examples/ProgramsProofs/TCO.lean NatAddComm}}`, however, leads to the wrong result.
The `rw` tactic guesses the wrong location for the rewrite, leading to an unintended goal:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqHelper7}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqHelper7}}
```
This can be fixed by explicitly providing `y` and `n` as arguments to `Nat.add_comm`:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqHelper8}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqHelper8}}
```
The goal now matches the induction hypothesis.
In particular, the induction hypothesis's type is a dependent function type.
Applying `ih` to `n + y` results in exactly the desired type.
The `exact` tactic completes a proof goal if its argument has exactly the desired type:
```lean
{{#example_decl Examples/ProgramsProofs/TCO.lean nonTailEqHelperDone}}
```

The actual proof requires only a little additional work to get the goal to match the helper's type.
The first step is still to invoke function extensionality:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqReal0}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqReal0}}
```
The next step is unfold `Tail.sum`, exposing `Tail.sumHelper`:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqReal1}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqReal1}}
```
Having done this, the types almost match.
However, the helper has an additional addend on the left side.
In other words, the proof goal is `NonTail.sum xs = Tail.sumHelper 0 xs`, but applying `non_tail_sum_eq_helper_accum` to `xs` and `0` yields the type `0 + NonTail.sum xs = Tail.sumHelper 0 xs`.
Another standard library proof, `{{#example_in Examples/ProgramsProofs/TCO.lean NatZeroAdd}}`, has type `{{#example_out Examples/ProgramsProofs/TCO.lean NatZeroAdd}}`.
Applying this function to `NonTail.sum xs` results in an expression with type `{{#example_out Examples/ProgramsProofs/TCO.lean NatZeroAddApplied}}`, so rewriting from right to left results in the desired goal:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean nonTailEqReal2}}
```
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean nonTailEqReal2}}
```
Finally, the helper can be used to complete the proof:
```lean
{{#example_decl Examples/ProgramsProofs/TCO.lean nonTailEqRealDone}}
```

This proof demonstrates a general pattern that can be used when proving that an accumulator-passing tail-recursive function is equal to the non-tail-recursive version.
The first step is to discover the relationship between the starting accumulator argument and the final result.
For instance, beginning `Tail.sumHelper` with an accumulator of `n` results in the final sum being added to `n`, and beginning `Tail.reverseHelper` with an accumulator of `ys` results in the final reversed list being prepended to `ys`.
The second step is to write down this relationship as a theorem statement and prove it by induction.
While the accumulator is always initialized with some neutral value in practice, such as `0` or `[]`, this more general statement that allows the starting accumulator to be any value is what's needed to get a strong enough induction hypothesis.
Finally, using this helper theorem with the actual initial accumulator value results in the desired proof.
For example, in `non_tail_sum_eq_tail_sum`, the accumulator is specified to be `0`.
This may require rewriting the goal to make the neutral initial accumulator values occur in the right place.



## Exercise

### Warming Up

Write your own proofs for `Nat.zero_add`, `Nat.add_assoc`, and `Nat.add_comm` using the `induction` tactic.
 
### More Accumulator Proofs

#### Reversing Lists

Adapt the proof for `sum` into a proof for `NonTail.reverse` and `Tail.reverse`.
The first step is to think about the relationship between the accumulator value being passed to `Tail.reverseHelper` and the non-tail-recursive reverse.
Just as adding a number to the accumulator in `Tail.sumHelper` is the same as adding it to the overall sum, using `List.cons` to add a new entry to the accumulator in `Tail.reverseHelper` is equivalent to some change to the overall result.
Try three or four different accumulator values with pencil and paper until the relationship becomes clear.
Use this relationship to prove a suitable helper theorem.
Then, write down the overall theorem.
Because `NonTail.reverse` and `Tail.reverse` are polymorphic, stating their equality requires the use of `@` to stop Lean from trying to figure out which type to use for `α`.
Once `α` is treated as an ordinary argument, `funext` should be invoked with both `α` and `xs`:
```lean
{{#example_in Examples/ProgramsProofs/TCO.lean reverseEqStart}}
```
This results in a suitable goal:
```output error
{{#example_out Examples/ProgramsProofs/TCO.lean reverseEqStart}}
```


#### Factorial

Prove that `NonTail.factorial` from the exercises in the previous section is equal to your tail-recursive solution by finding the relationship between the accumulator and the result and proving a suitable helper theorem.
