# More Inequalities

Lean's built-in proof automation is sufficient to check that `arrayMapHelper` and `findHelper` terminate.
All that was needed was to provide an expression whose value decreases with each recursive call.
However, Lean's built-in automation is not magic, and it often needs some help.

## Merge Sort

One example of a function whose termination proof is non-trivial is merge sort on `List`.
Merge sort consists of two phases: first, a list is split in half.
Each half is sorted using merge sort, and then the results are merged using a function that combines two sorted lists into a larger sorted list.
The base cases are the empty list and the singleton list, both of which are already considered to be sorted.

To merge two sorted lists, there are two basic cases to consider:
 1. If one of the input lists is empty, then the result is the other list.
 2. If both lists are non-empty, then their heads should be compared. The result of the function is the smaller of the two heads, followed by the result of merging the remaining entries of both lists.

This is not structurally recursive on either list.
The recursion terminates because an entry is removed from one of the two lists in each recursive call, but it could be either list.
Behind the scenes, Lean uses this fact to prove that it terminates:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean merge}}
```


A simple way to split a list is to add each entry in the input list to two alternating output lists:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean splitList}}
```
This splitting function is structurally recursive.

Merge sort checks whether a base case has been reached.
If so, it returns the input list.
If not, it splits the input, and merges the result of sorting each half:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortNoTerm}}
```
Lean's pattern match compiler is able to tell that the assumption `h` introduced by the `if` that tests whether `xs.length < 2` rules out lists longer than one entry, so there is no "missing cases" error.
However, even though this program always terminates, it is not structurally recursive, and Lean is unable to automatically discover a decreasing measure:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortNoTerm}}
```
The reason it terminates is that `splitList` always returns lists that are shorter than its input, at least when applied to lists that contain at least two elements.
Thus, the length of `halves.fst` and `halves.snd` are less than the length of `xs`.
This can be expressed using a `termination_by` clause:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortGottaProveIt}}
```
With this clause, the error message changes.
Instead of complaining that the function isn't structurally recursive, Lean instead points out that it was unable to automatically prove that `(splitList xs).fst.length < xs.length`:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortGottaProveIt}}
```

## Splitting a List Makes it Shorter

It will also be necessary to prove that `(splitList xs).snd.length < xs.length`.
Because `splitList` alternates between adding entries to the two lists, it is easiest to prove both statements at once, so the structure of the proof can follow the algorithm used to implement `splitList`.
In other words, it is easiest to prove that `∀(lst : List), (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length`.

Unfortunately, the statement is false.
In particular, `{{#example_in Examples/ProgramsProofs/Inequalities.lean splitListEmpty}}` is `{{#example_out Examples/ProgramsProofs/Inequalities.lean splitListEmpty}}`. Both output lists have length `0`, which is not less than `0`, the length of the input list.
Similarly, `{{#example_in Examples/ProgramsProofs/Inequalities.lean splitListOne}}` evaluates to `{{#example_out Examples/ProgramsProofs/Inequalities.lean splitListOne}}`, and `["basalt"]` is not shorter than `["basalt"]`.
However, `{{#example_in Examples/ProgramsProofs/Inequalities.lean splitListTwo}}` evaluates to `{{#example_out Examples/ProgramsProofs/Inequalities.lean splitListTwo}}`, and both of these output lists are shorter than the input list.

It turns out that the lengths of the output lists are always less than or equal to the length of the input list, but they are only strictly shorter when the input list contains at least two entries.
It turns out to be easiest to prove the former statement, then extend it to the latter statement.
Begin with a theorem statement:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le0}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le0}}
```
Because `splitList` is structurally recursive on the list, the proof should use induction.
The structural recursion in `splitList` fits a proof by induction perfectly: the base case of the induction matches the base case of the recursion, and the inductive step matches the recursive call.
The `induction` tactic gives two goals:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le1a}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le1a}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le1b}}
```

The goal for the `nil` case can be proved by invoking the simplifier and instructing it to unfold the definition of `splitList`, because the length of the empty list is less than or equal to the length of the empty list.
Similarly, simplifying with `splitList` in the `cons` case places `Nat.succ` around the lengths in the goal:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le2}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le2}}
```
This is because the call to `List.length` consumes the head of the list `x :: xs`, converting it to a `Nat.succ`, in both the length of the input list and the length of the first output list.

Writing `A ∧ B` in Lean is short for `And A B`.
`And` is a structure type in the `Prop` universe:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean And}}
```
In other words, a proof of `A ∧ B` consists of the `And.intro` constructor applied to a proof of `A` in the `left` field and a proof of `B` in the `right` field.

The `cases` tactic allows a proof to consider each constructor of a datatype or each potential proof of a proposition in turn.
It corresponds to a `match` expression without recursion.
Using `cases` on a structure results in the structure being broken apart, with an assumption added for each field of the structure, just as a pattern match expression extracts the field of a structure for use in a program.
Because structures have only one constructor, using `cases` on a structure does not result in additional goals.

Because `ih` is a proof of `List.length (splitList xs).fst ≤ List.length xs ∧ List.length (splitList xs).snd ≤ List.length xs`, using `cases ih` results in an assumption that `List.length (splitList xs).fst ≤ List.length xs` and an assumption that `List.length (splitList xs).snd ≤ List.length xs`:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le3}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le3}}
```

Because the goal of the proof is also an `And`, the `constructor` tactic can be used to apply `And.intro`, resulting in a goal for each argument:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le4}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le4}}
```

The `left` goal is identical to the `left✝` assumption, so the `assumption` tactic dispatches it:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le5}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le5}}
```


The `right` goal resembles the `right✝` assumption, except the goal adds a `+ 1` only to the length of the input list.
It's time to prove that the inequality holds.

### Adding One to the Greater Side

The inequality needed to prove `splitList_shorter_le` is `∀(n m : Nat), n ≤ m → n ≤ Nat.succ m`.
The incoming assumption that `n ≤ m` essentially tracks the difference between `n` and `m` in the number of `Nat.le.step` constructors.
Thus, the proof should add an extra `Nat.le.step` in the base case.

Starting out, the statement reads:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean le_succ_of_le0}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean le_succ_of_le0}}
```

The first step is to introduce a name for the assumption that `n ≤ m`:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean le_succ_of_le1}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean le_succ_of_le1}}
```

The proof is by induction on this assumption:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean le_succ_of_le2a}}
```
In the case for `refl`, where `n = m`, the goal is to prove that `n ≤ n + 1`:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean le_succ_of_le2a}}
```
In the case for `step`, the goal is to prove that `n ≤ m + 1` under the assumption that `n ≤ m`:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean le_succ_of_le2b}}
```

For the `refl` case, the `step` constructor can be applied:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean le_succ_of_le3}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean le_succ_of_le3}}
```
After `step`, `refl` can be used, which leaves only the goal for `step`:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean le_succ_of_le4}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean le_succ_of_le4}}
```

For the step, applying the `step` constructor transforms the goal into the induction hypothesis:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean le_succ_of_le5}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean le_succ_of_le5}}
```

The final proof is as follows:
```leantac
{{#example_decl Examples/ProgramsProofs/Inequalities.lean le_succ_of_le}}
```

To reveal what's going on behind the scenes, the `apply` and `exact` tactics can be used to indicate exactly which constructor is being applied.
The `apply` tactic solves the current goal by applying a function or constructor whose return type matches, creating new goals for each argument that was not provided, while `exact` fails if any new goals would be needed:
```leantac
{{#example_decl Examples/ProgramsProofs/Inequalities.lean le_succ_of_le_apply}}
```

The proof can be golfed:
```leantac
{{#example_decl Examples/ProgramsProofs/Inequalities.lean le_succ_of_le_golf}}
```
In this short tactic script, both goals introduced by `induction` are addressed using `repeat (first | constructor | assumption)`.
The tactic `first | T1 | T2 | ... | Tn` means to use try `T1` through `Tn` in order, using the first tactic that succeeds.
In other words, `repeat (first | constructor | assumption)` applies constructors as long as it can, and then attempts to solve the goal using an assumption.

The proof can be shortened even further by using `omega`, a built-in solver for linear arithmetic:
```leantac
{{#example_decl Examples/ProgramsProofs/Inequalities.lean le_succ_of_le_omega}}
```

Finally, the proof can be written as a recursive function:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean le_succ_of_le_recursive}}
```

Each style of proof can be appropriate to different circumstances.
The detailed proof script is useful in cases where beginners may be reading the code, or where the steps of the proof provide some kind of insight.
The short, highly-automated proof script is typically easier to maintain, because automation is frequently both flexible and robust in the face of small changes to definitions and datatypes.
The recursive function is typically both harder to understand from the perspective of mathematical proofs and harder to maintain, but it can be a useful bridge for programmers who are beginning to work with interactive theorem proving.

### Finishing the Proof

Now that both helper theorems have been proved, the rest of `splitList_shorter_le` will be completed quickly.
The current proof state has one goal remaining:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le5}}
```

Using `Nat.le_succ_of_le` together with the `right✝` assumption completes the proof:
```leantac
{{#example_decl Examples/ProgramsProofs/Inequalities.lean splitList_shorter_le}}
```

The next step is to return to the actual theorem that is needed to prove that merge sort terminates: that so long as a list has at least two entries, both results of splitting it are strictly shorter.
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean splitList_shorter_start}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_start}}
```
Pattern matching works just as well in tactic scripts as it does in programs.
Because `lst` has at least two entries, they can be exposed with `match`, which also refines the type through dependent pattern matching:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean splitList_shorter_1}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_1}}
```
Simplifying using `splitList` removes `x` and `y`, resulting in the computed lengths of lists each gaining a `+ 1`:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean splitList_shorter_2}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_2}}
```
Replacing `simp` with `simp +arith` removes these `+ 1`s, because `simp +arith` makes use of the fact that `n + 1 < m + 1` implies `n < m`:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean splitList_shorter_2b}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean splitList_shorter_2b}}
```
This goal now matches `splitList_shorter_le`, which can be used to conclude the proof:
```leantac
{{#example_decl Examples/ProgramsProofs/Inequalities.lean splitList_shorter}}
```

The facts needed to prove that `mergeSort` terminates can be pulled out of the resulting `And`:
```leantac
{{#example_decl Examples/ProgramsProofs/Inequalities.lean splitList_shorter_sides}}
```

## Merge Sort Terminates

Merge sort has two recursive calls, one for each sub-list returned by `splitList`.
Each recursive call will require a proof that the length of the list being passed to it is shorter than the length of the input list.
It's usually convenient to write a termination proof in two steps: first, write down the propositions that will allow Lean to verify termination, and then prove them.
Otherwise, it's possible to put a lot of effort into proving the propositions, only to find out that they aren't quite what's needed to establish that the recursive calls are on smaller inputs.

The `sorry` tactic can prove any goal, even false ones.
It isn't intended for use in production code or final proofs, but it is a convenient way to "sketch out" a proof or program ahead of time.
Any definitions or theorems that use `sorry` are annotated with a warning.

The initial sketch of `mergeSort`'s termination argument that uses `sorry` can be written by copying the goals that Lean couldn't prove into `have`-expressions.
In Lean, `have` is similar to `let`.
When using `have`, the name is optional.
Typically, `let` is used to define names that refer to interesting values, while `have` is used to locally prove propositions that can be found when Lean is searching for evidence that an array lookup is in-bounds or that a function terminates.
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortSorry}}
```
The warning is located on the name `mergeSort`:
```output warning
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortSorry}}
```
Because there are no errors, the proposed propositions are enough to establish termination.

The proofs begin by applying the helper theorems:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortNeedsGte}}
```
Both proofs fail, because `splitList_shorter_fst` and `splitList_shorter_snd` both require a proof that `xs.length ≥ 2`:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortNeedsGte}}
```
To check that this will be enough to complete the proof, add it using `sorry` and check for errors:
```leantac
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortGteStarted}}
```
Once again, there is only a warning.
```output warning
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortGteStarted}}
```

There is one promising assumption available: `h : ¬List.length xs < 2`, which comes from the `if`.
Clearly, if it is not the case that `xs.length < 2`, then `xs.length ≥ 2`.
The `omega` tactic solves this goal, and the program is now complete:
```leantac
{{#example_decl Examples/ProgramsProofs/Inequalities.lean mergeSort}}
```

The function can be tested on examples:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortRocks}}
```
```output info
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortRocks}}
```
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortNumbers}}
```
```output info
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortNumbers}}
```

## Division as Iterated Subtraction

Just as multiplication is iterated addition and exponentiation is iterated multiplication, division can be understood as iterated subtraction.
The [very first description of recursive functions in this book](../getting-to-know/datatypes-and-patterns.md#recursive-functions) presents a version of division that terminates when the divisor is not zero, but that Lean does not accept.
Proving that division terminates requires the use of a fact about inequalities.

Lean cannot prove that this definition of division terminates:
```lean
{{#example_in Examples/ProgramsProofs/Div.lean divTermination}}
```

```output error
{{#example_out Examples/ProgramsProofs/Div.lean divTermination}}
```

That's a good thing, because it doesn't!
When `k` is `0`, value of `n` does not decrease, so the program is an infinite loop.

Rewriting the function to take evidence that `k` is not `0` allows Lean to automaically prove termination:
```lean
{{#example_decl Examples/ProgramsProofs/Div.lean divRecursiveNeedsProof}}
```

This definition of `div` terminates because the first argument `n` is smaller on each recursive call.
This can be expressed using a `termination_by` clause:

```lean
{{#example_decl Examples/ProgramsProofs/Div.lean divRecursiveWithProof}}
```


## Exercises

Prove the following theorems:

 * For all natural numbers \\( n \\), \\( 0 < n + 1 \\).
 * For all natural numbers \\( n \\), \\( 0 \\leq n \\).
 * For all natural numbers \\( n \\) and \\( k \\), \\( (n + 1) - (k + 1) = n - k \\)
 * For all natural numbers \\( n \\) and \\( k \\), if \\( k < n \\) then \\( n \neq 0 \\)
 * For all natural numbers \\( n \\), \\( n - n = 0 \\)
 * For all natural numbers \\( n \\) and \\( k \\), if \\( n + 1 < k \\) then \\( n < k \\)
