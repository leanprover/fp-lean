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
 2. If both lists are non-empty, then their heads should be compared. The result of the function is smaller of the two heads, followed by the result of merging the remaining entries of both lists.

This is not structurally recursive on either list.
The recursion terminates because an entry is removed from one of the two lists in each recursive call, but it could be either list.
The `termination_by` clause uses the sum of the length of both lists as a decreasing value:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean merge}}
```

In addition to using the lengths of the lists, a pair that contains both lists can also be provided:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean mergePairTerm}}
```
This works because Lean has a built-in notion of sizes of data, expressed through a type class called `WellFoundedRelation`.
The instance for pairs automatically considers them to be smaller if either the first or the second item in the pair shrinks.

A simple way to split a list is to add each entry in the input list to two alternating output lists:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean split}}
```

Merge sort checks whether a base case has been reached.
If so, it returns the input list.
If not, it splits the input, and merges the result of sorting each half:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortNoTerm}}
```
Lean's pattern match compiler is able to tell that the assumption `h` introduced by the `if` that tests whether `xs.length < 2` rules out lists longer than one entry, so there is no "missing cases" error.
However, even though this program always terminates, it is not structurally recursive:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortNoTerm}}
```
The reason it terminates is that `split` always returns lists that are shorter than its input.
Thus, the length of `halves.fst` and `halves.snd` are less than the length of `xs`.
This can be expressed using a `termination_by` clause:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortGottaProveIt}}
```
With this clause, the error message changes.
Instead of complaining that the function isn't structurally recursive, Lean instead points out that it was unable to automatically prove that `(split xs).fst.length < xs.length`:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortGottaProveIt}}
```

## Splitting a List Makes it Shorter

It will also be necessary to prove that `(split xs).snd.length < xs.length`.
Because `split` alternates between adding entries to the two lists, it is easiest to prove both statements at once, so the structure of the proof can follow the algorithm used to implement `split`.
In other words, it is easiest to prove that `∀(lst : List), (split lst).fst.length < lst.length ∧ (split lst).snd.length < lst.length`.

Unfortunately, the statement is false.
In particular, `{{#example_in Examples/ProgramsProofs/Inequalities.lean splitEmpty}}` is `{{#example_out Examples/ProgramsProofs/Inequalities.lean splitEmpty}}`. Both output lists have length `0`, which is not less than `0`, the length of the input list.
Similarly, `{{#example_in Examples/ProgramsProofs/Inequalities.lean splitOne}}` evaluates to `{{#example_out Examples/ProgramsProofs/Inequalities.lean splitOne}}`, and `["basalt"]` is not shorter than `["basalt"]`.
However, `{{#example_in Examples/ProgramsProofs/Inequalities.lean splitTwo}}` evaluates to `{{#example_out Examples/ProgramsProofs/Inequalities.lean splitTwo}}`, and both of these output lists are shorter than the input list.

It turns out that the lengths of the output lists are always less than or equal to the length of the input list, but they are only strictly shorter when the input list contains at least two entries.
It turns out to be easiest to prove the former statement, then extend it to the latter statement.
Begin with a theorem statement:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean split_shorter_le0}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_le0}}
```
Because `split` is structurally recursive on the list, the proof should use induction.
The structural recursion in `split` fits a proof by induction perfectly: the base case of the induction matches the base case of the recursion, and the inductive step matches the recursive call.
The `induction` tactic gives two goals:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean split_shorter_le1a}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_le1a}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_le1b}}
```

The goal for the `nil` case can be proved by invoking the simplifier and instructing it to unfold the definition of `split`, because the length of the empty list is less than or equal to the length of the empty list.
Similarly, simplifying with `split` in the `cons` case places `Nat.succ` around the lengths in the goal:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean split_shorter_le2}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_le2}}
```
This is because the call to `List.length` consumes the head of the list `x :: xs`, converting it to a `Nat.succ`, in both the length of the input list and the length of the first output list.

Writing `A ∧ B` in Lean is short for `And A B`.
`And` is a structure type in the `Prop` universe:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean And}}
```
In other words, a proof of `A ∧ B` consists of the `And.intro` constructor applied to a proof of `A` in the `left` field and a proof of `B` in the `right` field`.

The `cases` tactic allows a proof to consider each constructor of a datatype or each potential proof of a proposition in turn.
It corresponds to a `match` expression without recursion.
Using `cases` on a structure results in the structure being broken apart, with an assumption added for each field of the structure, just as a pattern match expression extracts the field of a structure for use in a program.
Because structures have only one constructor, using `cases` on a structure does not result in additional goals.

Because `ih` is a proof of `List.length (split xs).fst ≤ List.length xs ∧ List.length (split xs).snd ≤ List.length xs`, using `cases ih` results in an assumption that `List.length (split xs).fst ≤ List.length xs` and an assumption that `List.length (split xs).snd ≤ List.length xs`:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean split_shorter_le3}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_le3}}
```

Because the goal of the proof is also an `And`, the `constructor` tactic can be used to apply `And.intro`, resulting in a goal for each argument:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean split_shorter_le4}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_le4}}
```

The `left` goal is very similar to the `left✝` assumption, except the goal wraps both sides of the inequality in `Nat.succ`.
Likewise, the `right` goal resembles the `right✝` assumption, except the goal adds a `Nat.succ` only to the length of the input list.
It's time to prove that these wrappings of `Nat.succ` preserve the truth of the statement.

### Adding One to Both Sides

For the `left` goal, the statement to prove is `Nat.succ_le_succ : n ≤ m → Nat.succ n ≤ Nat.succ m`.
In other words, if `n ≤ m`, then adding one to both sides doesn't change this fact.
Why is this true?
The proof that `n ≤ m` is a `Nat.le.refl` constructor with `m - n` instances of the `Nat.le.step` constructor wrapped around it.
Adding one to both sides simply means that the `refl` applies to a number that's one larger than before, with the same number of `step` constructors.

More formally, the proof is by induction on the evidence that `n ≤ m`.
If the evidence is `refl`, then `n = m`, so `Nat.succ n = Nat.succ m` and `refl` can be used again.
If the evidence is `step`, then the induction hypothesis provides evidence that `Nat.succ n ≤ Nat.succ m`, and the goal is to show that `Nat.succ n ≤ Nat.succ (Nat.succ m)`.
This can be done by using `step` together with the induction hypothesis.

In Lean, the theorem statement is:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean succ_le_succ0}}
```
and the error message recapitulates it:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean succ_le_succ0}}
```

The first step is to use the `intro` tactic, bringing the hypothesis that `n ≤ m` into scope and giving it a name:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean succ_le_succ1}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean succ_le_succ1}}
```

Because the proof is by induction on the evidence that `n ≤ m`, the next tactic is `induction h`:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean succ_le_succ3}}
```
This results in two goals, once for each constructor of `Nat.le`:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean succ_le_succ3}}
```
The goal for `refl` can itself be solved using `refl`, which the `constructor` tactic selects.
The goal for `step` will also require a use of the `step` constructor:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean succ_le_succ4}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean succ_le_succ4}}
```
The goal is no longer shown using the `≤` operator, but it is equivalent to the induction hypothesis `ih`.
The `assumption` tactic automatically selects an assumption that fulfills the goal, and the proof is complete:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean succ_le_succ5}}
```

Written as a recursive function, the proof is:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean succ_le_succ_recursive}}
```
It can be instructional to compare the tactic-based proof by induction with this recursive function.
Which proof steps correspond to which parts of the definition?

### Adding One to the Greater Side

The second inequality needed to prove `split_shorter_le` is `∀(n m : Nat), n ≤ m → n ≤ Nat.succ m`.
This proof is almost identical to `Nat.succ_le_succ`.
Once again, the incoming assumption that `n ≤ m` essentially tracks the difference between `n` and `m` in the number of `Nat.le.step` constructors.
Thus, the proof should add an extra `Nat.le.step` in the base case.
The proof can be written:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean le_succ_of_le}}
```

To reveal what's going on behind the scenes, the `apply` and `exact` tactics can be used to indicate exactly which constructor is being applied.
The `apply` tactic solves the current goal by applying a function or constructor whose return type matches, creating new goals for each argument that was not provided, while `exact` fails if any new goals would be needed:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean le_succ_of_le_apply}}
```

The proof can be golfed:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean le_succ_of_le_golf}}
```
In this short tactic script, both goals introduced by `induction` are addressed using `repeat (first | constructor | assumption)`.
The tactic `first | T1 | T2 | ... | Tn` means to use try `T1` through `Tn` in order, using the first tactic that succeeds.
In other words, `repeat (first | constructor | assumption)` applies constructors as long as it can, and then attempts to solve the goal using an assumption.

Finally, the proof can be written as a recursive function:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean le_succ_of_le_recursive}}
```

Each style of proof can be appropriate to different circumstances.
The detailed proof script is useful in cases where beginners may be reading the code, or where the steps of the proof provide some kind of insight.
The short, highly-automated proof script is typically easier to maintain, because automation is frequently both flexible and robust in the face of small changes to definitions and datatypes.
The recursive function is typically both harder to understand from the perspective of mathematical proofs and harder to maintain, but it can be a useful bridge for programmers who are beginning to work with interactive theorem proving.

### Finishing the Proof

Now that both helper theorems have been proved, the rest of `split_shorter_le` will be completed quickly.
The current proof state has two goals, for the left and right sides of the `And`:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_le4}}
```

The goals are named for the fields of the `And` structure. This means that the `case` tactic (not to be confused with `cases`) can be used to focus on each of them in turn:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean split_shorter_le5a}}
```
Instead of a single error that lists both unsolved goals, there are now two messages, one on each `skip`.
For the `left` goal, `Nat.succ_le_succ` can be used:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_le5a}}
```
In the right goal, `Nat.le_suc_of_le` fits:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_le5b}}
```
Both theorems include the precondition that `n ≤ m`.
These can be found as the `left✝` and `right✝` assumptions, which means that the `assumption` tactic takes care of the final goals:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean split_shorter_le}}
```

The next step is to return to the actual theorem that is needed to prove that merge sort terminates: that so long as a list has at least two entries, both results of splitting it are strictly shorter.
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean split_shorter_start}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_start}}
```
Pattern matching works just as well in tactic scripts as it does in programs.
Because `lst` has at least two entries, they can be exposed using with `match`, which also refines the type through dependent pattern matching:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean split_shorter_1}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_1}}
```
Simplifying using `split` removes `x` and `y`, resulting in the computed lengths of lists each gaining a `Nat.succ`:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean split_shorter_2}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_2}}
```
Replacing `simp` with `simp_arith` removes these `Nat.succ` constructors, because `simp_arith` makes use of the fact that `n + 1 < m + 1` implies `n < m`:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean split_shorter_2b}}
```
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean split_shorter_2b}}
```
This goal now matches `split_shorter_le`, which can be used to conclude the proof:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean split_shorter}}
```

The facts needed to prove that `mergeSort` terminates can be pulled out of the resulting `And`:
```lean
{{#example_decl Examples/ProgramsProofs/Inequalities.lean split_shorter_sides}}
```

## Merge Sort Terminates

Merge sort has two recursive calls, one for each sub-list returned by `split`.
Each recursive call will require a proof that the length of the list being passed to it is shorter than the length of the input list.
It's usually convenient to write a termination proof in two steps: first, write down the propositions that will allow Lean to verify termination, and then prove them.
Otherwise, it's possible to put a lot of effort into proving the propositions, only to find out that they aren't quite what's needed to establish that the recursive calls are on smaller inputs.

The `sorry` tactic can prove any goal, even false ones.
It isn't intended for use in production code or final proofs, but it is a convenient way to "sketch out" a proof or program ahead of time.
Any definitions or theorems that use `sorry` are annotated with a warning.

The initial sketch of `mergeSort`'s termination argument that uses `sorry` can be written by copying the goals that Lean couldn't prove into `have`-expressions:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortSorry}}
```
The warning is located on the name `mergeSort`:
```output warning
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortSorry}}
```
Because there are no errors, the proposed propositions are enough to establish termination.

The proofs begin by applying the helper theorems:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortNeedsGte}}
```
Both proofs fail, because `split_shorter_fst` and `split_shorter_snd` both require a proof that `xs.length ≥ 2`:
```output error
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortNeedsGte}}
```
To check that this will be enough to complete the proof, add it using `sorry` and check for errors:
```lean
{{#example_in Examples/ProgramsProofs/Inequalities.lean mergeSortGteStarted}}
```
Once again, there is only a warning.
```output warning
{{#example_out Examples/ProgramsProofs/Inequalities.lean mergeSortGteStarted}}
```

There is one promising assumption available: `h : ¬List.length xs < 2`, which comes from the `if`.
Clearly, if it is not the case that `xs.length < 2`, then `xs.length ≥ 2`.
The Lean library provides this theorem under the name `Nat.ge_of_not_lt`.
The program is now complete:
```lean
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

The first step is to refine the definition of division so that it requires evidence that the divisor is not zero:
```lean
{{#example_in Examples/ProgramsProofs/Div.lean divTermination}}
```
The error message is somewhat longer, due to the additional argument, but it contains essentially the same information:
```output error
{{#example_out Examples/ProgramsProofs/Div.lean divTermination}}
```

This definition of `div` terminates because the first argument `n` is smaller on each recursive call.
This can be expressed using a `termination_by` clause:
```lean
{{#example_in Examples/ProgramsProofs/Div.lean divRecursiveNeedsProof}}
```
Now, the error is confined to the recursive call:
```output error
{{#example_out Examples/ProgramsProofs/Div.lean divRecursiveNeedsProof}}
```

This can be proved using a theorem from the standard library, `Nat.sub_lt`.
This theorem states that `{{#example_out Examples/ProgramsProofs/Div.lean NatSubLt}}` (the curly braces indicate that `n` and `k` are implicit arguments).
Using this theorem requires demonstrating that both `n` and `k` are greater than zero.
Because `k > 0` is syntactic sugar for `0 < k`, the only necessary goal is to show that `0 < n`.
There are two possibilities: either `n` is `0`, or it is `n' + 1` for some other `Nat` `n'`.
But `n` cannot be `0`.
The fact that the `if` selected the second branch means that `¬ n < k`, but if `n = 0` and `k > 0` then must be less than `k`, which would be a contradiction.
This, `n = Nat.succ n'`, and `Nat.succ n'` is clearly greater than `0`.

The full definition of `div`, including the termination proof, is:
```lean
{{#example_decl Examples/ProgramsProofs/Div.lean div}}
```


## Exercises

Prove the following theorems:

 * For all natural numbers \\( n \\), \\( 0 < n + 1 \\).
 * For all natural numbers \\( n \\), \\( 0 \\leq n \\).
 * For all natural numbers \\( n \\) and \\( k \\), \\( (n + 1) - (k + 1) = n - k \\)
 * For all natural numbers \\( n \\) and \\( k \\), if \\( k < n \\) then \\( n \neq 0 \\)
 * For all natural numbers \\( n \\), \\( n - n = 0 \\)
 * For all natural numbers \\( n \\) and \\( k \\), if \\( n + 1 < k \\) then \\( n < k \\)
