# More Inequalities

Lean's built-in proof automation is sufficient to check that `arrayMapHelper` and `findHelper` terminate.
All that was needed was to provide an expression whose value decreases with each recursive call.
However, Lean's built-in automation is not magic, and it often needs some help.

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

It will also be necessary to prove that `(split xs).snd.length < xs.length`.
Because `split` alternates between adding entries to the two lists, it is easiest to prove both statements at once, so the structure of the proof can follow the algorithm used to implement `split`.
In other words, it is easiest to prove that `∀(lst : List), (split lst).fst.length < lst.length ∧ (split lst).snd.length < lst.length`.

Unfortunately, the statement is false.
In particular, `{{#example_in Examples/ProgramsProofs/Inequalities.lean splitEmpty}}` is `{{#example_out Examples/ProgramsProofs/Inequalities.lean splitEmpty}}`. Both output lists have length `0`, which is not less than `0`, the length of the input list.
Similarly, `{{#example_in Examples/ProgramsProofs/Inequalities.lean splitOne}}` evaluates to `{{#example_out Examples/ProgramsProofs/Inequalities.lean splitOne}}`, and `["basalt"]` is not shorter than `{{#example_in Examples/ProgramsProofs/Inequalities.lean splitOne}}`.
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

Adding 
