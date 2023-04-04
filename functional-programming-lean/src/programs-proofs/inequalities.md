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
Unfortunately, this is false.


