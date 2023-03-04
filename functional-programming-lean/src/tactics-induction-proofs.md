# Interlude: Tactics, Induction, and Proofs

## The Induction Tactic

The functions `plusR_succ_left` and `plusR_zero_left` can be seen from two perspectives.
On the one hand, they are recursive functions that build up evidence for a proposition, just as other recursive functions might construct a list, a string, or any other data structure.
On the other, they also correspond to proofs by mathematical induction.

Mathematical induction is a proof technique where a statement is proven to apply to _all_ natural numbers in two steps:
 1. The statement is shown to hold for \\( 0 \\).
 2. Assuming that the statement holds for some arbitrarily chosen number \\( n \\), it is shown to hold for \\( n + 1 \\).

Because it's impossible to check the statement for _every_ natural number, induction provides a means of writing a proof that could, in principle, be expanded to any particular natural number.
Thus, it proves the statement for all natural numbers.

Writing proofs by induction as recursive functions that use helpers such as `congrArg` does not always do a good job of expressing the intentions behind the proof.
Furthermore, Lean's tactic system provides a number of opportunities to automate the construction of a proof that are not available when writing the recursive function.
Lean provides an induction _tactic_ that can carry out an entire proof by induction in a single tactic block.


To prove `plusR_zero_left` with the induction tactic, begin by writing its signature (using `theorem`, because this really is a proof):
```lean
{{#example_in Examples/DependentTypes/Pitfalls.lean plusR_ind_zero_left_1}}
```
The message states that there are two goals:
```output error
{{#example_out Examples/DependentTypes/Pitfalls.lean plusR_ind_zero_left_1}}
```
A tactic block is a program that is run while the Lean type checker processes a file, somewhat like a much more powerful C preprocessor macro.
The tactics generate the actual program.
In the tactic language, there can be a number of goals.
When each goal is achieved, the proof is complete.
Tactics 

