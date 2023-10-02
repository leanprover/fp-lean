# Interlude: Tactics, Induction, and Proofs

## A Note on Proofs and User Interfaces

This book presents the process of writing proofs as if they are written in one go and submitted to Lean, which then replies with error messages that describe what remains to be done.
The actual process of interacting with Lean is much more pleasant.
Lean provides information about the proof as the cursor is moved through it and there are a number of interactive features that make proving easier.
Please consult the documentation of your Lean development environment for more information.

The approach in this book that focuses on incrementally building a proof and showing the messages that result demonstrates the kinds of interactive feedback that Lean provides while writing a proof, even though it is much slower than the process used by experts.
At the same time, seeing incomplete proofs evolve towards completeness is a useful perspective on proving.
As your skill in writing proofs increases, Lean's feedback will come to feel less like errors and more like support for your own thought processes.
Learning the interactive approach is very important.

## Recursion and Induction

The functions `plusR_succ_left` and `plusR_zero_left` from the preceding chapter can be seen from two perspectives.
On the one hand, they are recursive functions that build up evidence for a proposition, just as other recursive functions might construct a list, a string, or any other data structure.
On the other, they also correspond to proofs by _mathematical induction_.

Mathematical induction is a proof technique where a statement is proven for _all_ natural numbers in two steps:
 1. The statement is shown to hold for \\( 0 \\). This is called the _base case_.
 2. Under the assumption that the statement holds for some arbitrarily chosen number \\( n \\), it is shown to hold for \\( n + 1 \\). This is called the _induction step_. The assumption that the statement holds for \\( n \\) is called the _induction hypothesis_.

Because it's impossible to check the statement for _every_ natural number, induction provides a means of writing a proof that could, in principle, be expanded to any particular natural number.
For example, if a concrete proof were desired for the number 3, then it could be constructed by using first the base case and then the induction step three times, to show the statement for 0, 1, 2, and finally 3.
Thus, it proves the statement for all natural numbers.

## The Induction Tactic

Writing proofs by induction as recursive functions that use helpers such as `congrArg` does not always do a good job of expressing the intentions behind the proof.
While recursive functions indeed have the structure of induction, they should probably be viewed as an _encoding_ of a proof.
Furthermore, Lean's tactic system provides a number of opportunities to automate the construction of a proof that are not available when writing the recursive function explicitly.
Lean provides an induction _tactic_ that can carry out an entire proof by induction in a single tactic block.
Behind the scenes, Lean constructs the recursive function that corresponds the use of induction.

To prove `plusR_zero_left` with the induction tactic, begin by writing its signature (using `theorem`, because this really is a proof).
Then, use `by induction k` as the body of the definition:
```leantac
{{#example_in Examples/Induction.lean plusR_ind_zero_left_1}}
```
The resulting message states that there are two goals:
```output error
{{#example_out Examples/Induction.lean plusR_ind_zero_left_1}}
```
A tactic block is a program that is run while the Lean type checker processes a file, somewhat like a much more powerful C preprocessor macro.
The tactics generate the actual program.

In the tactic language, there can be a number of goals.
Each goal consists of a type together with some assumptions.
These are analogous to using underscores as placeholders—the type in the goal represents what is to be proved, and the assumptions represent what is in-scope and can be used.
In the case of the goal `case zero`, there are no assumptions and the type is `Nat.zero = Nat.plusR 0 Nat.zero`—this is the theorem statement with `0` instead of `k`.
In the goal `case succ`, there are two assumptions, named `n✝` and `n_ih✝`.
Behind the scenes, the `induction` tactic creates a dependent pattern match that refines the overall type, and `n✝` represents the argument to `Nat.succ` in the pattern.
The assumption `n_ih✝` represents the result of calling the generated function recursively on `n✝`.
Its type is the overall type of the theorem, just with `n✝` instead of `k`.
The type to be fulfilled as part of the goal `case succ` is the overall theorem statement, with `Nat.succ n✝` instead of `k`.

The two goals that result from the use of the `induction` tactic correspond to the base case and the induction step in the description of mathematical induction.
The base case is `case zero`.
In `case succ`, `n_ih✝` corresponds to the induction hypothesis, while the whole of `case succ` is the induction step.

The next step in writing the proof is to focus on each of the two goals in turn.
Just as `pure ()` can be used in a `do` block to indicate "do nothing", the tactic language has a statement `skip` that also does nothing.
This can be used when Lean's syntax requires a tactic, but it's not yet clear which one should be used.
Adding `with` to the end of the `induction` statement provides a syntax that is similar to pattern matching:
```leantac
{{#example_in Examples/Induction.lean plusR_ind_zero_left_2a}}
```
Each of the two `skip` statements has a message associated with it.
The first shows the base case:
```output error
{{#example_out Examples/Induction.lean plusR_ind_zero_left_2a}}
```
The second shows the induction step:
```output error
{{#example_out Examples/Induction.lean plusR_ind_zero_left_2b}}
```
In the induction step, the inaccessible names with daggers have been replaced with the names provided after `succ`, namely `n` and `ih`.

The cases after `induction ... with` are not patterns: they consist of the name of a goal followed by zero or more names.
The names are used for assumptions introduced in the goal; it is an error to provide more names than the goal introduces:
```leantac
{{#example_in Examples/Induction.lean plusR_ind_zero_left_3}}
```
```output error
{{#example_out Examples/Induction.lean plusR_ind_zero_left_3}}
```

Focusing on the base case, the `rfl` tactic works just as well inside of the `induction` tactic as it does in a recursive function:
```leantac
{{#example_in Examples/Induction.lean plusR_ind_zero_left_4}}
```
In the recursive function version of the proof, a type annotation made the expected type something that was easier to understand.
In the tactic language, there are a number of specific ways to transform a goal to make it easier to solve.
The `unfold` tactic replaces a defined name with its definition:
```leantac
{{#example_in Examples/Induction.lean plusR_ind_zero_left_5}}
```
Now, the right-hand side of the equality in the goal has become `Nat.plusR 0 n + 1` instead of `Nat.plusR 0 (Nat.succ n)`:
```output error
{{#example_out Examples/Induction.lean plusR_ind_zero_left_5}}
```

Instead of appealing to functions like `congrArg` and operators like `▸`, there are tactics that allow equality proofs to be used to transform proof goals.
One of the most important is `rw`, which takes a list of equality proofs and replaces the left side with the right side in the goal.
This almost does the right thing in `plusR_zero_left`:
```leantac
{{#example_in Examples/Induction.lean plusR_ind_zero_left_6}}
```
However, the direction of the rewrite was incorrect.
Replacing `n` with `Nat.plusR 0 n` made the goal more complicated rather than less complicated:
```output error
{{#example_out Examples/Induction.lean plusR_ind_zero_left_6}}
```
This can be remedied by placing a left arrow before `ih` in the call to `rewrite`, which instructs it to replace the right-hand side of the equality with the left-hand side:
```leantac
{{#example_decl Examples/Induction.lean plusR_zero_left_done}}
```
This rewrite makes both sides of the equation identical, and Lean takes care of the `rfl` on its own.
The proof is complete.

## Tactic Golf

So far, the tactic language has not shown its true value.
The above proof is no shorter than the recursive function; it's merely written in a domain-specific language instead of the full Lean language.
But proofs with tactics can be shorter, easier, and more maintainable.
Just as a lower score is better in the game of golf, a shorter proof is better in the game of tactic golf.

The induction step of `plusR_zero_left` can be proved using the simplification tactic `simp`.
Using `simp` on its own does not help:
```leantac
{{#example_in Examples/Induction.lean plusR_zero_left_golf_1}}
```
```output error
{{#example_out Examples/Induction.lean plusR_zero_left_golf_1}}
```
However, `simp` can be configured to make use of a set of definitions.
Just like `rw`, these arguments are provided in a list.
Asking `simp` to take the definition of `Nat.plusR` into account leads to a simpler goal:
```leantac
{{#example_in Examples/Induction.lean plusR_zero_left_golf_2}}
```
```output error
{{#example_out Examples/Induction.lean plusR_zero_left_golf_2}}
```
In particular, the goal is now identical to the induction hypothesis.
In addition to automatically proving simple equality statements, the simplifier automatically replaces goals like `Nat.succ A = Nat.succ B` with `A = B`.
Because the induction hypothesis `ih` has exactly the right type, the `exact` tactic can indicate that it should be used:
```leantac
{{#example_decl Examples/Induction.lean plusR_zero_left_golf_3}}
```

However, the use of `exact` is somewhat fragile.
Renaming the induction hypothesis, which may happen while "golfing" the proof, would cause this proof to stop working.
The `assumption` tactic solves the current goal if _any_ of the assumptions match it:
```leantac
{{#example_decl Examples/Induction.lean plusR_zero_left_golf_4}}
```

This proof is no shorter than the prior proof that used unfolding and explicit rewriting.
However, a series of transformations can make it much shorter, taking advantage of the fact that `simp` can solve many kinds of goals.
The first step is to drop the `with` at the end of `induction`.
For structured, readable proofs, the `with` syntax is convenient.
It complains if any cases are missing, and it shows the structure of the induction clearly.
But shortening proofs can often require a more liberal approach.

Using `induction` without `with` simply results in a proof state with two goals.
The `case` tactic can be used to select one of them, just as in the branches of the `induction ... with` tactic.
In other words, the following proof is equivalent to the prior proof:
```leantac
{{#example_decl Examples/Induction.lean plusR_zero_left_golf_5}}
```

In a context with a single goal (namely, `k = Nat.plusR 0 k`), the `induction k` tactic yields two goals.
In general, a tactic will either fail with an error or take a goal and transform it into zero or more new goals.
Each new goal represents what remains to be proved.
If the result is zero goals, then the tactic was a success, and that part of the proof is done.

The `<;>` operator takes two tactics as arguments, resulting in a new tactic.
`T1 <;> T2` applies `T1` to the current goal, and then applies `T2` in _all_ goals created by `T1`.
In other words, `<;>` enables a general tactic that can solve many kinds of goals to be used on multiple new goals all at once.
One such general tactic is `simp`.

Because `simp` can both complete the proof of the base case and make progress on the proof of the induction step, using it with `induction` and `<;>` shortens the proof:
```leantac
{{#example_in Examples/Induction.lean plusR_zero_left_golf_6a}}
```
This results in only a single goal, the transformed induction step:
```output error
{{#example_out Examples/Induction.lean plusR_zero_left_golf_6a}}
```
Running `assumption` in this goal completes the proof:
```leantac
{{#example_decl Examples/Induction.lean plusR_zero_left_golf_6}}
```
Here, `exact` would not have been possible, because `ih` was never explicitly named.

For beginners, this proof is not easier to read.
However, a common pattern for expert users is to take care of a number of simple cases with powerful tactics like `simp`, allowing them to focus the text of the proof on the interesting cases.
Additionally, these proofs tend to be more robust in the face of small changes to the functions and datatypes involved in the proof.
The game of tactic golf is a useful part of developing good taste and style when writing proofs.

## Induction on Other Datatypes

Mathematical induction proves a statement for natural numbers by providing a base case for `Nat.zero` and an induction step for `Nat.succ`.
The principle of induction is also valid for other datatypes.
Constructors without recursive arguments form the base cases, while constructors with recursive arguments form the induction steps.
The ability to carry out proofs by induction is the very reason why they are called _inductive_ datatypes.

One example of this is induction on binary trees.
Induction on binary trees is a proof technique where a statement is proven for _all_ binary trees in two steps:
 1. The statement is shown to hold for `BinTree.leaf`. This is called the base case.
 2. Under the assumption that the statement holds for some arbitrarily chosen trees `l` and `r`, it is shown to hold for `BinTree.branch l x r`, where `x` is an arbitrarily-chosen new data point. This is called the _induction step_. The assumptions that the statement holds for `l` and `r` are called the _induction hypotheses_.

`BinTree.count` counts the number of branches in a tree:
```lean
{{#example_decl Examples/Induction.lean BinTree_count}}
```
[Mirroring a tree](monads/conveniences.md#leading-dot-notation) does not change the number of branches in it.
This can be proven using induction on trees.
The first step is to state the theorem and invoke `induction`:
```leantac
{{#example_in Examples/Induction.lean mirror_count_0a}}
```
The base case states that counting the mirror of a leaf is the same as counting the leaf:
```output error
{{#example_out Examples/Induction.lean mirror_count_0a}}
```
The induction step allows the assumption that mirroring the left and right subtrees won't affect their branch counts, and requests a proof that mirroring a branch with these subtrees also preserves the overall branch count:
```output error
{{#example_out Examples/Induction.lean mirror_count_0b}}
```


The base case is true because mirroring `leaf` results in `leaf`, so the left and right sides are definitionally equal.
This can be expressed by using `simp` with instructions to unfold `BinTree.mirror`:
```leantac
{{#example_in Examples/Induction.lean mirror_count_1}}
```
In the induction step, nothing in the goal immediately matches the induction hypotheses.
Simplifying using the definitions of `BinTree.count` and `BinTree.mirror` reveals the relationship:
```leantac
{{#example_in Examples/Induction.lean mirror_count_2}}
```
```output error
{{#example_out Examples/Induction.lean mirror_count_2}}
```
Both induction hypotheses can be used to rewrite the left-hand side of the goal into something almost like the right-hand side:
```leantac
{{#example_in Examples/Induction.lean mirror_count_3}}
```
```output error
{{#example_out Examples/Induction.lean mirror_count_3}}
```

The `simp_arith` tactic, a version of `simp` that can use additional arithmetic identities, is enough to prove this goal, yielding:
```leantac
{{#example_decl Examples/Induction.lean mirror_count_4}}
```

In addition to definitions to be unfolded, the simplifier can also be passed names of equality proofs to use as rewrites while it simplifies proof goals.
`BinTree.mirror_count` can also be written:
```leantac
{{#example_decl Examples/Induction.lean mirror_count_5}}
```
As proofs grow more complicated, listing assumptions by hand can become tedious.
Furthermore, manually writing assumption names can make it more difficult to re-use proof steps for multiple subgoals.
The argument `*` to `simp` or `simp_arith` instructs them to use _all_ assumptions while simplifying or solving the goal.
In other words, the proof could also be written:
```leantac
{{#example_decl Examples/Induction.lean mirror_count_6}}
```
Because both branches are using the simplifier, the proof can be reduced to:
```leantac
{{#example_decl Examples/Induction.lean mirror_count_7}}
```


## Exercises

 * Prove `plusR_succ_left` using the `induction ... with` tactic.
 * Rewrite the proof of `plus_succ_left` to use `<;>` in a single line.
 * Prove that appending lists is associative using induction on lists: `theorem List.append_assoc (xs ys zs : List α) : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs`
