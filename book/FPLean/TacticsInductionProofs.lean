import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Induction"

#doc (Manual) "Interlude: Tactics, Induction, and Proofs" =>
%%%
tag := "tactics-induction-proofs"
number := false
htmlSplit := .never
%%%

# A Note on Proofs and User Interfaces
%%%
tag := "proofs-and-uis"
%%%

This book presents the process of writing proofs as if they are written in one go and submitted to Lean, which then replies with error messages that describe what remains to be done.
The actual process of interacting with Lean is much more pleasant.
Lean provides information about the proof as the cursor is moved through it and there are a number of interactive features that make proving easier.
Please consult the documentation of your Lean development environment for more information.

The approach in this book that focuses on incrementally building a proof and showing the messages that result demonstrates the kinds of interactive feedback that Lean provides while writing a proof, even though it is much slower than the process used by experts.
At the same time, seeing incomplete proofs evolve towards completeness is a useful perspective on proving.
As your skill in writing proofs increases, Lean's feedback will come to feel less like errors and more like support for your own thought processes.
Learning the interactive approach is very important.

# Recursion and Induction
%%%
tag := "recursion-vs-induction"
%%%

The functions {anchorName plusR_succ_left (module := Examples.DependentTypes.Pitfalls)}`plusR_succ_left` and {anchorName plusR_zero_left_thm (module:=Examples.DependentTypes.Pitfalls)}`plusR_zero_left` from the preceding chapter can be seen from two perspectives.
On the one hand, they are recursive functions that build up evidence for a proposition, just as other recursive functions might construct a list, a string, or any other data structure.
On the other, they also correspond to proofs by _mathematical induction_.

Mathematical induction is a proof technique where a statement is proven for _all_ natural numbers in two steps:
 1. The statement is shown to hold for $`0`. This is called the _base case_.
 2. Under the assumption that the statement holds for some arbitrarily chosen number $`n`, it is shown to hold for $`n + 1`. This is called the _induction step_. The assumption that the statement holds for $`n` is called the _induction hypothesis_.

Because it's impossible to check the statement for _every_ natural number, induction provides a means of writing a proof that could, in principle, be expanded to any particular natural number.
For example, if a concrete proof were desired for the number 3, then it could be constructed by using first the base case and then the induction step three times, to show the statement for 0, 1, 2, and finally 3.
Thus, it proves the statement for all natural numbers.

# The Induction Tactic
%%%
tag := "induction-tactic"
%%%

Writing proofs by induction as recursive functions that use helpers such as {anchorName plusR_zero_left_done (module:=Examples.DependentTypes.Pitfalls)}`congrArg` does not always do a good job of expressing the intentions behind the proof.
While recursive functions indeed have the structure of induction, they should probably be viewed as an _encoding_ of a proof.
Furthermore, Lean's tactic system provides a number of opportunities to automate the construction of a proof that are not available when writing the recursive function explicitly.
Lean provides an induction _tactic_ that can carry out an entire proof by induction in a single tactic block.
Behind the scenes, Lean constructs the recursive function that corresponds the use of induction.

To prove {anchorName plusR_zero_left_done (module:=Examples.DependentTypes.Pitfalls)}`plusR_zero_left` with the {kw}`induction` tactic, begin by writing its signature (using {kw}`theorem`, because this really is a proof).
Then, use {anchorTerm plusR_ind_zero_left_1}`by induction k` as the body of the definition:
```anchor plusR_ind_zero_left_1
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k
```
The resulting message states that there are two goals:
```anchorError plusR_ind_zero_left_1
unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0

case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ + 1 = Nat.plusR 0 (n✝ + 1)
```
A tactic block is a program that is run while the Lean type checker processes a file, somewhat like a much more powerful C preprocessor macro.
The tactics generate the actual program.

In the tactic language, there can be a number of goals.
Each goal consists of a type together with some assumptions.
These are analogous to using underscores as placeholders—the type in the goal represents what is to be proved, and the assumptions represent what is in-scope and can be used.
In the case of the goal {lit}`case zero`, there are no assumptions and the type is {anchorTerm others}`Nat.zero = Nat.plusR 0 Nat.zero`—this is the theorem statement with {anchorTerm others}`0` instead of {anchorName plusR_ind_zero_left_1}`k`.
In the goal {lit}`case succ`, there are two assumptions, named {lit}`n✝` and {lit}`n_ih✝`.
Behind the scenes, the {anchorTerm plusR_ind_zero_left_1}`induction` tactic creates a dependent pattern match that refines the overall type, and {lit}`n✝` represents the argument to {anchorName others}`Nat.succ` in the pattern.
The assumption {lit}`n_ih✝` represents the result of calling the generated function recursively on {lit}`n✝`.
Its type is the overall type of the theorem, just with {lit}`n✝` instead of {anchorName plusR_ind_zero_left_1}`k`.
The type to be fulfilled as part of the goal {lit}`case succ` is the overall theorem statement, with {lit}`Nat.succ n✝` instead of {anchorName plusR_ind_zero_left_1}`k`.

The two goals that result from the use of the {anchorTerm plusR_ind_zero_left_1}`induction` tactic correspond to the base case and the induction step in the description of mathematical induction.
The base case is {lit}`case zero`.
In {lit}`case succ`, {lit}`n_ih✝` corresponds to the induction hypothesis, while the whole of {lit}`case succ` is the induction step.

The next step in writing the proof is to focus on each of the two goals in turn.
Just as {anchorTerm others}`pure ()` can be used in a {kw}`do` block to indicate “do nothing”, the tactic language has a statement {kw}`skip` that also does nothing.
This can be used when Lean's syntax requires a tactic, but it's not yet clear which one should be used.
Adding {kw}`with` to the end of the {kw}`induction` statement provides a syntax that is similar to pattern matching:
```anchor plusR_ind_zero_left_2a
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => skip
  | succ n ih => skip
```
Each of the two {kw}`skip` statements has a message associated with it.
The first shows the base case:
```anchorError plusR_ind_zero_left_2a
unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0
```
The second shows the induction step:
```anchorError plusR_ind_zero_left_2b
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 (n + 1)
```
In the induction step, the inaccessible names with daggers have been replaced with the names provided after {lit}`succ`, namely {anchorName plusR_ind_zero_left_2a}`n` and {anchorName plusR_ind_zero_left_2a}`ih`.

The cases after {kw}`induction`{lit}` ...`{kw}`with` are not patterns: they consist of the name of a goal followed by zero or more names.
The names are used for assumptions introduced in the goal; it is an error to provide more names than the goal introduces:
```anchor plusR_ind_zero_left_3
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => skip
  | succ n ih lots of names => skip
```
```anchorError plusR_ind_zero_left_3
Too many variable names provided at alternative 'succ': 5 provided, but 2 expected
```

Focusing on the base case, the {kw}`rfl` tactic works just as well inside of the {kw}`induction` tactic as it does in a recursive function:
```anchor plusR_ind_zero_left_4
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih => skip
```
In the recursive function version of the proof, a type annotation made the expected type something that was easier to understand.
In the tactic language, there are a number of specific ways to transform a goal to make it easier to solve.
The {kw}`unfold` tactic replaces a defined name with its definition:
```anchor plusR_ind_zero_left_5
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
```
Now, the right-hand side of the equality in the goal has become {anchorTerm others}`Nat.plusR 0 n + 1` instead of {anchorTerm others}`Nat.plusR 0 (Nat.succ n)`:
```anchorError plusR_ind_zero_left_5
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 n + 1
```

Instead of appealing to functions like {anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`congrArg` and operators like {anchorTerm appendR (module:=Examples.DependentTypes.Pitfalls)}`▸`, there are tactics that allow equality proofs to be used to transform proof goals.
One of the most important is {kw}`rw`, which takes a list of equality proofs and replaces the left side with the right side in the goal.
This almost does the right thing in {anchorName plusR_ind_zero_left_6}`plusR_zero_left`:
```anchor plusR_ind_zero_left_6
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [ih]
```
However, the direction of the rewrite was incorrect.
Replacing {anchorName others}`n` with {anchorTerm others}`Nat.plusR 0 n` made the goal more complicated rather than less complicated:
```anchorError plusR_ind_zero_left_6
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ Nat.plusR 0 n + 1 = Nat.plusR 0 (Nat.plusR 0 n) + 1
```
This can be remedied by placing a left arrow before {anchorName plusR_zero_left_done}`ih` in the call to {kw}`rw`, which instructs it to replace the right-hand side of the equality with the left-hand side:

```anchor plusR_zero_left_done
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [←ih]
```
This rewrite makes both sides of the equation identical, and Lean takes care of the {kw}`rfl` on its own.
The proof is complete.

# Tactic Golf
%%%
tag := "tactic-golf"
%%%

So far, the tactic language has not shown its true value.
The above proof is no shorter than the recursive function; it's merely written in a domain-specific language instead of the full Lean language.
But proofs with tactics can be shorter, easier, and more maintainable.
Just as a lower score is better in the game of golf, a shorter proof is better in the game of tactic golf.

The induction step of {anchorName plusR_zero_left_golf_1}`plusR_zero_left` can be proved using the simplification tactic {tactic}`simp`.
Using {tactic}`simp` on its own does not help:
```anchor plusR_zero_left_golf_1
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp
```
```anchorError plusR_zero_left_golf_1
`simp` made no progress
```
However, {tactic}`simp` can be configured to make use of a set of definitions.
Just like {kw}`rw`, these arguments are provided in a list.
Asking {tactic}`simp` to take the definition of {anchorName plusR_zero_left_golf_1}`Nat.plusR` into account leads to a simpler goal:
```anchor plusR_zero_left_golf_2
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
```
```anchorError plusR_zero_left_golf_2
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n = Nat.plusR 0 n
```
In particular, the goal is now identical to the induction hypothesis.
In addition to automatically proving simple equality statements, the simplifier automatically replaces goals like {anchorTerm others}`Nat.succ A = Nat.succ B` with {anchorTerm others}`A = B`.
Because the induction hypothesis {anchorName plusR_zero_left_golf_3}`ih` has exactly the right type, the {kw}`exact` tactic can indicate that it should be used:

```anchor plusR_zero_left_golf_3
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    exact ih
```

However, the use of {kw}`exact` is somewhat fragile.
Renaming the induction hypothesis, which may happen while “golfing” the proof, would cause this proof to stop working.
The {kw}`assumption` tactic solves the current goal if _any_ of the assumptions match it:

```anchor plusR_zero_left_golf_4
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    assumption
```

This proof is no shorter than the prior proof that used unfolding and explicit rewriting.
However, a series of transformations can make it much shorter, taking advantage of the fact that {tactic}`simp` can solve many kinds of goals.
The first step is to drop the {kw}`with` at the end of {kw}`induction`.
For structured, readable proofs, the {kw}`with` syntax is convenient.
It complains if any cases are missing, and it shows the structure of the induction clearly.
But shortening proofs can often require a more liberal approach.

Using {kw}`induction` without {kw}`with` simply results in a proof state with two goals.
The {kw}`case` tactic can be used to select one of them, just as in the branches of the {kw}`induction`{lit}` ...`{kw}`with` tactic.
In other words, the following proof is equivalent to the prior proof:

```anchor plusR_zero_left_golf_5
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k
  case zero => rfl
  case succ n ih =>
    simp [Nat.plusR]
    assumption
```

In a context with a single goal (namely, {anchorTerm plusR_zero_left_golf_6a}`k = Nat.plusR 0 k`), the {anchorTerm plusR_zero_left_golf_5}`induction k` tactic yields two goals.
In general, a tactic will either fail with an error or take a goal and transform it into zero or more new goals.
Each new goal represents what remains to be proved.
If the result is zero goals, then the tactic was a success, and that part of the proof is done.

The {kw}`<;>` operator takes two tactics as arguments, resulting in a new tactic.
{lit}`T1 `{kw}`<;>`{lit}` T2` applies {lit}`T1` to the current goal, and then applies {lit}`T2` in _all_ goals created by {lit}`T1`.
In other words, {kw}`<;>` enables a general tactic that can solve many kinds of goals to be used on multiple new goals all at once.
One such general tactic is {tactic}`simp`.

Because {tactic}`simp` can both complete the proof of the base case and make progress on the proof of the induction step, using it with {kw}`induction` and {kw}`<;>` shortens the proof:
```anchor plusR_zero_left_golf_6a
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR]
```
This results in only a single goal, the transformed induction step:
```anchorError plusR_zero_left_golf_6a
unsolved goals
case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ = Nat.plusR 0 n✝
```
Running {kw}`assumption` in this goal completes the proof:

```anchor plusR_zero_left_golf_6
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR] <;> assumption
```
Here, {kw}`exact` would not have been possible, because {lit}`ih` was never explicitly named.

For beginners, this proof is not easier to read.
However, a common pattern for expert users is to take care of a number of simple cases with powerful tactics like {tactic}`simp`, allowing them to focus the text of the proof on the interesting cases.
Additionally, these proofs tend to be more robust in the face of small changes to the functions and datatypes involved in the proof.
The game of tactic golf is a useful part of developing good taste and style when writing proofs.

# Induction on Other Datatypes
%%%
tag := "induction-other-types"
%%%

Mathematical induction proves a statement for natural numbers by providing a base case for {anchorName others}`Nat.zero` and an induction step for {anchorName others}`Nat.succ`.
The principle of induction is also valid for other datatypes.
Constructors without recursive arguments form the base cases, while constructors with recursive arguments form the induction steps.
The ability to carry out proofs by induction is the very reason why they are called _inductive_ datatypes.

One example of this is induction on binary trees.
Induction on binary trees is a proof technique where a statement is proven for _all_ binary trees in two steps:
 1. The statement is shown to hold for {anchorName TreeCtors}`BinTree.leaf`. This is called the base case.
 2. Under the assumption that the statement holds for some arbitrarily chosen trees {anchorName TreeCtors}`l` and {anchorName TreeCtors}`r`, it is shown to hold for {anchorTerm TreeCtors}`BinTree.branch l x r`, where {anchorName TreeCtors}`x` is an arbitrarily-chosen new data point. This is called the _induction step_. The assumptions that the statement holds for {anchorName TreeCtors}`l` and {anchorName TreeCtors}`r` are called the _induction hypotheses_.

{anchorName BinTree_count}`BinTree.count` counts the number of branches in a tree:

```anchor BinTree_count
def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count
```
{ref "leading-dot-notation"}[Mirroring a tree] does not change the number of branches in it.
This can be proven using induction on trees.
The first step is to state the theorem and invoke {kw}`induction`:
```anchor mirror_count_0a
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => skip
  | branch l x r ihl ihr => skip
```
The base case states that counting the mirror of a leaf is the same as counting the leaf:
```anchorError mirror_count_0a
unsolved goals
case leaf
α : Type
⊢ leaf.mirror.count = leaf.count
```
The induction step allows the assumption that mirroring the left and right subtrees won't affect their branch counts, and requests a proof that mirroring a branch with these subtrees also preserves the overall branch count:
```anchorError mirror_count_0b
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ (l.branch x r).mirror.count = (l.branch x r).count
```


The base case is true because mirroring {anchorName mirror_count_1}`leaf` results in {anchorName mirror_count_1}`leaf`, so the left and right sides are definitionally equal.
This can be expressed by using {tactic}`simp` with instructions to unfold {anchorName mirror_count_1}`BinTree.mirror`:
```anchor mirror_count_1
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr => skip
```
In the induction step, nothing in the goal immediately matches the induction hypotheses.
Simplifying using the definitions of {anchorName mirror_count_2}`BinTree.count` and {anchorName mirror_count_2}`BinTree.mirror` reveals the relationship:
```anchor mirror_count_2
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
```
```anchorError mirror_count_2
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ 1 + r.mirror.count + l.mirror.count = 1 + l.count + r.count
```
Both induction hypotheses can be used to rewrite the left-hand side of the goal into something almost like the right-hand side:
```anchor mirror_count_3
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
    rw [ihl, ihr]
```
```anchorError mirror_count_3
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ 1 + r.count + l.count = 1 + l.count + r.count
```

The {tactic}`simp` tactic can use additional arithmetic identities when passed the {anchorTerm mirror_count_4}`+arith` option.
It is enough to prove this goal, yielding:

```anchor mirror_count_4
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
    rw [ihl, ihr]
    simp +arith
```

In addition to definitions to be unfolded, the simplifier can also be passed names of equality proofs to use as rewrites while it simplifies proof goals.
{anchorName mirror_count_5}`BinTree.mirror_count` can also be written:

```anchor mirror_count_5
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp +arith [BinTree.mirror, BinTree.count, ihl, ihr]
```
As proofs grow more complicated, listing assumptions by hand can become tedious.
Furthermore, manually writing assumption names can make it more difficult to re-use proof steps for multiple subgoals.
The argument {lit}`*` to {tactic}`simp` or {kw}`simp +arith` instructs them to use _all_ assumptions while simplifying or solving the goal.
In other words, the proof could also be written:

```anchor mirror_count_6
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp +arith [BinTree.mirror, BinTree.count, *]
```
Because both branches are using the simplifier, the proof can be reduced to:

```anchor mirror_count_7
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t <;> simp +arith [BinTree.mirror, BinTree.count, *]
```

# The {lit}`grind` Tactic
%%%
tag := "grind"
%%%

The {tactic}`grind` tactic can automatically prove many theorems.
Like {tactic}`simp`, it accepts an optional list of additional facts to take into consideration or functions to unfold; unlike {tactic}`simp`, it automatically takes local hypotheses into consideration.
Additionally, {tactic}`grind`'s support for reasoning about specific mathematical domains is far stronger than {tactic}`simp`'s arithmetic support.
The proof of {anchorName mirror_count_8}`BinTree.mirror_count` can rewritten to use {tactic}`grind`:
```anchor mirror_count_8
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t <;> grind [BinTree.mirror, BinTree.count]
```

Because the proofs in this book are fairly modest, most of them do not provide an opportunity for {tactic}`grind` to show its full power.
However, it is very convenient in some of the later proofs in the book.

# Exercises
%%%
tag := "tactics-induction-proofs-exercises"
%%%

 * Prove {anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`plusR_succ_left` using the {kw}`induction`{lit}` ...`{kw}`with` tactic.
 * Rewrite the proof of {anchorName plusR_succ_left (module:=Examples.DependentTypes.Pitfalls)}`plusR_succ_left` to use {kw}`<;>` in a single line.
 * Prove that appending lists is associative using induction on lists:
   ```anchorTerm ex
   theorem List.append_assoc (xs ys zs : List α) :
       xs ++ (ys ++ zs) = (xs ++ ys) ++ zs
   ```
