# Propositions, Proofs, and Indexing

Like many languages, Lean uses square brackets for indexing into arrays and lists.
For instance, if `woodlandCritters` is defined as follows:
```lean
{{#example_decl Examples/Props.lean woodlandCritters}}
```
then the individual components can be extracted:
```lean
{{#example_decl Examples/Props.lean animals}}
```
However, attempting to extract the fourth element results in a compile-time error, rather than a run-time error:
```lean
{{#example_in Examples/Props.lean outOfBounds}}
```
```lean error
{{#example_out Examples/Props.lean outOfBounds}}
```
This error message is saying Lean tried to automatically mathematically prove that `3 < List.length woodlandCritters`, which would mean that the lookup was safe, but that it could not do so.
Out-of-bounds errors are a common class of bugs, and Lean uses its dual nature as a programming language and a theorem prover to rule out as many as possible.

Understanding how this works requires understanding of three key ideas: propositions, proofs, and tactics.

## Propositions and Proofs

A _proposition_ is a statement that can be true or false.
All of the following are propositions:

 * 1 + 1 = 2
 * Addition is commutative
 * There are infinitely many prime numbers
 * 1 + 1 = 15
 * Paris is the capital of France
 * Buenos Aires is the capital of South Korea
 * All birds can fly

On the other hand, nonsense statements that don't even make sense are not propositions.
None of the following are propositions:

 * 1 + green = ice cream
 * All capital cities are prime numbers
 * At least one gorg is a fleep

Propositions come in two varieties: those that are purely mathematical, relying only on our definitions of concepts, and those that are facts about the world.
Theorem provers like Lean are concerned with the former category.

A _proof_ is a convincing argument that a proposition is true.
For mathematical propositions, these arguments make use of the definitions of the concepts that are involved as well as the rules of logical argumentation.
Most proofs are written for people to understand, and leave out many tedious details.

In Lean, a type describes a program.
For instance, a program of type `Nat → List String` will take a `Nat` argument and produce a list of strings.
Similarly, a Lean proposition describes what counts as evidence that it is true.
The proposition is proved by providing this evidence.

For example, the proposition "1 + 1 = 2" can be written directly in Lean.
The evidence for this proposition is the constructor `rfl`, which is short for _reflexivity_:
```lean
{{#example_decl Examples/Props.lean onePlusOneIsTwo}}
```
A relation is reflexive if everything is related to itself.
In the case of equality, it simply means that every value is equal to itself.
In other words, 1 = 1, 2 = 2, 3 = 3, and so forth.
When Lean sees `rfl` being used to prove that `1 + 1 = 2`, it checks that the two sides of the equation are, in fact, equal, and then accepts the proof.

When a proposition has been proven, it is called a _theorem_.
In Lean, it is conventional to declare theorems with the `theorem` keyword instead of `def`.
This helps keep their roles clear in a file.

Just as `Type` describes types such as `Nat`, `String`, and `List (Nat × String × (Int → Float))` that represent data structures and functions, `Prop` describes propositions.
The prior example could be rewritten as follows:
```lean
{{#example_decl Examples/Props.lean onePlusOneIsTwoProp}}
```



## Tactics

Proofs are normally written using _tactics_, rather than by providing evidence directly.
Tactics are small programs that construct evidence for a proposition.
These programs run in a _proof state_ that tracks the statement that is to be proved along with the assumptions that are available to prove it.

To write a proof with tactics, begin the definition with `by`.
Writing `by` puts Lean into tactic mode until the end of the next indented block.
While in tactic mode, Lean provides ongoing feedback about the current proof state.
Written with tactics, `onePlusOneIsTwo` is still quite short:
```lean
{{#example_decl Examples/Props.lean onePlusOneIsTwoTactics}}
```
The `simp` tactic, short for "simplify", is the workhorse of Lean.
It rewrites the goal to as simple a form as possible, taking care of parts of the proof that are small enough.
In particular, it proves simple equality statements.
Behind the scenes, a detailed formal proof is constructed, but `simp` frees users from having to read or write these details.

Tactics are useful for a number of reasons:
 1. Many proofs are complicated and tedious when written out down to the smallest detail, and tactics can automate these parts.
 2. Proofs written with tactics are easier to maintain over time, because flexible automation can paper over small changes to definitions.
 3. Because a single tactic can prove many different theorems, Lean can use tactics behind the scenes to free users from writing proofs by hand. For instance, an array lookup requires a proof that the index is in bounds, and a tactic can typically construct that proof without the user needing to worry about it.


## Connectives

The basic building blocks of logic, such as "and", "or", "true", "false", and "not", are called _logical connectives_.
