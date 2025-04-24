# Interlude: Propositions, Proofs, and Indexing

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
```output error
{{#example_out Examples/Props.lean outOfBounds}}
```
This error message is saying Lean tried to automatically mathematically prove that `3 < woodlandCritters.length` (i.e. `3 < List.length woodlandCritters`), which would mean that the lookup was safe, but that it could not do so.
Out-of-bounds errors are a common class of bugs, and Lean uses its dual nature as a programming language and a theorem prover to rule out as many as possible.

Understanding how this works requires an understanding of three key ideas: propositions, proofs, and tactics.

## Propositions and Proofs

A _proposition_ is a statement that can be true or false.
All of the following English sentences are propositions:

 * 1 + 1 = 2
 * Addition is commutative.
 * There are infinitely many prime numbers.
 * 1 + 1 = 15
 * Paris is the capital of France.
 * Buenos Aires is the capital of South Korea.
 * All birds can fly.

On the other hand, nonsense statements are not propositions.
Despite being grammatical, none of the following are propositions:

 * 1 + green = ice cream
 * All capital cities are prime numbers.
 * At least one gorg is a fleep.

Propositions come in two varieties: those that are purely mathematical, relying only on our definitions of concepts, and those that are facts about the world.
Theorem provers like Lean are concerned with the former category, and have nothing to say about the flight capabilities of penguins or the legal status of cities.

A _proof_ is a convincing argument that a proposition is true.
For mathematical propositions, these arguments make use of the definitions of the concepts that are involved as well as the rules of logical argumentation.
Most proofs are written for people to understand, and leave out many tedious details.
Computer-aided theorem provers like Lean are designed to allow mathematicians to write proofs while omitting many details, and it is the software's responsibility to fill in the missing explicit steps.
These steps can be mechanically checked.
This decreases the likelihood of oversights or mistakes.

In Lean, a program's type describes the ways it can be interacted with.
For instance, a program of type `Nat → List String` is a function that takes a `Nat` argument and produces a list of strings.
In other words, each type specifies what counts as a program with that type.

In Lean, propositions are in fact types.
They specify what counts as evidence that the statement is true.
The proposition is proved by providing this evidence, which is checked by Lean.
On the other hand, if the proposition is false, then it will be impossible to construct this evidence.

For example, the proposition "1 + 1 = 2" can be written directly in Lean.
The evidence for this proposition is the constructor `rfl`, which is short for _reflexivity_.
In mathematics, a relation is _reflexive_ if every element is related to itself; this is a basic requirement in order to have a sensible notion of equality.
Because `1 + 1` computes to `2`, they are really the same thing:
```lean
{{#example_decl Examples/Props.lean onePlusOneIsTwo}}
```
On the other hand, `rfl` does not prove the false proposition "1 + 1 = 15":
```lean
{{#example_in Examples/Props.lean onePlusOneIsFifteen}}
```
```output error
{{#example_out Examples/Props.lean onePlusOneIsFifteen}}
```
This error message indicates that `rfl` can prove that two expressions are equal when both sides of the equality statement are already the same number.
Because `1 + 1` evaluates directly to `2`, they are considered to be the same, which allows `onePlusOneIsTwo` to be accepted.
Just as `Type` describes types such as `Nat`, `String`, and `List (Nat × String × (Int → Float))` that represent data structures and functions, `Prop` describes propositions.

When a proposition has been proven, it is called a _theorem_.
In Lean, it is conventional to declare theorems with the `theorem` keyword instead of `def`.
This helps readers see which declarations are intended to be read as mathematical proofs, and which are definitions.
Generally speaking, with a proof, what matters is that there is evidence that a proposition is true, but it's not particularly important _which_ evidence was provided.
With definitions, on the other hand, it matters very much which particular value is selected—after all, a definition of addition that always returns `0` is clearly wrong.
Because the details of a proof don't matter for later proofs, using the `theorem` keyword enables greater parallelism in the Lean compiler.

The prior example could be rewritten as follows:
```lean
{{#example_decl Examples/Props.lean onePlusOneIsTwoProp}}
```

## Tactics

Proofs are normally written using _tactics_, rather than by providing evidence directly.
Tactics are small programs that construct evidence for a proposition.
These programs run in a _proof state_ that tracks the statement that is to be proved (called the _goal_) along with the assumptions that are available to prove it.
Running a tactic on a goal results in a new proof state that contains new goals.
The proof is complete when all goals have been proven.

To write a proof with tactics, begin the definition with `by`.
Writing `by` puts Lean into tactic mode until the end of the next indented block.
While in tactic mode, Lean provides ongoing feedback about the current proof state.
Written with tactics, `onePlusOneIsTwo` is still quite short:
```leantac
{{#example_decl Examples/Props.lean onePlusOneIsTwoTactics}}
```
The `decide` tactic invokes a _decision procedure_, which is a program that can check whether a statement is true or false, returning a suitable proof in either case.
It is primarily used when working with concrete values like `1` and `2`.
The other important tactic in this book is `simp`, short for "simplify", which is the workhorse of Lean proofs.
It rewrites the goal to as simple a form as possible.
In many cases, this rewriting simplifies the statement so much that it can be automatically proved.
Behind the scenes, a detailed formal proof is constructed, but using `simp` hides this complexity.


Tactics are useful for a number of reasons:
 1. Many proofs are complicated and tedious when written out down to the smallest detail, and tactics can automate these uninteresting parts.
 2. Proofs written with tactics are easier to maintain over time, because flexible automation can paper over small changes to definitions.
 3. Because a single tactic can prove many different theorems, Lean can use tactics behind the scenes to free users from writing proofs by hand. For instance, an array lookup requires a proof that the index is in bounds, and a tactic can typically construct that proof without the user needing to worry about it.

Behind the scenes, indexing notation uses a tactic to prove that the user's lookup operation is safe.
This tactic takes many facts about arithemtic into account, combining them with any locally-known facts to attempt to prove that the index is in bounds.


## Connectives

The basic building blocks of logic, such as "and", "or", "true", "false", and "not", are called _logical connectives_.
Each connective defines what counts as evidence of its truth.
For example, to prove a statement "_A_ and _B_", one must prove both _A_ and _B_.
This means that evidence for "_A_ and _B_" is a pair that contains both evidence for _A_ and evidence for _B_.
Similarly, evidence for "_A_ or _B_" consists of either evidence for _A_ or evidence for _B_.

In particular, most of these connectives are defined like datatypes, and they have constructors.
If `A` and `B` are propositions, then "`A` and `B`" (written `{{#example_in Examples/Props.lean AndProp}}`) is a proposition.
Evidence for `A ∧ B` consists of the constructor `{{#example_in Examples/Props.lean AndIntro}}`, which has the type `{{#example_out Examples/Props.lean AndIntro}}`.
Replacing `A` and `B` with concrete propositions, it is possible to prove `{{#example_out Examples/Props.lean AndIntroEx}}` with `{{#example_in Examples/Props.lean AndIntroEx}}`.
Of course, `decide` is also powerful enough to find this proof:
```leantac
{{#example_decl Examples/Props.lean AndIntroExTac}}
```

Similarly, "`A` or `B`" (written `{{#example_in Examples/Props.lean OrProp}}`) has two constructors, because a proof of "`A` or `B`" requires only that one of the two underlying propositions be true.
There are two constructors: `{{#example_in Examples/Props.lean OrIntro1}}`, with type `{{#example_out Examples/Props.lean OrIntro1}}`, and `{{#example_in Examples/Props.lean OrIntro2}}`, with type `{{#example_out Examples/Props.lean OrIntro2}}`.

Implication (if _A_ then _B_) is represented using functions.
In particular, a function that transforms evidence for _A_ into evidence for _B_ is itself evidence that _A_ implies _B_.
This is different from the usual description of implication, in which `A → B` is shorthand for `¬A ∨ B`, but the two formulations are equivalent.

Because evidence for an "and" is a constructor, it can be used with pattern matching.
For instance, a proof that _A_ and _B_ implies _A_ or _B_ is a function that pulls the evidence of _A_ (or of _B_) out of the evidence for _A_ and _B_, and then uses this evidence to produce evidence of _A_ or _B_:
```lean
{{#example_decl Examples/Props.lean andImpliesOr}}
```


| Connective      | Lean Syntax | Evidence     |
|-----------------|-------------|--------------|
| True            | `True`      | `True.intro : True` |
| False           | `False`     | No evidence  |
| _A_ and _B_     | `A ∧ B`     | `And.intro : A → B → A ∧ B` |
| _A_ or _B_      | `A ∨ B`     | Either `Or.inl : A → A ∨ B` or `Or.inr : B → A ∨ B` |
| _A_ implies _B_ | `A → B`     | A function that transforms evidence of _A_ into evidence of _B_ |
| not _A_         | `¬A`        | A function that would transform evidence of _A_ into evidence of `False` |

The `decide` tactic can prove theorems that use these connectives.
For example:
```leantac
{{#example_decl Examples/Props.lean connectivesD}}
```

## Evidence as Arguments

In some cases, safely indexing into a list requires that the list have some minimum size, but the list itself is a variable rather than a concrete value.
For this lookup to be safe, there must be some evidence that the list is long enough.
One of the easiest ways to make indexing safe is to have the function that performs a lookup into a data structure take the required evidence of safety as an argument.
For instance, a function that returns the third entry in a list is not generally safe because lists might contain zero, one, or two entries:
```lean
{{#example_in Examples/Props.lean thirdErr}}
```
```output error
{{#example_out Examples/Props.lean thirdErr}}
```
However, the obligation to show that the list has at least three entries can be imposed on the caller by adding an argument that consists of evidence that the indexing operation is safe:
```lean
{{#example_decl Examples/Props.lean third}}
```
In this example, `xs.length > 2` is not a program that checks _whether_ `xs` has more than 2 entries.
It is a proposition that could be true or false, and the argument `ok` must be evidence that it is true.

When the function is called on a concrete list, its length is known.
In these cases, `by decide` can construct the evidence automatically:
```leantac
{{#example_in Examples/Props.lean thirdCritters}}
```
```output info
{{#example_out Examples/Props.lean thirdCritters}}
```

## Indexing Without Evidence

In cases where it's not practical to prove that an indexing operation is in bounds, there are other alternatives.
Adding a question mark results in an `Option`, where the result is `some` if the index is in bounds, and `none` otherwise.
For example:
```lean
{{#example_decl Examples/Props.lean thirdOption}}

{{#example_in Examples/Props.lean thirdOptionCritters}}
```
```output info
{{#example_out Examples/Props.lean thirdOptionCritters}}
```
```lean
{{#example_in Examples/Props.lean thirdOptionTwo}}
```
```output info
{{#example_out Examples/Props.lean thirdOptionTwo}}
```

There is also a version that crashes the program when the index is out of bounds, rather than returning an `Option`:
```lean
{{#example_in Examples/Props.lean crittersBang}}
```
```output info
{{#example_out Examples/Props.lean crittersBang}}
```


## Messages You May Meet
In addition to proving that a statement is true, the `decide` tactic can also prove that it is false.
When asked to prove that a one-element list has more than two elements, it returns an error that indicates that the statement is indeed false:
```lean
{{#example_in Examples/Props.lean thirdRabbitErr}}
```
```output error
{{#example_out Examples/Props.lean thirdRabbitErr}}
```

The `simp` and `decide` tactics do not automatically unfold definitions with `def`.
Attempting to prove `OnePlusOneIsTwo` using `simp` fails:
```leantac
{{#example_in Examples/Props.lean onePlusOneIsStillTwo}}
```
The error messages simply states that it could do nothing, because without unfolding `OnePlusOneIsTwo`, no progress can be made:
```output error
{{#example_out Examples/Props.lean onePlusOneIsStillTwo}}
```
Using `decide` also fails:
```leantac
{{#example_in Examples/Props.lean onePlusOneIsStillTwo2}}
```
This is also due to it not unfolding `OnePlusOneIsTwo`:
```output error
{{#example_out Examples/Props.lean onePlusOneIsStillTwo2}}
```
Defining `OnePlusOneIsTwo` with [`abbrev` fixes the problem](getting-to-know/functions-and-definitions.md#messages-you-may-meet) by marking the definition for unfolding.

In addition to the error that occurs when Lean is unable to find compile-time evidence that an indexing operation is safe, polymorphic functions that use unsafe indexing may produce the following message:
```lean
{{#example_in Examples/Props.lean unsafeThird}}
```
```output error
{{#example_out Examples/Props.lean unsafeThird}}
```
This is due to a technical restriction that is part of keeping Lean usable as both a logic for proving theorems and a programming language.
In particular, only programs whose types contain at least one value are allowed to crash.
This is because a proposition in Lean is a kind of type that classifies evidence of its truth.
False propositions have no such evidence.
If a program with an empty type could crash, then that crashing program could be used as a kind of fake evidence for a false proposition.

Internally, Lean contains a table of types that are known to have at least one value.
This error is saying that some arbitrary type `α` is not necessarily in that table.
The next chapter describes how to add to this table, and how to successfully write functions like `unsafeThird`.

Adding whitespace between a list and the brackets used for lookup can cause another message:
```lean
{{#example_in Examples/Props.lean extraSpace}}
```
```output error
{{#example_out Examples/Props.lean extraSpace}}
```
Adding a space causes Lean to treat the expression as a function application, and the index as a list that contains a single number.
This error message results from having Lean attempt to treat `woodlandCritters` as a function.

## Exercises

* Prove the following theorems using `rfl`: `2 + 3 = 5`, `15 - 8 = 7`, `"Hello, ".append "world" = "Hello, world"`. What happens if `rfl` is used to prove `5 < 18`? Why?
* Prove the following theorems using `by decide`: `2 + 3 = 5`, `15 - 8 = 7`, `"Hello, ".append "world" = "Hello, world"`, `5 < 18`.
* Write a function that looks up the fifth entry in a list. Pass the evidence that this lookup is safe as an argument to the function.
