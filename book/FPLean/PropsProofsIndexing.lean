import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"

set_option verso.exampleModule "Examples.Props"

set_option pp.rawOnError true

#doc (Manual) "Interlude: Propositions, Proofs, and Indexing" =>
%%%
tag := "props-proofs-indexing"
number := false
htmlSplit := .never
%%%

Like many languages, Lean uses square brackets for indexing into arrays and lists.
For instance, if {moduleTerm}`woodlandCritters` is defined as follows:

```anchor woodlandCritters
def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]
```

then the individual components can be extracted:

```anchor animals
def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]
```

However, attempting to extract the fourth element results in a compile-time error, rather than a run-time error:

```anchor outOfBounds
def oops := woodlandCritters[3]
```

```anchorError outOfBounds
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ 3 < woodlandCritters.length
```

This error message is saying Lean tried to automatically mathematically prove that {moduleTerm}`3 < woodlandCritters.length` (i.e. {moduleTerm}`3 < List.length woodlandCritters`), which would mean that the lookup was safe, but that it could not do so.
Out-of-bounds errors are a common class of bugs, and Lean uses its dual nature as a programming language and a theorem prover to rule out as many as possible.

Understanding how this works requires an understanding of three key ideas: propositions, proofs, and tactics.

# Propositions and Proofs
%%%
tag := "propositions-and-proofs"
%%%

A _proposition_ is a statement that can be true or false.
All of the following English sentences are propositions:

 * $`1 + 1 = 2`
 * Addition is commutative.
 * There are infinitely many prime numbers.
 * $`1 + 1 = 15`
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
For instance, a program of type {moduleTerm}`Nat → List String` is a function that takes a {moduleTerm}`Nat` argument and produces a list of strings.
In other words, each type specifies what counts as a program with that type.

In Lean, propositions are in fact types.
They specify what counts as evidence that the statement is true.
The proposition is proved by providing this evidence, which is checked by Lean.
On the other hand, if the proposition is false, then it will be impossible to construct this evidence.

For example, the proposition $`1 + 1 = 2` can be written directly in Lean.
The evidence for this proposition is the constructor {moduleTerm}`rfl`, which is short for _reflexivity_.
In mathematics, a relation is _reflexive_ if every element is related to itself; this is a basic requirement in order to have a sensible notion of equality.
Because {moduleTerm}`1 + 1` computes to {moduleTerm}`2`, they are really the same thing:

```anchor onePlusOneIsTwo
def onePlusOneIsTwo : 1 + 1 = 2 := rfl
```

On the other hand, {moduleTerm}`rfl` does not prove the false proposition $`1 + 1 = 15`:

```anchor onePlusOneIsFifteen
def onePlusOneIsFifteen : 1 + 1 = 15 := rfl
```

```anchorError onePlusOneIsFifteen
Type mismatch
  rfl
has type
  ?m.16 = ?m.16
but is expected to have type
  1 + 1 = 15
```

This error message indicates that {moduleTerm}`rfl` can prove that two expressions are equal when both sides of the equality statement are already the same number.
Because {moduleTerm}`1 + 1` evaluates directly to {moduleTerm}`2`, they are considered to be the same, which allows {moduleTerm}`onePlusOneIsTwo` to be accepted.
Just as {moduleTerm}`Type` describes types such as {moduleTerm}`Nat`, {moduleTerm}`String`, and {moduleTerm}`List (Nat × String × (Int → Float))` that represent data structures and functions, {moduleTerm}`Prop` describes propositions.

When a proposition has been proven, it is called a _theorem_.
In Lean, it is conventional to declare theorems with the {kw}`theorem` keyword instead of {kw}`def`.
This helps readers see which declarations are intended to be read as mathematical proofs, and which are definitions.
Generally speaking, with a proof, what matters is that there is evidence that a proposition is true, but it's not particularly important _which_ evidence was provided.
With definitions, on the other hand, it matters very much which particular value is selected—after all, a definition of addition that always returns {anchorTerm SomeNats}`0` is clearly wrong.
Because the details of a proof don't matter for later proofs, using the {kw}`theorem` keyword enables greater parallelism in the Lean compiler.

The prior example could be rewritten as follows:

```anchor onePlusOneIsTwoProp
def OnePlusOneIsTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo : OnePlusOneIsTwo := rfl
```


# Tactics
%%%
tag := "tactics"
%%%

Proofs are normally written using _tactics_, rather than by providing evidence directly.
Tactics are small programs that construct evidence for a proposition.
These programs run in a _proof state_ that tracks the statement that is to be proved (called the _goal_) along with the assumptions that are available to prove it.
Running a tactic on a goal results in a new proof state that contains new goals.
The proof is complete when all goals have been proven.

To write a proof with tactics, begin the definition with {kw}`by`.
Writing {kw}`by` puts Lean into tactic mode until the end of the next indented block.
While in tactic mode, Lean provides ongoing feedback about the current proof state.
Written with tactics, {anchorTerm onePlusOneIsTwoTactics}`onePlusOneIsTwo` is still quite short:

```anchor onePlusOneIsTwoTactics
theorem onePlusOneIsTwo : 1 + 1 = 2 := by
  decide
```

The {tactic}`decide` tactic invokes a _decision procedure_, which is a program that can check whether a statement is true or false, returning a suitable proof in either case.
It is primarily used when working with concrete values like {anchorTerm SomeNats}`1` and {anchorTerm SomeNats}`2`.
The other important tactics in this book are {tactic}`simp`, short for “simplify,” and {tactic}`grind`, which can automatically prove many theorems.

Tactics are useful for a number of reasons:
 1. Many proofs are complicated and tedious when written out down to the smallest detail, and tactics can automate these uninteresting parts.
 2. Proofs written with tactics are easier to maintain over time, because flexible automation can paper over small changes to definitions.
 3. Because a single tactic can prove many different theorems, Lean can use tactics behind the scenes to free users from writing proofs by hand. For instance, an array lookup requires a proof that the index is in bounds, and a tactic can typically construct that proof without the user needing to worry about it.

Behind the scenes, indexing notation uses a tactic to prove that the user's lookup operation is safe.
This tactic takes many facts about arithmetic into account, combining them with any locally-known facts to attempt to prove that the index is in bounds.

The {tactic}`simp` tactic is a workhorse of Lean proofs.
It rewrites the goal to as simple a form as possible.
In many cases, this rewriting simplifies the statement so much that it can be automatically proved.
Behind the scenes, a detailed formal proof is constructed, but using {tactic}`simp` hides this complexity.

Like {tactic}`decide`, the {tactic}`grind` tactic is used to finish proofs.
It uses a collection of techniques from SMT solvers that can prove a wide variety of theorems.
Unlike {tactic}`simp`, {tactic}`grind` can never make progress towards a proof without completing it entirely; it either succeeds fully or fails.
The {tactic}`grind` tactic is very powerful, customizable, and extensible; due to this power and flexibility, its output when it fails to prove a theorem contains a lot of information that can help trained Lean users diagnose the reason for the failure.
This can be overwhelming in the beginning, so this chapter uses only {tactic}`decide` and {tactic}`simp`.

# Connectives
%%%
tag := "connectives"
%%%

The basic building blocks of logic, such as “and”, “or”, “true”, “false”, and “not”, are called {deftech}_logical connectives_.
Each connective defines what counts as evidence of its truth.
For example, to prove a statement “_A_ and _B_”, one must prove both _A_ and _B_.
This means that evidence for “_A_ and _B_” is a pair that contains both evidence for _A_ and evidence for _B_.
Similarly, evidence for “_A_ or _B_” consists of either evidence for _A_ or evidence for _B_.

In particular, most of these connectives are defined like datatypes, and they have constructors.
If {anchorTerm AndProp}`A` and {anchorTerm AndProp}`B` are propositions, then “{anchorTerm AndProp}`A` and {anchorTerm AndProp}`B`” (written {anchorTerm AndProp}`A ∧ B`) is a proposition.
Evidence for {anchorTerm AndProp}`A ∧ B` consists of the constructor {anchorTerm AndIntro}`And.intro`, which has the type {anchorTerm AndIntro}`A → B → A ∧ B`.
Replacing {anchorTerm AndIntro}`A` and {anchorTerm AndIntro}`B` with concrete propositions, it is possible to prove {anchorTerm AndIntroEx}`1 + 1 = 2 ∧ "Str".append "ing" = "String"` with {anchorTerm AndIntroEx}`And.intro rfl rfl`.
Of course, {tactic}`decide` is also powerful enough to find this proof:

```anchor AndIntroExTac
theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide
```


Similarly, “{anchorTerm OrProp}`A` or {anchorTerm OrProp}`B`” (written {anchorTerm OrProp}`A ∨ B`) has two constructors, because a proof of “{anchorTerm OrProp}`A` or {anchorTerm OrProp}`B`” requires only that one of the two underlying propositions be true.
There are two constructors: {anchorTerm OrIntro1}`Or.inl`, with type {anchorTerm OrIntro1}`A → A ∨ B`, and {anchorTerm OrIntro2}`Or.inr`, with type {anchorTerm OrIntro2}`B → A ∨ B`.

Implication (if {anchorTerm impliesDef}`A` then {anchorTerm impliesDef}`B`) is represented using functions.
In particular, a function that transforms evidence for {anchorTerm impliesDef}`A` into evidence for {anchorTerm impliesDef}`B` is itself evidence that {anchorTerm impliesDef}`A` implies {anchorTerm impliesDef}`B`.
This is different from the usual description of implication, in which {anchorTerm impliesDef}`A → B` is shorthand for {anchorTerm impliesDef}`¬A ∨ B`, but the two formulations are equivalent.

Because evidence for an “and” is a constructor, it can be used with pattern matching.
For instance, a proof that {anchorTerm andImpliesOr}`A` and {anchorTerm andImpliesOr}`B` implies {anchorTerm andImpliesOr}`A` or {anchorTerm andImpliesOr}`B` is a function that pulls the evidence of {anchorTerm andImpliesOr}`A` (or of {anchorTerm andImpliesOr}`B`) out of the evidence for {anchorTerm andImpliesOr}`A` and {anchorTerm andImpliesOr}`B`, and then uses this evidence to produce evidence of {anchorTerm andImpliesOr}`A` or {anchorTerm andImpliesOr}`B`:

```anchor andImpliesOr
theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a b => Or.inl a
```


:::table +header
*
  - Connective
  - Lean Syntax
  - Evidence
*
 -  True
 -  {anchorName connectiveTable}`True`
 -  {anchorTerm connectiveTable}`True.intro : True`

*
 -  False
 -  {anchorName connectiveTable}`False`
 -  No evidence

*
 -  {anchorName connectiveTable}`A` and {anchorName connectiveTable}`B`
 -  {anchorTerm connectiveTable}`A ∧ B`
 -  {anchorTerm connectiveTable}`And.intro : A → B → A ∧ B`

*
 -  {anchorName connectiveTable}`A` or {anchorName connectiveTable}`B`
 -  {anchorTerm connectiveTable}`A ∨ B`
 -  Either {anchorTerm connectiveTable}`Or.inl : A → A ∨ B` or {anchorTerm connectiveTable}`Or.inr : B → A ∨ B`

*
 -  {anchorName connectiveTable}`A` implies {anchorName connectiveTable}`B`
 -  {anchorTerm connectiveTable}`A → B`
 -  A function that transforms evidence of {anchorName connectiveTable}`A` into evidence of {anchorName connectiveTable}`B`

*
 -  not {anchorName connectiveTable}`A`
 -  {anchorTerm connectiveTable}`¬A`
 -  A function that would transform evidence of {anchorName connectiveTable}`A` into evidence of {anchorName connectiveTable}`False`


:::

The {tactic}`decide` tactic can prove theorems that use these connectives.
For example:

```anchor connectivesD
theorem onePlusOneOrLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by decide
theorem trueIsTrue : True := by decide
theorem trueOrFalse : True ∨ False := by decide
theorem falseImpliesTrue : False → True := by decide
```


# Evidence as Arguments
%%%
tag := "evidence-passing"
%%%

In some cases, safely indexing into a list requires that the list have some minimum size, but the list itself is a variable rather than a concrete value.
For this lookup to be safe, there must be some evidence that the list is long enough.
One of the easiest ways to make indexing safe is to have the function that performs a lookup into a data structure take the required evidence of safety as an argument.
For instance, a function that returns the third entry in a list is not generally safe because lists might contain zero, one, or two entries:

```anchor thirdErr
def third (xs : List α) : α := xs[2]
```

```anchorError thirdErr
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.5379
xs : List α
⊢ 2 < xs.length
```

However, the obligation to show that the list has at least three entries can be imposed on the caller by adding an argument that consists of evidence that the indexing operation is safe:

```anchor third
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
```

In this example, {anchorTerm third}`xs.length > 2` is not a program that checks _whether_ {anchorTerm third}`xs` has more than 2 entries.
It is a proposition that could be true or false, and the argument {anchorTerm third}`ok` must be evidence that it is true.

When the function is called on a concrete list, its length is known.
In these cases, {anchorTerm thirdCritters}`by decide` can construct the evidence automatically:

```anchor thirdCritters
#eval third woodlandCritters (by decide)
```

```anchorInfo thirdCritters
"snail"
```


# Indexing Without Evidence
%%%
tag := "indexing-without-evidence"
%%%

In cases where it's not practical to prove that an indexing operation is in bounds, there are other alternatives.
Adding a question mark results in an {anchorName thirdOption}`Option`, where the result is {anchorName OptionNames}`some` if the index is in bounds, and {anchorName OptionNames}`none` otherwise.
For example:


```anchor thirdOption
def thirdOption (xs : List α) : Option α := xs[2]?
```

```anchor thirdOptionCritters
#eval thirdOption woodlandCritters
```

```anchorInfo thirdOptionCritters
some "snail"
```

```anchor thirdOptionTwo
#eval thirdOption ["only", "two"]
```

```anchorInfo thirdOptionTwo
none
```

:::paragraph
There is also a version that crashes the program when the index is out of bounds, rather than returning an {moduleTerm}`Option`:

```anchor crittersBang
#eval woodlandCritters[1]!
```

```anchorInfo crittersBang
"deer"
```
:::


# Messages You May Meet
%%%
tag := "props-proofs-indexing-messages"
%%%
In addition to proving that a statement is true, the {anchorTerm thirdRabbitErr}`decide` tactic can also prove that it is false.
When asked to prove that a one-element list has more than two elements, it returns an error that indicates that the statement is indeed false:

```anchor thirdRabbitErr
#eval third ["rabbit"] (by decide)
```


```anchorError thirdRabbitErr
Tactic `decide` proved that the proposition
  ["rabbit"].length > 2
is false
```


The {tactic}`simp` and {tactic}`decide` tactics do not automatically unfold definitions with {kw}`def`.
Attempting to prove {anchorTerm onePlusOneIsStillTwo}`OnePlusOneIsTwo` using {anchorTerm onePlusOneIsStillTwo}`simp` fails:

```anchor onePlusOneIsStillTwo
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by simp
```

The error messages simply states that it could do nothing, because without unfolding {anchorTerm onePlusOneIsStillTwo}`OnePlusOneIsTwo`, no progress can be made:

```anchorError onePlusOneIsStillTwo
`simp` made no progress
```

Using {anchorTerm onePlusOneIsStillTwo2}`decide` also fails:

```anchor onePlusOneIsStillTwo2
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by decide
```

This is also due to it not unfolding {anchorName onePlusOneIsStillTwo2}`OnePlusOneIsTwo`:

```anchorError onePlusOneIsStillTwo2
failed to synthesize
  Decidable OnePlusOneIsTwo

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

Defining {anchorName onePlusOneIsStillTwo}`OnePlusOneIsTwo` with {ref "abbrev-vs-def"}[{kw}`abbrev` fixes the problem] by marking the definition for unfolding.

In addition to the error that occurs when Lean is unable to find compile-time evidence that an indexing operation is safe, polymorphic functions that use unsafe indexing may produce the following message:

```anchor unsafeThird
def unsafeThird (xs : List α) : α := xs[2]!
```


```anchorError unsafeThird
failed to synthesize
  Inhabited α

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```

This is due to a technical restriction that is part of keeping Lean usable as both a logic for proving theorems and a programming language.
In particular, only programs whose types contain at least one value are allowed to crash.
This is because a proposition in Lean is a kind of type that classifies evidence of its truth.
False propositions have no such evidence.
If a program with an empty type could crash, then that crashing program could be used as a kind of fake evidence for a false proposition.

Internally, Lean contains a table of types that are known to have at least one value.
This error is saying that some arbitrary type {anchorTerm unsafeThird}`α` is not necessarily in that table.
The next chapter describes how to add to this table, and how to successfully write functions like {anchorTerm unsafeThird}`unsafeThird`.

Adding whitespace between a list and the brackets used for lookup can cause another message:

```anchor extraSpace
#eval woodlandCritters [1]
```


```anchorError extraSpace
Function expected at
  woodlandCritters
but this term has type
  List String

Note: Expected a function because this term is being applied to the argument
  [1]
```

Adding a space causes Lean to treat the expression as a function application, and the index as a list that contains a single number.
This error message results from having Lean attempt to treat {anchorTerm woodlandCritters}`woodlandCritters` as a function.

## Exercises
%%%
tag := "props-proofs-indexing-exercises"
%%%

* Prove the following theorems using {anchorTerm exercises}`rfl`: {anchorTerm exercises}`2 + 3 = 5`, {anchorTerm exercises}`15 - 8 = 7`, {anchorTerm exercises}`"Hello, ".append "world" = "Hello, world"`. What happens if {anchorTerm exercises}`rfl` is used to prove {anchorTerm exercises}`5 < 18`? Why?
* Prove the following theorems using {anchorTerm exercises}`by decide`: {anchorTerm exercises}`2 + 3 = 5`, {anchorTerm exercises}`15 - 8 = 7`, {anchorTerm exercises}`"Hello, ".append "world" = "Hello, world"`, {anchorTerm exercises}`5 < 18`.
* Write a function that looks up the fifth entry in a list. Pass the evidence that this lookup is safe as an argument to the function.
