import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Universes"

#doc (Manual) "Universes" =>
%%%
tag := "universe-levels"
%%%

In the interests of simplicity, this book has thus far papered over an important feature of Lean: _universes_.
A universe is a type that classifies other types.
Two of them are familiar: {anchorTerm TypeType}`Type` and {anchorTerm PropType}`Prop`.
{anchorTerm SomeTypes}`Type` classifies ordinary types, such as {anchorName SomeTypes}`Nat`, {anchorTerm SomeTypes}`String`, {anchorTerm SomeTypes}`Int → String × Char`, and {anchorTerm SomeTypes}`IO Unit`.
{anchorTerm PropType}`Prop` classifies propositions that may be true or false, such as {anchorTerm SomeTypes}`"nisse" = "elf"` or {anchorTerm SomeTypes}`3 > 2`.
The type of {anchorTerm PropType}`Prop` is {anchorTerm SomeTypes}`Type`:
```anchor PropType
#check Prop
```
```anchorInfo PropType
Prop : Type
```

For technical reasons, more universes than these two are needed.
In particular, {anchorTerm SomeTypes}`Type` cannot itself be a {anchorTerm SomeTypes}`Type`.
This would allow a logical paradox to be constructed and undermine Lean's usefulness as a theorem prover.

The formal argument for this is known as _Girard's Paradox_.
It is related to a better-known paradox known as _Russell's Paradox_, which was used to show that early versions of set theory were inconsistent.
In these set theories, a set can be defined by a property.
For example, one might have the set of all red things, the set of all fruit, the set of all natural numbers, or even the set of all sets.
Given a set, one can ask whether a given element is contained in it.
For instance, a bluebird is not contained in the set of all red things, but the set of all red things is contained in the set of all sets.
Indeed, the set of all sets even contains itself.

What about the set of all sets that do not contain themselves?
It contains the set of all red things, as the set of all red things is not itself red.
It does not contain the set of all sets, because the set of all sets contains itself.
But does it contain itself?
If it does contain itself, then it cannot contain itself.
But if it does not, then it must.

This is a contradiction, which demonstrates that something was wrong with the initial assumptions.
In particular, allowing sets to be constructed by providing an arbitrary property is too powerful.
Later versions of set theory restrict the formation of sets to remove the paradox.

A related paradox can be constructed in versions of dependent type theory that assign the type {anchorTerm SomeTypes}`Type` to {anchorTerm SomeTypes}`Type`.
To ensure that Lean has consistent logical foundations and can be used as a tool for mathematics, {anchorTerm SomeTypes}`Type` needs to have some other type.
This type is called {anchorTerm SomeTypes}`Type 1`:
```anchor TypeType
#check Type
```
```anchorInfo TypeType
Type : Type 1
```
Similarly, {anchorTerm Type1Type}`Type 1` is a {anchorTerm Type1Type}`Type 2`,
{anchorTerm Type2Type}`Type 2` is a {anchorTerm Type2Type}`Type 3`,
{anchorTerm Type3Type}`Type 3` is a {anchorTerm Type3Type}`Type 4`, and so forth.

Function types occupy the smallest universe that can contain both the argument type and the return type.
This means that {anchorTerm NatNatType}`Nat → Nat` is a {anchorTerm NatNatType}`Type`, {anchorTerm Fun00Type}`Type → Type` is a {anchorTerm Fun00Type}`Type 1`, and {anchorTerm Fun12Type}`Type 3` is a {anchorTerm Fun12Type}`Type 1 → Type 2`.

There is one exception to this rule.
If the return type of a function is a {anchorTerm PropType}`Prop`, then the whole function type is in {anchorTerm PropType}`Prop`, even if the argument is in a larger universe such as {anchorTerm SomeTypes}`Type` or even {anchorTerm SomeTypes}`Type 1`.
In particular, this means that predicates over values that have ordinary types are in {anchorTerm PropType}`Prop`.
For example, the type {anchorTerm FunPropType}`(n : Nat) → n = n + 0` represents a function from a {anchorTerm SomeTypes}`Nat` to evidence that it is equal to itself plus zero.
Even though {anchorTerm SomeTypes}`Nat` is in {anchorTerm SomeTypes}`Type`, this function type is in {anchorTerm FunPropType}`Prop` due to this rule.
Similarly, even though {anchorTerm SomeTypes}`Type` is in {anchorTerm SomeTypes}`Type 1`, the function type {anchorTerm FunTypePropType}`Type → 2 + 2 = 4` is still in {anchorTerm FunTypePropType}`Prop`.

# User Defined Types
%%%
tag := "inductive-type-universes"
%%%

Structures and inductive datatypes can be declared to inhabit particular universes.
Lean then checks whether each datatype avoids paradoxes by being in a universe that's large enough to prevent it from containing its own type.
For instance, in the following declaration, {anchorName MyList1}`MyList` is declared to reside in {anchorTerm SomeTypes}`Type`, and so is its type argument {anchorName MyList1}`α`:

```anchor MyList1
inductive MyList (α : Type) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```
{anchorTerm MyList1Type}`MyList` itself is a {anchorTerm MyList1Type}`Type → Type`.
This means that it cannot be used to contain actual types, because then its argument would be {anchorTerm SomeTypes}`Type`, which is a {anchorTerm SomeTypes}`Type 1`:
```anchor myListNat1Err
def myListOfNat : MyList Type :=
  .cons Nat .nil
```
```anchorError myListNat1Err
Application type mismatch: The argument
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  MyList Type
```

Updating {anchorName MyList2}`MyList` so that its argument is a {anchorTerm MyList2}`Type 1` results in a definition rejected by Lean:
```anchor MyList2
inductive MyList (α : Type 1) : Type where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```
```anchorError MyList2
Invalid universe level in constructor `MyList.cons`: Parameter has type
  α
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
```
This error occurs because the argument to {anchorTerm MyList2}`cons` with type {anchorName MyList2}`α` is from a larger universe than {anchorName MyList2}`MyList`.
Placing {anchorName MyList2}`MyList` itself in {anchorTerm SomeTypes}`Type 1` solves this issue, but at the cost of {anchorName MyList2}`MyList` now being itself inconvenient to use in contexts that expect a {anchorTerm SomeTypes}`Type`.

The specific rules that govern whether a datatype is allowed are somewhat complicated.
Generally speaking, it's easiest to start with the datatype in the same universe as the largest of its arguments.
Then, if Lean rejects the definition, increase its level by one, which will usually go through.

# Universe Polymorphism
%%%
tag := "universe-polymorphism"
%%%

Defining a datatype in a specific universe can lead to code duplication.
Placing {anchorName MyList1}`MyList` in {anchorTerm MyList1Type}`Type → Type` means that it can't be used for an actual list of types.
Placing it in {anchorTerm MyList15Type}`Type 1 → Type 1` means that it can't be used for a list of lists of types.
Rather than copy-pasting the datatype to create versions in {anchorTerm SomeTypes}`Type`, {anchorTerm SomeTypes}`Type 1`, {anchorTerm Type2Type}`Type 2`, and so on, a feature called _universe polymorphism_ can be used to write a single definition that can be instantiated in any of these universes.

Ordinary polymorphic types use variables to stand for types in a definition.
This allows Lean to fill in the variables differently, which enables these definitions to be used with a variety of types.
Similarly, universe polymorphism allows variables to stand for universes in a definition, enabling Lean to fill them in differently so that they can be used with a variety of universes.
Just as type arguments are conventionally named with Greek letters, universe arguments are conventionally named {lit}`u`, {lit}`v`, and {lit}`w`.

This definition of {anchorName MyList3}`MyList` doesn't specify a particular universe level, but instead uses a variable {anchorTerm MyList3}`u` to stand for any level.
If the resulting datatype is used with {anchorTerm SomeTypes}`Type`, then {anchorTerm MyList3}`u` is {lit}`0`, and if it's used with {anchorTerm Fun12Type}`Type 3`, then {anchorTerm MyList3}`u` is {lit}`3`:

```anchor MyList3
inductive MyList (α : Type u) : Type u where
  | nil : MyList α
  | cons : α → MyList α → MyList α
```

With this definition, the same definition of {anchorName MyList3}`MyList` can be used to contain both actual natural numbers and the natural number type itself:

```anchor myListOfNat3
def myListOfNumbers : MyList Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList Type :=
  .cons Nat .nil
```
It can even contain itself:

```anchor myListOfList3
def myListOfList : MyList (Type → Type) :=
  .cons MyList .nil
```

It would seem that this would make it possible to write a logical paradox.
After all, the whole point of the universe system is to rule out self-referential types.
Behind the scenes, however, each occurrence of {anchorName MyList3}`MyList` is provided with a universe level argument.
In essence, the universe-polymorphic definition of {anchorName MyList3}`MyList` created a _copy_ of the datatype at each level, and the level argument selects which copy is to be used.
These level arguments are written with a dot and curly braces, so {anchorTerm MyListDotZero}`MyList.{0} : Type → Type`, {anchorTerm MyListDotOne}`MyList.{1} : Type 1 → Type 1`, and {anchorTerm MyListDotTwo}`MyList.{2} : Type 2 → Type 2`.

Writing the levels explicitly, the prior example becomes:

```anchor myListOfList3Expl
def myListOfNumbers : MyList.{0} Nat :=
  .cons 0 (.cons 1 .nil)

def myListOfNat : MyList.{1} Type :=
  .cons Nat .nil

def myListOfList : MyList.{1} (Type → Type) :=
  .cons MyList.{0} .nil
```

When a universe-polymorphic definition takes multiple types as arguments, it's a good idea to give each argument its own level variable for maximum flexibility.
For example, a version of {anchorName SumNoMax}`Sum` with a single level argument can be written as follows:

```anchor SumNoMax
inductive Sum (α : Type u) (β : Type u) : Type u where
  | inl : α → Sum α β
  | inr : β → Sum α β
```
This definition can be used at multiple levels:

```anchor SumPoly
def stringOrNat : Sum String Nat := .inl "hello"

def typeOrType : Sum Type Type := .inr Nat
```
However, it requires that both arguments be in the same universe:
```anchor stringOrTypeLevels
def stringOrType : Sum String Type := .inr Nat
```
```anchorError stringOrTypeLevels
Application type mismatch: The argument
  Type
has type
  Type 1
of sort `Type 2` but is expected to have type
  Type
of sort `Type 1` in the application
  Sum String Type
```

This datatype can be made more flexible by using different variables for the two type arguments' universe levels, and then declaring that the resulting datatype is in the largest of the two:

```anchor SumMax
inductive Sum (α : Type u) (β : Type v) : Type (max u v) where
  | inl : α → Sum α β
  | inr : β → Sum α β
```
This allows {anchorName SumMax}`Sum` to be used with arguments from different universes:

```anchor stringOrTypeSum
def stringOrType : Sum String Type := .inr Nat
```

In positions where Lean expects a universe level, any of the following are allowed:
 * A concrete level, like {lit}`0` or {lit}`1`
 * A variable that stands for a level, such as {anchorTerm SumMax}`u` or {anchorTerm SumMax}`v`
 * The maximum of two levels, written as {anchorTerm SumMax}`max` applied to the levels
 * A level increase, written with {anchorTerm someTrueProps}`+ 1`

## Writing Universe-Polymorphic Definitions
%%%
tag := none
%%%

Until now, every datatype defined in this book has been in {anchorTerm SomeTypes}`Type`, the smallest universe of data.
When presenting polymorphic datatypes from the Lean standard library, such as {anchorName SomeTypes}`List` and {anchorName SumMax}`Sum`, this book created non-universe-polymorphic versions of them.
The real versions use universe polymorphism to enable code re-use between type-level and non-type-level programs.

There are a few general guidelines to follow when writing universe-polymorphic types.
First off, independent type arguments should have different universe variables, which enables the polymorphic definition to be used with a wider variety of arguments, increasing the potential for code reuse.
Secondly, the whole type is itself typically either in the maximum of all the universe variables, or one greater than this maximum.
Try the smaller of the two first.
Finally, it's a good idea to put the new type in as small of a universe as possible, which allows it to be used more flexibly in other contexts.
Non-polymorphic types, such as {anchorTerm SomeTypes}`Nat` and {anchorName SomeTypes}`String`, can be placed directly in {anchorTerm Type0Type}`Type 0`.

## {anchorTerm PropType}`Prop` and Polymorphism
%%%
tag := none
%%%


Just as {anchorTerm SomeTypes}`Type`, {anchorTerm SomeTypes}`Type 1`, and so on describe types that classify programs and data, {anchorTerm PropType}`Prop` classifies logical propositions.
A type in {anchorTerm PropType}`Prop` describes what counts as convincing evidence for the truth of a statement.
Propositions are like ordinary types in many ways: they can be declared inductively, they can have constructors, and functions can take propositions as arguments.
However, unlike datatypes, it typically doesn't matter _which_ evidence is provided for the truth of a statement, only _that_ evidence is provided.
On the other hand, it is very important that a program not only return a {anchorTerm SomeTypes}`Nat`, but that it's the _correct_ {anchorTerm SomeTypes}`Nat`.

{anchorTerm PropType}`Prop` is at the bottom of the universe hierarchy, and the type of {anchorTerm PropType}`Prop` is {anchorTerm SomeTypes}`Type`.
This means that {anchorTerm PropType}`Prop` is a suitable argument to provide to {anchorName SomeTypes}`List`, for the same reason that {anchorTerm SomeTypes}`Nat` is.
Lists of propositions have type {anchorTerm SomeTypes}`List Prop`:

```anchor someTrueProps
def someTruePropositions : List Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
```
Filling out the universe argument explicitly demonstrates that {anchorTerm PropType}`Prop` is a {anchorTerm SomeTypes}`Type`:

```anchor someTruePropsExp
def someTruePropositions : List.{0} Prop := [
  1 + 1 = 2,
  "Hello, " ++ "world!" = "Hello, world!"
]
```

Behind the scenes, {anchorTerm PropType}`Prop` and {anchorTerm SomeTypes}`Type` are united into a single hierarchy called {anchorTerm SomeTypes}`Sort`.
{anchorTerm PropType}`Prop` is the same as {anchorTerm sorts}`Sort 0`, {anchorTerm Type0Type}`Type 0` is {anchorTerm sorts}`Sort 1`, {anchorTerm SomeTypes}`Type 1` is {anchorTerm sorts}`Sort 2`, and so forth.
In fact, {anchorTerm sorts}`Type u` is the same as {anchorTerm sorts}`Sort (u+1)`.
When writing programs with Lean, this is typically not relevant, but it may occur in error messages from time to time, and it explains the name of the {anchorName sorts}`CoeSort` class.
Additionally, having {anchorTerm PropType}`Prop` as {anchorTerm sorts}`Sort 0` allows one more universe operator to become useful.
The universe level {lit}`imax u v` is {lit}`0` when {anchorTerm sorts}`v` is {lit}`0`, or the larger of {anchorTerm sorts}`u` or {anchorTerm sorts}`v` otherwise.
Together with {anchorTerm sorts}`Sort`, this allows the special rule for functions that return {anchorTerm PropType}`Prop`s to be used when writing code that should be as portable as possible between {anchorTerm PropType}`Prop` and {anchorTerm SomeTypes}`Type` universes.

# Polymorphism in Practice
%%%
tag := none
%%%

In the remainder of the book, definitions of polymorphic datatypes, structures, and classes will use universe polymorphism in order to be consistent with the Lean standard library.
This will enable the complete presentation of the {moduleName}`Functor`, {anchorName next}`Applicative`, and {anchorName next}`Monad` classes to be completely consistent with their actual definitions.
