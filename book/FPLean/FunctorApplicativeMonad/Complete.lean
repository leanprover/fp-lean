import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.FunctorApplicativeMonad.ActualDefs"

#doc (Manual) "The Complete Definitions" =>
%%%
tag := "complete-definitions"
%%%

Now that all the relevant language features have been presented, this section describes the complete, honest definitions of {anchorName HonestFunctor}`Functor`, {anchorName Applicative}`Applicative`, and {anchorName Monad}`Monad` as they occur in the Lean standard library.
For the sake of understanding, no details are omitted.

# Functor
%%%
tag := "complete-functor-definition"
%%%


The complete definition of the {anchorName Applicative}`Functor` class makes use of universe polymorphism and a default method implementation:

```anchor HonestFunctor
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α :=
    Function.comp map (Function.const _)
```
In this definition, {anchorName HonestFunctor}`Function.comp` is function composition, which is typically written with the {lit}`∘` operator.
{anchorName HonestFunctor}`Function.const` is the _constant function_, which is a two-argument function that ignores its second argument.
Applying this function to only one argument produces a function that always returns the same value, which is useful when an API demands a function but a program doesn't need to compute different results for different arguments.
A simple version of {anchorName HonestFunctor}`Function.const` can be written as follows:

```anchor simpleConst
def simpleConst  (x : α) (_ : β) : α := x
```
Using it with one argument as the function argument to {anchorTerm extras}`List.map` demonstrates its utility:
```anchor mapConst
#eval [1, 2, 3].map (simpleConst "same")
```
```anchorInfo mapConst
["same", "same", "same"]
```
The actual function has the following signature:
```anchorInfo FunctionConstType
Function.const.{u, v} {α : Sort u} (β : Sort v) (a : α) : β → α
```
Here, the type argument {anchorName HonestFunctor}`β` is an explicit argument, so the default definition of {anchorName HonestFunctor}`mapConst` provides an {anchorTerm HonestFunctor}`_` argument that instructs Lean to find a unique type to pass to {anchorName HonestFunctor}`Function.const` that would cause the program to type check.
{anchorTerm unfoldCompConst}`Function.comp map (Function.const _)` is equivalent to {anchorTerm unfoldCompConst}`fun (x : α) (y : f β) => map (fun _ => x) y`.

The {anchorName HonestFunctor}`Functor` type class inhabits a universe that is the greater of {anchorTerm HonestFunctor}`u+1` and {anchorTerm HonestFunctor}`v`.
Here, {anchorTerm HonestFunctor}`u` is the level of universes accepted as arguments to {anchorName HonestFunctor}`f`, while {anchorTerm HonestFunctor}`v` is the universe returned by {anchorName HonestFunctor}`f`.
To see why the structure that implements the {anchorName HonestFunctor}`Functor` type class must be in a universe that's larger than {anchorTerm HonestFunctor}`u`, begin with a simplified definition of the class:

```anchor FunctorSimplified
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
```
This type class's structure type is equivalent to the following inductive type:

```anchor FunctorDatatype
inductive Functor (f : Type u → Type v) : Type (max (u+1) v) where
  | mk : ({α β : Type u} → (α → β) → f α → f β) → Functor f
```
The implementation of the {lit}`map` method that is passed as an argument to {anchorName FunctorDatatype}`mk` contains a function that takes two types in {anchorTerm FunctorDatatype}`Type u` as arguments.
This means that the type of the function itself is in {lit}`Type (u+1)`, so {anchorName FunctorDatatype}`Functor` must also be at a level that is at least {anchorTerm FunctorDatatype}`u+1`.
Similarly, other arguments to the function have a type built by applying {anchorName FunctorDatatype}`f`, so it must also have a level that is at least {anchorTerm FunctorDatatype}`v`.
All the type classes in this section share this property.

# Applicative
%%%
tag := "complete-applicative-definition"
%%%

The {anchorName Applicative}`Applicative` type class is actually built from a number of smaller classes that each contain some of the relevant methods.
The first are {anchorName Applicative}`Pure` and {anchorName Applicative}`Seq`, which contain {anchorName Applicative}`pure` and {anchorName Seq}`seq` respectively:

```anchor Pure
class Pure (f : Type u → Type v) : Type (max (u+1) v) where
  pure {α : Type u} : α → f α
```

```anchor Seq
class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
```

In addition to these, {anchorName Applicative}`Applicative` also depends on {anchorName SeqRight}`SeqRight` and an analogous {anchorName SeqLeft}`SeqLeft` class:

```anchor SeqRight
class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β
```

```anchor SeqLeft
class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α
```

The {anchorName SeqRight}`seqRight` function, which was introduced in the {ref "alternative"}[section about alternatives and validation], is easiest to understand from the perspective of effects.
{anchorTerm seqRightSugar (module := Examples.FunctorApplicativeMonad)}`E1 *> E2`, which desugars to {anchorTerm seqRightSugar (module := Examples.FunctorApplicativeMonad)}`SeqRight.seqRight E1 (fun () => E2)`, can be understood as first executing {anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E1`, and then {anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E2`, resulting only in {anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E2`'s result.
Effects from {anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E1` may result in {anchorName seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E2` not being run, or being run multiple times.
Indeed, if {anchorName SeqRight}`f` has a {anchorName Monad}`Monad` instance, then {anchorTerm seqRightSugar (module:=Examples.FunctorApplicativeMonad)}`E1 *> E2` is equivalent to {lit}`do let _ ← E1; E2`, but {anchorName SeqRight}`seqRight` can be used with types like {anchorName Validate (module:=Examples.FunctorApplicativeMonad)}`Validate` that are not monads.

Its cousin {anchorName SeqLeft}`seqLeft` is very similar, except the leftmost expression's value is returned.
{anchorTerm seqLeftSugar}`E1 <* E2` desugars to {anchorTerm seqLeftSugar}`SeqLeft.seqLeft E1 (fun () => E2)`.
{anchorTerm seqLeftType}`SeqLeft.seqLeft` has type {anchorTerm seqLeftType}`f α → (Unit → f β) → f α`, which is identical to that of {anchorName SeqRight}`seqRight` except for the fact that it returns {anchorTerm SeqLeft}`f α`.
{anchorTerm seqLeftSugar}`E1 <* E2` can be understood as a program that first executes {anchorName seqLeftSugar}`E1`, and then {anchorName seqLeftSugar}`E2`, returning the original result for {anchorName seqLeftSugar}`E1`.
If {anchorName SeqLeft}`f` has a {anchorName Monad}`Monad` instance, then {anchorTerm seqLeftSugar}`E1 <* E2` is equivalent to {lit}`do let x ← E1; _ ← E2; pure x`.
Generally speaking, {anchorName SeqLeft}`seqLeft` is useful for specifying extra conditions on a value in a validation or parser-like workflow without changing the value itself.

The definition of {anchorName Applicative}`Applicative` extends all these classes, along with {anchorName Applicative}`Functor`:

```anchor Applicative
class Applicative (f : Type u → Type v)
    extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
```
A complete definition of {anchorName Applicative}`Applicative` requires only definitions for {anchorName Applicative}`pure` and {anchorName Seq}`seq`.
This is because there are default definitions for all of the methods from {anchorName Applicative}`Functor`, {anchorName SeqLeft}`SeqLeft`, and {anchorName SeqRight}`SeqRight`.
The {anchorName HonestFunctor}`mapConst` method of {anchorName HonestFunctor}`Functor` has its own default implementation in terms of {anchorName Applicative}`Functor.map`.
These default implementations should only be overridden with new functions that are behaviorally equivalent, but more efficient.
The default implementations should be seen as specifications for correctness as well as automatically-created code.

The default implementation for {anchorName SeqLeft}`seqLeft` is very compact.
Replacing some of the names with their syntactic sugar or their definitions can provide another view on it, so:
```anchorTerm unfoldMapConstSeqLeft
Seq.seq (Functor.map (Function.const _) a) b
```
becomes
```anchorTerm unfoldMapConstSeqLeft
fun a b => Seq.seq ((fun x _ => x) <$> a) b
```
How should {anchorTerm unfoldMapConstSeqLeft}`(fun x _ => x) <$> a` be understood?
Here, {anchorName unfoldMapConstSeqLeft}`a` has type {anchorTerm unfoldMapConstSeqLeft}`f α`, and {anchorName unfoldMapConstSeqLeft}`f` is a functor.
If {anchorName unfoldMapConstSeqLeft}`f` is {anchorName extras}`List`, then {anchorTerm mapConstList}`(fun x _ => x) <$> [1, 2, 3]` evaluates to {anchorTerm mapConstList}`[fun _ => 1, fun _ => 2, fun _ => 3`.
If {anchorName unfoldMapConstSeqLeft}`f` is {anchorName mapConstOption}`Option`, then {anchorTerm mapConstOption}`(fun x _ => x) <$> some "hello"` evaluates to {anchorTerm mapConstOption}`some (fun _ => "hello")`.
In each case, the values in the functor are replaced by functions that return the original value, ignoring their argument.
When combined with {anchorName Seq}`seq`, this function discards the values from {anchorName Seq}`seq`'s second argument.

The default implementation for {anchorName SeqRight}`seqRight` is very similar, except {anchorName FunctionConstType}`Function.const` has an additional argument {anchorName Applicative}`id`.
This definition can be understood similarly, by first introducing some standard syntactic sugar and then replacing some names with their definitions:
```anchorEvalSteps unfoldMapConstSeqRight
fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
===>
fun a b => Seq.seq ((fun _ => id) <$> a) b
===>
fun a b => Seq.seq ((fun _ => fun x => x) <$> a) b
===>
fun a b => Seq.seq ((fun _ x => x) <$> a) b
```
How should {anchorTerm unfoldMapConstSeqRight}`(fun _ x => x) <$> a` be understood?
Once again, examples are useful.
{anchorTerm mapConstIdList}`fun _ x => x) <$> [1, 2, 3]` is equivalent to {anchorTerm mapConstIdList}`[fun x => x, fun x => x, fun x => x]`, and {anchorTerm mapConstIdOption}`(fun _ x => x) <$> some "hello"` is equivalent to {anchorTerm mapConstIdOption}`some (fun x => x)`.
In other words, {anchorTerm unfoldMapConstSeqRight}`(fun _ x => x) <$> a` preserves the overall shape of {anchorName unfoldMapConstSeqRight}`a`, but each value is replaced by the identity function.
From the perspective of effects, the side effects of {anchorName unfoldMapConstSeqRight}`a` occur, but the values are thrown out when it is used with {anchorName Seq}`seq`.

# Monad
%%%
tag := "complete-monad-definition"
%%%

Just as the constituent operations of {anchorName Applicative}`Applicative` are split into their own type classes, {anchorName Bind}`Bind` has its own class as well:

```anchor Bind
class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β
```
{anchorName Monad}`Monad` extends {anchorName Applicative}`Applicative` with {anchorName Bind}`Bind`:

```anchor Monad
class Monad (m : Type u → Type v) : Type (max (u+1) v)
    extends Applicative m, Bind m where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()
```
Tracing the collection of inherited methods and default methods from the entire hierarchy shows that a {anchorName Monad}`Monad` instance requires only implementations of {anchorName Bind}`bind` and {anchorName Pure}`pure`.
In other words, {anchorName Monad}`Monad` instances automatically yield implementations of {anchorName Seq}`seq`, {anchorName SeqLeft}`seqLeft`, {anchorName SeqRight}`seqRight`, {anchorName HonestFunctor}`map`, and {anchorName HonestFunctor}`mapConst`.
From the perspective of API boundaries, any type with a {anchorName Monad}`Monad` instance gets instances for {anchorName Bind}`Bind`, {anchorName Pure}`Pure`, {anchorName Seq}`Seq`, {anchorName Applicative}`Functor`, {anchorName SeqLeft}`SeqLeft`, and {anchorName SeqRight}`SeqRight`.


# Exercises
%%%
tag := "complete-functor-applicative-monad-exercises"
%%%

 1. Understand the default implementations of {anchorName HonestFunctor}`map`, {anchorName Seq}`seq`, {anchorName SeqLeft}`seqLeft`, and {anchorName SeqRight}`seqRight` in {anchorName Monad}`Monad` by working through examples such as {anchorName mapConstOption}`Option` and {anchorName ApplicativeExcept (module:=Examples.FunctorApplicativeMonad)}`Except`. In other words, substitute their definitions for {anchorName Bind}`bind` and {anchorName Pure}`pure` into the default definitions, and simplify them to recover the versions {anchorName HonestFunctor}`map`, {anchorName Seq}`seq`, {anchorName SeqLeft}`seqLeft`, and {anchorName SeqRight}`seqRight` that would be written by hand.
 2. On paper or in a text file, prove to yourself that the default implementations of {anchorName HonestFunctor}`map` and {anchorName Seq}`seq` satisfy the contracts for {anchorName Applicative}`Functor` and {anchorName Applicative}`Applicative`. In this argument, you're allowed to use the rules from the {anchorName Monad}`Monad` contract as well as ordinary expression evaluation.
