import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.Class"

#doc (Manual) "The Monad Type Class" =>
%%%
tag := "monad-type-class"
%%%

:::paragraph
Rather than having to import an operator like {lit}`ok` or {lit}`andThen` for each type that is a monad, the Lean standard library contains a type class that allow them to be overloaded, so that the same operators can be used for _any_ monad.
Monads have two operations, which are the equivalent of {lit}`ok` and {lit}`andThen`:

```anchor FakeMonad
class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β
```
This definition is slightly simplified.
The actual definition in the Lean library is somewhat more involved, and will be presented later.
:::

:::paragraph
The {anchorName MonadOptionExcept}`Monad` instances for {anchorName MonadOptionExcept}`Option` and {anchorTerm MonadOptionExcept}`Except ε` can be created by adapting the definitions of their respective {lit}`andThen` operations:

```anchor MonadOptionExcept
instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt with
    | Except.error e => Except.error e
    | Except.ok x => next x
```
:::

:::paragraph
As an example, {lit}`firstThirdFifthSeventh` was defined separately for {anchorTerm Names}`Option α` and {anchorTerm Names}`Except String α` return types.
Now, it can be defined polymorphically for _any_ monad.
It does, however, require a lookup function as an argument, because different monads might fail to find a result in different ways.
The infix version of {anchorName FakeMonad}`bind` is {lit}`>>=`, which plays the same role as {lit}`~~>` in the examples.

```anchor firstThirdFifthSeventhMonad
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)
```
:::

:::paragraph
Given example lists of slow mammals and fast birds, this implementation of {anchorName firstThirdFifthSeventhMonad}`firstThirdFifthSeventh` can be used with {moduleName}`Option`:

```anchor animals
def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]

def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]
```
```anchor noneSlow
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals
```
```anchorInfo noneSlow
none
```
```anchor someFast
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds
```
```anchorInfo someFast
some ("Peregrine falcon", "Golden eagle", "Spur-winged goose", "Anna's hummingbird")
```
:::

:::paragraph
After renaming {anchorName getOrExcept}`Except`'s lookup function {lit}`get` to something more specific, the very same implementation of {anchorName firstThirdFifthSeventhMonad}`firstThirdFifthSeventh` can be used with {anchorName getOrExcept}`Except` as well:

```anchor getOrExcept
def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none =>
    Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x =>
    Except.ok x
```
```anchor errorSlow
#eval firstThirdFifthSeventh getOrExcept slowMammals
```
```anchorInfo errorSlow
Except.error "Index 2 not found (maximum is 1)"
```
```anchor okFast
#eval firstThirdFifthSeventh getOrExcept fastBirds
```
```anchorInfo okFast
Except.ok ("Peregrine falcon", "Golden eagle", "Spur-winged goose", "Anna's hummingbird")
```
The fact that {anchorName firstThirdFifthSeventhMonad}`m` must have a {anchorName firstThirdFifthSeventhMonad}`Monad` instance means that the {lit}`>>=` and {anchorName firstThirdFifthSeventhMonad}`pure` operations are available.
:::

# General Monad Operations
%%%
tag := "monad-class-polymorphism"
%%%

:::paragraph
Because many different types are monads, functions that are polymorphic over _any_ monad are very powerful.
For example, the function {anchorName mapM}`mapM` is a version of {anchorName Names (show:=map)}`Functor.map` that uses a {anchorName mapM}`Monad` to sequence and combine the results of applying a function:

```anchor mapM
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)
```
The return type of the function argument {anchorName mapM}`f` determines which {anchorName mapM}`Monad` instance will be used.
In other words, {anchorName mapM}`mapM` can be used for functions that produce logs, for functions that can fail, or for functions that use mutable state.
Because {anchorName mapM}`f`'s type determines the available effects, they can be tightly controlled by API designers.
:::

:::paragraph
As described in {ref "numbering-tree-nodes"}[this chapter's introduction], {anchorTerm StateEx}`State σ α` represents programs that make use of a mutable variable of type {anchorName StateEx}`σ` and return a value of type {anchorName StateEx}`α`.
These programs are actually functions from a starting state to a pair of a value and a final state.
The {anchorName StateMonad}`Monad` class requires that its parameter expect a single type argument—that is, it should be a {anchorTerm StateEx}`Type → Type`.
This means that the instance for {anchorName StateMonad}`State` should mention the state type {anchorName StateMonad}`σ`, which becomes a parameter to the instance:

```anchor StateMonad
instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'
```
This means that the type of the state cannot change between calls to {anchorName StateEx}`get` and {anchorName StateEx}`set` that are sequenced using {anchorName StateMonad}`bind`, which is a reasonable rule for stateful computations.
The operator {anchorName increment}`increment` increases a saved state by a given amount, returning the old value:

```anchor increment
def increment (howMuch : Int) : State Int Int :=
  get >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i
```
:::

:::paragraph
Using {anchorName mapMincrementOut}`mapM` with {anchorName mapMincrementOut}`increment` results in a program that computes the sum of the entries in a list.
More specifically, the mutable variable contains the sum so far, while the resulting list contains a running sum.
In other words, {anchorTerm mapMincrement}`mapM increment` has type {anchorTerm mapMincrement}`List Int → State Int (List Int)`, and expanding the definition of {anchorName StateMonad}`State` yields {anchorTerm mapMincrement2}`List Int → Int → (Int × List Int)`.
It takes an initial sum as an argument, which should be {anchorTerm mapMincrementOut}`0`:
```anchor mapMincrementOut
#eval mapM increment [1, 2, 3, 4, 5] 0
```
```anchorInfo mapMincrementOut
(15, [0, 1, 3, 6, 10])
```
:::

:::paragraph
A {ref "logging"}[logging effect] can be represented using {anchorName MonadWriter}`WithLog`.
Just like {anchorName StateEx}`State`, its {anchorName MonadWriter}`Monad` instance is polymorphic with respect to the type of the logged data:

```anchor MonadWriter
instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
```
:::

:::paragraph
{anchorName saveIfEven}`saveIfEven` is a function that logs even numbers but returns its argument unchanged:

```anchor saveIfEven
def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then
    save i
   else pure ()) >>= fun () =>
  pure i
```
Using this function with {anchorName mapMsaveIfEven}`mapM` results in a log containing even numbers paired with an unchanged input list:
```anchor mapMsaveIfEven
#eval mapM saveIfEven [1, 2, 3, 4, 5]
```
```anchorInfo mapMsaveIfEven
{ log := [2, 4], val := [1, 2, 3, 4, 5] }
```
:::


# The Identity Monad
%%%
tag := "Id-monad"
%%%

Monads encode programs with effects, such as failure, exceptions, or logging, into explicit representations as data and functions.
Sometimes, however, an API will be written to use a monad for flexibility, but the API's client may not require any encoded effects.
The {deftech}_identity monad_ is a monad that has no effects.
It allows pure code to be used with monadic APIs:

```anchor IdMonad
def Id (t : Type) : Type := t

instance : Monad Id where
  pure x := x
  bind x f := f x
```
The type of {anchorName IdMonad}`pure` should be {anchorTerm IdMore}`α → Id α`, but {anchorTerm IdMore}`Id α` reduces to just {anchorTerm IdMore}`α`.
Similarly, the type of {anchorName IdMonad}`bind` should be {anchorTerm IdMore}`α → (α → Id β) → Id β`.
Because this reduces to {anchorTerm IdMore}`α → (α → β) → β`, the second argument can be applied to the first to find the result.

:::paragraph
With the identity monad, {anchorName mapMId}`mapM` becomes equivalent to {anchorName Names (show:=map)}`Functor.map`
To call it this way, however, Lean requires a hint that the intended monad is {anchorName mapMId}`Id`:
```anchor mapMId
#eval mapM (m := Id) (· + 1) [1, 2, 3, 4, 5]
```
```anchorInfo mapMId
[2, 3, 4, 5, 6]
```
Omitting the hint results in an error:
```anchor mapMIdNoHint
#eval mapM (· + 1) [1, 2, 3, 4, 5]
```
```anchorError mapMIdNoHint
failed to synthesize
  HAdd Nat Nat (?m.4 ?m.3)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
```
In this error, the application of one metavariable to another indicates that Lean doesn't run the type-level computation backwards.
The return type of the function is expected to be the monad applied to some other type.
Similarly, using {anchorName mapMIdId}`mapM` with a function whose type doesn't provide any specific hints about which monad is to be used results in an “instance problem is stuck” message:
```anchor mapMIdId
#eval mapM (fun (x : Nat) => x) [1, 2, 3, 4, 5]
```
```anchorError mapMIdId
typeclass instance problem is stuck, it is often due to metavariables
  Monad ?m.22785
```
:::

# The Monad Contract
%%%
tag := "monad-contract"
%%%

Just as every pair of instances of {anchorName MonadContract}`BEq` and {anchorName MonadContract}`Hashable` should ensure that any two equal values have the same hash, there is a contract that each instance of {anchorName MonadContract}`Monad` should obey.
First, {anchorName MonadContract}`pure` should be a left identity of {anchorName MonadContract}`bind`.
That is, {anchorTerm MonadContract}`bind (pure v) f` should be the same as {anchorTerm MonadContract}`f v`.
Secondly, {anchorName MonadContract}`pure` should be a right identity of {anchorName MonadContract}`bind`, so {anchorTerm MonadContract}`bind v pure` is the same as {anchorName MonadContract2}`v`.
Finally, {anchorName MonadContract}`bind` should be associative, so {anchorTerm MonadContract}`bind (bind v f) g` is the same as {anchorTerm MonadContract}`bind v (fun x => bind (f x) g)`.

This contract specifies the expected properties of programs with effects more generally.
Because {anchorName MonadContract}`pure` has no effects, sequencing its effects with {anchorName MonadContract}`bind` shouldn't change the result.
The associative property of {anchorName MonadContract}`bind` basically says that the sequencing bookkeeping itself doesn't matter, so long as the order in which things are happening is preserved.

# Exercises
%%%
tag := "monad-class-exercises"
%%%

## Mapping on a Tree
%%%
tag := none
%%%

:::paragraph
Define a function {anchorName ex1}`BinTree.mapM`.
By analogy to {anchorName mapM}`mapM` for lists, this function should apply a monadic function to each data entry in a tree, as a preorder traversal.
The type signature should be:
```anchorTerm ex1
def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
```
:::

## The Option Monad Contract
%%%
tag := none
%%%

:::paragraph
First, write a convincing argument that the {anchorName badOptionMonad}`Monad` instance for {anchorName badOptionMonad}`Option` satisfies the monad contract.
Then, consider the following instance:
```anchor badOptionMonad
instance : Monad Option where
  pure x := some x
  bind opt next := none
```
Both methods have the correct type.
Why does this instance violate the monad contract?
:::
