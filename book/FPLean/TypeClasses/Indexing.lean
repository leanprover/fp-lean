import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Classes"

set_option pp.rawOnError true

#doc (Manual) "Arrays and Indexing" =>


The {ref "props-proofs-indexing"}[Interlude] describes how to use indexing notation in order to look up entries in a list by their position.
This syntax is also governed by a type class, and it can be used for a variety of different types.

# Arrays
%%%
tag := "array-indexing"
%%%

For instance, Lean arrays are much more efficient than linked lists for most purposes.
In Lean, the type {anchorTerm arrVsList}`Array α` is a dynamically-sized array holding values of type {anchorName arrVsList}`α`, much like a Java {java}`ArrayList`, a C++ {cpp}`std::vector`, or a Rust {rust}`Vec`.
Unlike {anchorTerm arrVsList}`List`, which has a pointer indirection on each use of the {anchorName arrVsList}`cons` constructor, arrays occupy a contiguous region of memory, which is much better for processor caches.
Also, looking up a value in an array takes constant time, while lookup in a linked list takes time proportional to the index being accessed.

In pure functional languages like Lean, it is not possible to mutate a given position in a data structure.
Instead, a copy is made that has the desired modifications.
However, copying is not always necessary: the Lean compiler and runtime contain an optimization that can allow modifications to be implemented as mutations behind the scenes when there is only a single unique reference to an array.

Arrays are written similarly to lists, but with a leading {lit}`#`:

```anchor northernTrees
def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]
```
The number of values in an array can be found using {anchorName arrVsList}`Array.size`.
For instance, {anchorTerm northernTreesSize}`northernTrees.size` evaluates to {anchorTerm northernTreesSize}`4`.
For indices that are smaller than an array's size, indexing notation can be used to find the corresponding value, just as with lists.
That is, {anchorTerm northernTreesTwo}`northernTrees[2]` evaluates to {anchorTerm northernTreesTwo}`"elm"`.
Similarly, the compiler requires a proof that an index is in bounds, and attempting to look up a value outside the bounds of the array results in a compile-time error, just as with lists.
For instance, {anchorTerm northernTreesEight}`northernTrees[8]` results in:
```anchorError northernTreesEight
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ 8 < northernTrees.size
```

# Non-Empty Lists
%%%
tag := "non-empty-list-indexing"
%%%

A datatype that represents non-empty lists can be defined as a structure with a field for the head of the list and a field for the tail, which is an ordinary, potentially empty list:

```anchor NonEmptyList
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
```
For example, the non-empty list {moduleName}`idahoSpiders` (which contains some spider species native to the US state of Idaho) consists of {anchorTerm firstSpider}`"Banded Garden Spider"` followed by four other spiders, for a total of five spiders:

```anchor idahoSpiders
def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}
```

Looking up the value at a specific index in this list with a recursive function should consider three possibilities:
 1. The index is {anchorTerm NEListGetHuh}`0`, in which case the head of the list should be returned.
 2. The index is {anchorTerm NEListGetHuh}`n + 1` and the tail is empty, in which case the index is out of bounds.
 3. The index is {anchorTerm NEListGetHuh}`n + 1` and the tail is non-empty, in which case the function can be called recursively on the tail and {anchorTerm NEListGetHuh}`n`.

For example, a lookup function that returns an {moduleName}`Option` can be written as follows:

```anchor NEListGetHuh
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n
```
Each case in the pattern match corresponds to one of the possibilities above.
The recursive call to {anchorName NEListGetHuh}`get?` does not require a {moduleName}`NonEmptyList` namespace qualifier because the body of the definition is implicitly in the definition's namespace.
Another way to write this function uses a list lookup {anchorTerm NEListGetHuhList}`xs.tail[n]?` when the index is greater than zero:

```anchor NEListGetHuhList
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail[n]?
```

If the list contains one entry, then only {anchorTerm nats}`0` is a valid index.
If it contains two entries, then both {anchorTerm nats}`0` and {anchorTerm nats}`1` are valid indices.
If it contains three entries, then {anchorTerm nats}`0`, {anchorTerm nats}`1`, and {anchorTerm nats}`2` are valid indices.
In other words, the valid indices into a non-empty list are natural numbers that are strictly less than the length of the list, which are less than or equal to the length of the tail.

The definition of what it means for an index to be in bounds should be written as an {kw}`abbrev` because the tactics used to find evidence that indices are acceptable are able to solve inequalities of numbers, but they don't know anything about the name {moduleName}`NonEmptyList.inBounds`:

```anchor inBoundsNEList
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length
```
This function returns a proposition that might be true or false.
For instance, {anchorTerm spiderBoundsChecks}`2` is in bounds for {moduleName}`idahoSpiders`, while {anchorTerm spiderBoundsChecks}`5` is not:

```anchor spiderBoundsChecks
theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by decide

theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by decide
```
The logical negation operator has a very low precedence, which means that {anchorTerm spiderBoundsChecks}`¬idahoSpiders.inBounds 5` is equivalent to {anchorTerm spiderBoundsChecks'}`¬(idahoSpiders.inBounds 5)`.


This fact can be used to write a lookup function that requires evidence that the index is valid, and thus need not return {moduleName}`Option`, by delegating to the version for lists that checks the evidence at compile time:

```anchor NEListGet
def NonEmptyList.get (xs : NonEmptyList α)
    (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]
```
It is, of course, possible to write this function to use the evidence directly, rather than delegating to a standard library function that happens to be able to use the same evidence.
This requires techniques for working with proofs and propositions that are described later in this book.


# Overloading Indexing
%%%
tag := "overloading-indexing"
%%%

Indexing notation for a collection type can be overloaded by defining an instance of the {anchorName GetElem}`GetElem` type class.
For the sake of flexibility, {anchorName GetElem}`GetElem` has four parameters:
 * The type of the collection
 * The type of the index
 * The type of elements that are extracted from the collection
 * A function that determines what counts as evidence that the index is in bounds

The element type and the evidence function are both output parameters.
{anchorName GetElem}`GetElem` has a single method, {anchorName GetElem}`getElem`, which takes a collection value, an index value, and evidence that the index is in bounds as arguments, and returns an element:

```anchor GetElem
class GetElem
    (coll : Type)
    (idx : Type)
    (item : outParam Type)
    (inBounds : outParam (coll → idx → Prop)) where
  getElem : (c : coll) → (i : idx) → inBounds c i → item
```

In the case of {anchorTerm GetElemNEList}`NonEmptyList α`, these parameters are:
 * The collection is {anchorTerm GetElemNEList}`NonEmptyList α`
 * Indices have type {anchorName GetElemNEList}`Nat`
 * The type of elements is {anchorName GetElemNEList}`α`
 * An index is in bounds if it is less than or equal to the length of the tail

In fact, the {anchorTerm GetElemNEList}`GetElem` instance can delegate directly to {anchorTerm GetElemNEList}`NonEmptyList.get`:

```anchor GetElemNEList
instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get
```
With this instance, {anchorTerm GetElemNEList}`NonEmptyList` becomes just as convenient to use as {moduleName}`List`.
Evaluating {anchorTerm firstSpider}`idahoSpiders.head` yields {anchorTerm firstSpider}`"Banded Garden Spider"`, while {anchorTerm tenthSpider}`idahoSpiders[9]` leads to the compile-time error:
```anchorError tenthSpider
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ idahoSpiders.inBounds 9
```

Because both the collection type and the index type are input parameters to the {anchorTerm ListPosElem}`GetElem` type class, new types can be used to index into existing collections.
The positive number type {anchorTerm ListPosElem}`Pos` is a perfectly reasonable index into a {anchorTerm ListPosElem}`List`, with the caveat that it cannot point at the first entry.
The following instance of {anchorTerm ListPosElem}`GetElem` allows {anchorTerm ListPosElem}`Pos` to be used just as conveniently as {moduleName}`Nat` to find a list entry:

```anchor ListPosElem
instance : GetElem (List α) Pos α
    (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]
```

Indexing can also make sense for non-numeric indices.
For example, {moduleName}`Bool` can be used to select between the fields in a point, with {moduleName}`false` corresponding to {anchorTerm PPointBoolGetElem}`x` and {moduleName}`true` corresponding to {anchorTerm PPointBoolGetElem}`y`:

```anchor PPointBoolGetElem
instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y
```
In this case, both Booleans are valid indices.
Because every possible {moduleName}`Bool` is in bounds, the evidence is simply the true proposition {moduleName}`True`.
