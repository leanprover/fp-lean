import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Fin"

#doc (Manual) "Bounded Numbers" =>
%%%
tag := "Fin"
%%%

The {anchorTerm sundries}`GetElem` instance for {anchorName sundries}`Array` and {anchorName sundries}`Nat` requires a proof that the provided {anchorName sundries}`Nat` is smaller than the array.
In practice, these proofs often end up being passed to functions along with the indices.
Rather than passing an index and a proof separately, a type called {anchorName Fin}`Fin` can be used to bundle up the index and the proof into a single value.
This can make code easier to read.

The type {anchorTerm sundries}`Fin n` represents numbers that are strictly less than {anchorName sundries}`n`.
In other words, {anchorTerm sundries}`Fin 3` describes {anchorTerm sundries}`0`, {anchorTerm sundries}`1`, and {anchorTerm sundries}`2`, while {anchorTerm sundries}`Fin 0` has no values at all.
The definition of {anchorName Fin}`Fin` resembles {anchorName sundries}`Subtype`, as a {anchorTerm sundries}`Fin n` is a structure that contains a {anchorName Fin}`Nat` and a proof that it is less than {anchorName sundries}`n`:

```anchor Fin
structure Fin (n : Nat) where
  val  : Nat
  isLt : LT.lt val n
```

Lean includes instances of {anchorName sundries}`ToString` and {anchorName sundries}`OfNat` that allow {anchorName Fin}`Fin` values to be conveniently used as numbers.
In other words, the output of {anchorTerm fiveFinEight}`#eval (5 : Fin 8)` is {anchorInfo fiveFinEight}`5`, rather than something like {lit}`{val := 5, isLt := _}`.

Instead of failing when the provided number is larger than the bound, the {anchorName sundries}`OfNat` instance for {anchorName Fin}`Fin` returns a value modulo the bound.
This means that {anchorTerm finOverflow}`#eval (45 : Fin 10)` results in {anchorInfo finOverflow}`5` rather than a compile-time error.

In a return type, a {anchorName Fin}`Fin` returned as a found index makes its connection to the data structure in which it was found more clear.
The {anchorName ArrayFind}`Array.find` in the {ref "proving-termination"}[previous section] returns an index that the caller cannot immediately use to perform lookups into the array, because the information about its validity has been lost.
A more specific type results in a value that can be used without making the program significantly more complicated:

```anchor ArrayFindHelper
def findHelper (arr : Array α) (p : α → Bool) (i : Nat) :
    Option (Fin arr.size × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (⟨i, h⟩, x)
    else findHelper arr p (i + 1)
  else none
```

```anchor ArrayFind
def Array.find (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) :=
  findHelper arr p 0
```

# Exercise
%%%
tag := "Fin-exercises"
%%%

Write a function {anchorTerm exercise}`Fin.next? : Fin n → Option (Fin n)` that returns the next largest {anchorName nextThreeFin}`Fin` when it would be in bounds, or {anchorName ArrayFindHelper}`none` if not.
Check that
```anchor nextThreeFin
#eval (3 : Fin 8).next?
```
outputs
```anchorInfo nextThreeFin
some 4
```
and that
```anchor nextSevenFin
#eval (7 : Fin 8).next?
```
outputs
```anchorInfo nextSevenFin
none
```
