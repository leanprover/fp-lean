import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Fin"

#doc (Manual) "Safe Array Indices" =>

The `GetElem` instance for `Array` and `Nat` requires a proof that the provided `Nat` is smaller than the array.
In practice, these proofs often end up being passed to functions along with the indices.
Rather than passing an index and a proof separately, a type called `Fin` can be used to bundle up the index and the proof into a single value.
This can make code easier to read.
Additionally, many of the built-in operations on arrays take their index arguments as `Fin` rather than as `Nat`, so using these built-in operations requires understanding how to use `Fin`.

The type `Fin n` represents numbers that are strictly less than `n`.
In other words, `Fin 3` describes `0`, `1`, and `2`, while `Fin 0` has no values at all.
The definition of `Fin` resembles `Subtype`, as a `Fin n` is a structure that contains a `Nat` and a proof that it is less than `n`:

```anchor Fin
structure Fin (n : Nat) where
  val  : Nat
  isLt : LT.lt val n
```

Lean includes instances of `ToString` and `OfNat` that allow `Fin` values to be conveniently used as numbers.
In other words, the output of {anchorTerm fiveFinEight}`#eval (5 : Fin 8)` is {anchorInfo fiveFinEight}`5`, rather than something like `{val := 5, isLt := _}`.

Instead of failing when the provided number is larger than the bound, the `OfNat` instance for `Fin` returns a value modulo the bound.
This means that {anchorTerm finOverflow}`#eval (45 : Fin 10)` results in {anchorInfo finOverflow}`5` rather than a compile-time error.

In a return type, a `Fin` returned as a found index makes its connection to the data structure in which it was found more clear.
The `Array.find` in the [previous section](./arrays-termination.md#proving-termination) returns an index that the caller cannot immediately use to perform lookups into the array, because the information about its validity has been lost.
A more specific type results in a value that can be used without making the program significantly more complicated:

```anchor ArrayFindHelper
def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Fin arr.size × α) :=
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

Write a function `Fin.next? : Fin n → Option (Fin n)` that returns the next largest `Fin` when it would be in bounds, or `none` if not.
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
