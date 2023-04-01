# Safe Array Indices

The `GetElem` instance for `Array` and `Nat` requires that the provided `Nat` be smaller than the array.
In practice, these proofs often end up being passed to functions along with the indices.
Rather than passing an index and a proof separately, a type called `Fin` can be used to bundle up the index with the proof.
This can make code easier to read.
Additionally, many of the built-in operations on arrays take their index arguments as `Fin` rather than as `Nat`, so using these built-in operations requires understanding how to use `Fin`.

The type `Fin n` represents numbers that are strictly less than `n`.
In other words, `Fin 3` represents `0`, `1`, and `2`, while `Fin 0` has no values at all.
