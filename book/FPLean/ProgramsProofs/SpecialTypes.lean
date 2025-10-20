import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.SpecialTypes"

#doc (Manual) "Special Types" =>
%%%
tag := "runtime-special-types"
%%%

Understanding the representation of data in memory is very important.
Usually, the representation can be understood from the definition of a datatype.
Each constructor corresponds to an object in memory that has a header that includes a tag and a reference count.
The constructor's arguments are each represented by a pointer to some other object.
In other words, {anchorName all}`List` really is a linked list and extracting a field from a {kw}`structure` really does just chase a pointer.

There are, however, some important exceptions to this rule.
A number of types are treated specially by the compiler.
For example, the type {anchorName all}`UInt32` is defined as {anchorTerm all}`Fin (2 ^ 32)`, but it is replaced at run-time with an actual native implementation based on machine words.
Similarly, even though the definition of {anchorName all}`Nat` suggests an implementation similar to {anchorTerm all}`List Unit`, the actual run-time representation uses immediate machine words for sufficiently-small numbers and an efficient arbitrary-precision arithmetic library for larger numbers.
The Lean compiler translates from definitions that use pattern matching into the appropriate operations for this representation, and calls to operations like addition and subtraction are mapped to fast operations from the underlying arithmetic library.
After all, addition should not take time linear in the size of the addends.

The fact that some types have special representations also means that care is needed when working with them.
Most of these types consist of a {kw}`structure` that is treated specially by the compiler.
With these structures, using the constructor or the field accessors directly can trigger an expensive conversion from an efficient representation to a slow one that is convenient for proofs.
For example, {anchorName all}`String` is defined as a structure that contains a list of characters, but the run-time representation of strings uses UTF-8, not linked lists of pointers to characters.
Applying the constructor to a list of characters creates a byte array that encodes them in UTF-8, and accessing the field of the structure takes time linear in the length of the string to decode the UTF-8 representation and allocate a linked list.
Arrays are represented similarly.
From the logical perspective, arrays are structures that contain a list of array elements, but the run-time representation is a dynamically-sized array.
At run time, the constructor translates the list into an array, and the field accessor allocates a linked list from the array.
The various array operations are replaced with efficient versions by the compiler that mutate the array when possible instead of allocating a new one.

Both types themselves and proofs of propositions are completely erased from compiled code.
In other words, they take up no space, and any computations that might have been performed as part of a proof are similarly erased.
This means that proofs can take advantage of the convenient interface to strings and arrays as inductively-defined lists, including using induction to prove things about them, without imposing slow conversion steps while the program is running.
For these built-in types, a convenient logical representation of the data does not imply that the program must be slow.

If a structure type has only a single non-type non-proof field, then the constructor itself disappears at run time, being replaced with its single argument.
In other words, a subtype is represented identically to its underlying type, rather than with an extra layer of indirection.
Similarly, {anchorName all}`Fin` is just {anchorName all}`Nat` in memory, and single-field structures can be created to keep track of different uses of {anchorName all}`Nat`s or {anchorName all}`String`s without paying a performance penalty.
If a constructor has no non-type non-proof arguments, then the constructor also disappears and is replaced with a constant value where the pointer would otherwise be used.
This means that {anchorName all}`true`, {anchorName all}`false`, and {anchorName all}`none` are constant values, rather than pointers to heap-allocated objects.


The following types have special representations:

:::table +header
*
  * Type
  * Logical representation
  * Run-time Representation

*
  * {anchorName all}`Nat`
  * Unary, with one pointer from each {anchorTerm all}`Nat.succ`
  * Efficient arbitrary-precision integers

*
  * {anchorName all}`Int`
  * A sum type with constructors for positive or negative values, each containing a {anchorName all}`Nat`
  * Efficient arbitrary-precision integers

*
  * {anchorTerm all}`BitVec w`
  * A {anchorName all}`Fin` with an appropriate bound $`2^w`
  * Efficient arbitrary-precision integers

*
  * {anchorName all}`UInt8`, {anchorName all}`UInt16`, {anchorName all}`UInt32`, {anchorName all}`UInt64`, {anchorName all}`USize`
  * A bitvector of the correct width
  * Fixed-precision machine integers

*
  * {anchorName all}`Int8`, {anchorName all}`Int16`, {anchorName all}`Int32`, {anchorName all}`Int64`, {anchorName all}`ISize`
  * A wrapped unsigned integer of the same width
  * Fixed-precision machine integers

*
  * {anchorName all}`Char`
  * A {anchorName all}`UInt32` paired with a proof that it's a valid code point
  * Ordinary characters

*
  * {anchorName all}`String`
  * A structure that contains a {anchorTerm all}`List Char` in a field called {anchorTerm StringDetail}`data`
  * UTF-8-encoded string

*
  * {anchorTerm sequences}`Array α`
  * A structure that contains a {anchorTerm sequences}`List α` in a field called {anchorName sequences}`toList`
  * Packed arrays of pointers to {anchorName sequences}`α` values

*
  * {anchorTerm all}`Sort u`
  * A type
  * Erased completely

*
  * Proofs of propositions
  * Whatever data is suggested by the proposition when considered as a type of evidence
  * Erased completely
:::


# Exercise
%%%
tag := "runtime-special-types-exercise"
%%%

The {ref "positive-numbers"}[definition of {anchorName Pos (module := Examples.Classes)}`Pos`] does not take advantage of Lean's compilation of {anchorName all}`Nat` to an efficient type.
At run time, it is essentially a linked list.
Alternatively, a subtype can be defined that allows Lean's fast {anchorName all}`Nat` type to be used internally, as described {ref "subtypes"}[in the initial section on subtypes].
At run time, the proof will be erased.
Because the resulting structure has only a single data field, it is represented as that field, which means that this new representation of {anchorName Pos (module := Examples.Classes)}`Pos` is identical to that of {anchorName all}`Nat`.

After proving the theorem {anchorTerm all}`∀ {n k : Nat}, n ≠ 0 → k ≠ 0 → n + k ≠ 0`, define instances of {anchorName all}`ToString`, and {anchorName all}`Add` for this new representation of {anchorName Pos (module := Examples.Classes)}`Pos`. Then, define an instance of {anchorName all}`Mul`, proving any necessary theorems along the way.
