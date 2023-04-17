# Special Types

Understanding the representation of data in memory is very important.
Usually, the representation can be understood from the definition of a datatype.
Each constructor corresponds to an object in memory that has a header that includes a tag and a reference count.
The constructor's arguments are each represented by a pointer to some other object.
In other words, `List` really is a linked list and extracting a field from a `structure` really does just chase a pointer.

There are, however, some important exceptions to this rule.
A number of types are treated specially by the compiler.
For example, the type `UInt32` is defined as `Fin (2 ^ 32)`, but it is replaced at run-time with an actual native implementation based on machine words.
Similarly, even though the definition of `Nat` suggests an implementation similar to `List Unit`, the actual run-time representation uses an efficient arbitrary-precision arithmetic library.
The Lean compiler translates from definitions that use pattern matching into the appropriate operations in this library, and calls to operations like addition and subtraction are mapped to fast operations from the underlying arithmetic library.
After all, addition should not take time linear in the size of the addends.

The fact that some types have special representations also means that care is needed when working with them.
Most of these types consist of a `structure` that is treated specially by the compiler.
With these structures, using the constructor or the field accessors directly can trigger an expensive conversion from an efficient representation to a slow one that is convenient for proofs.
For example, `String` is defined as a structure that contains a list of characters, but the run-time representation of strings is as packed arrays of characters, not as linked lists of pointers to characters.
Applying the constructor to a list of characters creates a packed array, and accessing the field of the structure takes time linear in the length of the string to allocate a linked list.
Arrays are represented similarly.

Both types themselves and proofs of propositions are completely erased from compiled code.
In other words, they take up no space, and any computations that might have been performed as part of a proof are similarly erased.
This means that proofs can take advantage of the convenient interface to strings and arrays as inductively-defined lists, including using induction to prove things about them, without imposing slow conversion steps while the program is running.
For these built-in types, a convenient logical representation of the data does not imply that the program must be slow.

The following types have special representations:

| Type                                  | Logical representation                                                                | Run-time Representation                 |
|---------------------------------------|---------------------------------------------------------------------------------------|-----------------------------------------|
| `Nat`                                 | Unary, with one pointer from each `Nat.succ`                                          | Efficient arbitrary-precision integers  |
| `Int`                                 | A sum type with constructors for positive or negative values, each containing a `Nat` | Efficient arbitrary-precision integers  |
| `UInt8`, `UInt16`, `UInt32`, `UInt64` | A `Fin` with an appropriate bound                                                     | Fixed-precision machine integers        |
| `Char`                                | A `UInt32` paired with a proof that it's a valid code point                           | Ordinary characters                     |
| `String`                              | A structure that contains a `List Char` in a field called `data`                      | Packed arrays of pointers to characters |
| `Array α`                             | A structure that contains a `List α` in a field called `data`                         | Packed arrays of pointers to `α` values |
| `Sort u`                              | A type                                                                                | Erased completely                       |
| Proofs of propositions                | Whatever data is suggested by the proposition when considered as a type of evidence   | Erased completely                       |

## Exercise

The [definition of `Pos`](../type-classes/pos.html) does not take advantage of Lean's compilation of `Nat` to an efficient type.
At run time, it is essentially a linked list.
Rewrite `Pos` as a structure that contains a `Nat` and a proof that it does not equal `0`.
At runtime, the proof will be erased, which means that this new representation of `Pos` is not substantially less efficient that the representation of `Nat`.

After proving the theorem `∀ {n k : Nat}, n ≠ 0 → k ≠ 0 → n + k ≠ 0`, define instance of `OfNat`, `ToString`, and `Add` for this new representation of `Pos`.
