# Arrays and Indexing

The [Interlude](../props-proofs-indexing.md) describes how to use indexing notation in order to look up entries in a list by their position.
This syntax is also governed by a type class, and it can be used for a variety of different types.

## Arrays
For instance, Lean arrays are much more efficient than linked lists for most purposes.
In Lean, the type `Array α` is a dynamically-sized array holding values of type `α`, much like a Java `ArrayList`, a C++ `std::vector`, or a Rust `Vec`.
Unlike `List`, arrays occupy a contiguous region of memory, which is much better for processor caches.
Also, looking up a value in an array takes constant time, while lookup in a linked list takes time proportional to the index being accessed.

In pure functional languages like Lean, it is not possible to mutate a given position in a data structure.
Instead, a copy is made that has the desired modifications.
When using an array, the Lean compiler and runtime contain an optimizations that can allow modifications to be implemented as mutations behind the scenes when there is only a single unique reference to an array, while a list would require copies of all prior nodes to be made.

Arrays are written similarly to lists, but with a leading `#`:
```lean
{{#example_decl Examples/Classes.lean northernTrees}}
```
The number of values in an array can be found using `Array.size`.
For instance, `{{#example_in Examples/Classes.lean northernTreesSize}}` evaluates to `{{#example_out Examples/Classes.lean northernTreesSize}}`.
For indices that are smaller than an array's size, indexing notation can be used to find the corresponding value, just as with lists.
That is, `{{#example_in Examples/Classes.lean northernTreesTwo}}` evaluates to `{{#example_out Examples/Classes.lean northernTreesTwo}}`.
Similarly, the compiler requires a proof that an index is in bounds, and attempting to look up a value outside the bounds of the array results in a compile-time error, just as with lists.
For instance, `{{#example_in Examples/Classes.lean northernTreesEight}}` results in:
```output error
{{#example_out Examples/Classes.lean northernTreesEight}}
```

## Non-Empty Lists

A datatype that represents non-empty lists can be defined as a structure with a field for the head of the list and a field for the tail, which is an ordinary, potentially empty list:
```lean
{{#example_decl Examples/Classes.lean NonEmptyList}}
```
For example, the non-empty list `idahoSpiders` (which contains some spider species native to the US state of Idaho) consists of `{{#example_out Examples/Classes.lean firstSpider}}` followed by four other spiders, for a total of five spiders.

Looking up the value at a specific index in this list with a recursive function should consider three possibilities:
 1. The index is `0`, in which case the head of the list should be returned.
 2. The index is `n + 1` and the tail is empty, in which case the index is out of bounds.
 3. The index is `n + 1` and the tail is non-empty, in which case the function can be called recursively on the tail and `n`.

For example, a lookup function that returns an `Option` can be written as follows:
```lean
{{#example_decl Examples/Classes.lean NEListGetHuh}}
```
Each case in the pattern match corresponds to one of the possibilities above.
The recursive call to `get?` does not require a `NonEmptyList` namespace qualifier because the body of the definition is implicitly in the definition's namespace.
Another way to write this function uses `get?` for lists when the index is greater than zero:
```lean
{{#example_decl Examples/Classes.lean NEListGetHuhList}}
```

If the list contains one entry, then only `0` is a valid index.
If it contains two entries, then both `0` and `1` are valid indices.
If it contains three entries, then `0`, `1`, and `2` are valid indices.
In other words, the valid indices into a non-empty list are natural numbers that are strictly less than the length of the list, which are less than or equal to the length of the tail.

The definition of what it means for an index to be in bounds should be written as an `abbrev` because the tactics used to find evidence that indices are acceptable are able to solve inequalities of numbers, but they don't know anything about the name `NonEmptyList.inBounds`:
```lean
{{#example_decl Examples/Classes.lean inBoundsNEList}}
```
This function returns a proposition that might be true or false.
For instance, `2` is in bounds for `idahoSpiders`, while `5` is not:
```lean
{{#example_decl Examples/Classes.lean spiderBoundsChecks}}
```
The logical negation operator has a very low precedence, which means that `¬idahoSpiders.inBounds 5` is equivalent to `¬(idahoSpiders.inBounds 5)`.


This fact can be used to write a lookup function that requires evidence that the index is valid, and thus need not return `Option`, by delegating to the version for lists that checks the evidence at compile time:
```lean
{{#example_decl Examples/Classes.lean NEListGet}}
```
It is, of course, possible to write this function to use the evidence directly, rather than delegating to a standard library function that happens to be able to use the same evidence.
This requires techniques for working with proofs and propositions that are described later in this book.


## Overloading Indexing

Indexing notation for a collection type can be overloaded by defining an instance of the `GetElem` type class.
For the sake of flexiblity, `GetElem` has four parameters:
 * The type of the collection
 * The type of the index
 * The type of elements that are extracted from the collection
 * A function that determines what counts as evidence that the index is in bounds

The element type and the evidence function are both output parameters.
`GetElem` has a single method, `getElem`, which takes a collection value, an index value, and evidence that the index is in bounds as arguments, and returns an element:
```lean
{{#example_decl Examples/Classes.lean GetElem}}
```
 
In the case of `NonEmptyList α`, these parameters are:
 * The collection is `NonEmptyList α`
 * Indices have type `Nat`
 * The type of elements is `α`
 * An index is in bounds if it is less than or equal to the length of the tail

In fact, the `GetElem` instance can delegate directly to `NonEmptyList.get`:
```lean
{{#example_decl Examples/Classes.lean GetElemNEList}}
```
With this instance, `NonEmptyList` becomes just as convenient to use as `List`.
Evaluating `{{#example_in Examples/Classes.lean firstSpider}}` yields `{{#example_out Examples/Classes.lean firstSpider}}`, while `{{#example_in Examples/Classes.lean tenthSpider}}` leads to the compile-time error:
```output error
{{#example_out Examples/Classes.lean tenthSpider}}
```

Because both the collection type and the index type are input parameters to the `GetElem` type class, new types can be used to index into existing collections.
The positive number type `Pos` is a perfectly reasonable index into a `List`, with the caveat that it cannot point at the first entry.
The follow instance of `GetElem` allows `Pos` to be used just as conveniently as `Nat` to find a list entry:
```lean
{{#example_decl Examples/Classes.lean ListPosElem}}
```

Indexing can also make sense for non-numeric indices.
For example, `Bool` can be used to select between the fields in a point, with `false` corresponding to `x` and `true` corresponding to `y`:
```lean
{{#example_decl Examples/Classes.lean PPointBoolGetElem}}
```
In this case, both Booleans are valid indices.
Because every possible `Bool` is in bounds, the evidence is simply the true proposition `True`.

