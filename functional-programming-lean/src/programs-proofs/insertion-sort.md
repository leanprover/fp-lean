# Insertion Sort

While insertion sort does not have the optimal worst-case time complexity for a sorting algorithm, it still has a number of useful properties:
 * It is simple and straightforward to implement and understand
 * It is an in-place algorithm, requiring no additional space to run
 * It is a stable sort
 * It is fast when the input is already almost sorted
 
In-place algorithms are particularly useful in Lean due to the way it manages memory.
In some cases, operations that would normally copy an array can be optimized into mutation.
This includes swapping elements in an array.

Most languages and run-time systems with automatic memory management, including JavaScript, the JVM, and .NET, use tracing garbage collection.
When memory needs to be reclaimed, the system starts at a number of roots (such as the call stack and global values) and then determines which values can be reached by recursively chasing pointers.
Any values that can't be reached are deallocated, freeing memory.

Reference counting is an alternative to tracing garbage collection that is used by a number of languages, including Python, Swift, and Lean.
In a system with reference counting, each object in memory has a field that tracks how many references there are it.
When a new reference is established, the counter is incremented.
When a reference ceases to exist, the counter is decremented.
When the counter reaches zero, the object is immediately deallocated.

Reference counting has one major disadvantage compared to a tracing garbage collector: circular references can lead to memory leaks.
If object \\( A \\) references object \\( B \\) , and object \\( B \\) references object \\( A \\), they will never be deallocated, even if nothing else in the program references either \\( A \\) or \\( B \\).
Circular references result either from uncontrolled recursion or from mutable references.
Because Lean supports neither, it is impossible to construct circular references.

Reference counting means that the Lean runtime system's primitives for allocating and deallocating data structures can check whether a reference count is about to fall to zero, and re-use an existing object instead of allocating a new one.
This is particularly important when working with large arrays.


An implementation of insertion sort for Lean arrays should satisfy the following criteria:
 1. Lean should accept the function without a `partial` annotation
 2. If passed an array to which there are no other references, it should modify the array in-place rather than allocating a new one

The first criterion is easy to check: if Lean accepts the definition, then it is satisfied.
The second, however, requires a means of testing it.
Lean provides a built-in function called `dbgTraceIfShared` with the following signature:
```output info
{{#example_out Examples/ProgramsProofs/InsertionSort.lean dbgTraceIfSharedSig}}
```
It takes a string and a value as arguments, and prints a message that uses the string to standard error if the value has more than one reference, returning the value.
This is not, strictly speaking, a pure function.
However, it is intended to be used only during development to check that a function is in fact able to re-use memory rather than allocating.

TODO find a good short example of dbgTraceIfShared here


Insertion sort consists of two loops.
The outer loop moves a pointer from left to right across the array to be sorted.
After each iteration, the region of the array to the left of the pointer is sorted, while the region to the right may not yet be sorted.
The inner loop takes the element pointed to by the pointer and moves it to the left until the appropriate location has been found and the loop invariant has been restored.
In other words, each iteration inserts the next element of the array into the appropriate location in the sorted region.

## The Inner Loop

The inner loop of insertion sort can be implemented as a tail-recursive function that takes the array and the index of the element being inserted as arguments.
The element being inserted is repeatedly swapped with the element to its left until either the element to the left is smaller or the beginning of the array is reached.
The inner loop is structurally recursive on the `Nat` that is inside the `Fin` used to index into the array:
```lean
{{#example_decl Examples/ProgramsProofs/InsertionSort.lean insertSorted}}
```
If the index `i` is `0`, then the element being inserted into the sorted region has reached the beginning of the region and is the smallest.
If the index is `i' + 1`, then the element at `i'` should be compared to the element at `i`.
Note that while `i` is a `Fin arr.size`, `i'` is just a `Nat` because it results from the `val` field of `i`.
It is thus necessary to prove that `i' < arr.size` before `i'` can be used to index into `arr`.

This proof uses a `have`-expression.
In Lean, `have` is similar to `let`.
When using `have`, the name is optional.
Typically, `let` is used to define names that refer to interesting values, while `have` is used to locally prove propositions that can be found by termination proofs and array indexing safety proofs.
Omitting the proof reveals the following goal:
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insertSortedNoProof}}
```

The hint `Nat.lt_of_succ_lt` is a theorem from Lean's standard library.
Its signature, found by `{{#example_in Examples/ProgramsProofs/InsertionSort.lean lt_of_succ_lt_type}}`, is
```output info
{{#example_out Examples/ProgramsProofs/InsertionSort.lean lt_of_succ_lt_type}}
```
In other words, it states that if `n + 1 < m`, then `n < m`.
The `*` passed to `simp` causes it to combine `Nat.lt_of_succ_lt` with the `isLt` field from `i` to get the final proof.

Having established that `i'` can be used to look up the element to the left of the element being inserted, the two elements are looked up and compared. 
If the element to the left is less than or equal to the element being inserted, then the loop is finished and the invariant has been restored.
If the element to the left is greater than the element being inserted, then the elements are swapped and the inner loop begins again.
`Array.swap` takes both of its indices as `Fin`s, and the `by assumption` that establishes that `i' < arr.size` makes use of the `have`.
The index to be examined on the next round through the inner loop is also `i'`, but `by assumption` is not sufficient in this case.
This is because the proof was written for the original array `arr`, not the result of swapping two elements.
The `simp` tactic's database contains the fact that swapping two elements of an array doesn't change its size.




