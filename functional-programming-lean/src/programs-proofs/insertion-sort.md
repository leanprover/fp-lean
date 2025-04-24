# Insertion Sort and Array Mutation

While insertion sort does not have the optimal worst-case time complexity for a sorting algorithm, it still has a number of useful properties:
 * It is simple and straightforward to implement and understand
 * It is an in-place algorithm, requiring no additional space to run
 * It is a stable sort
 * It is fast when the input is already almost sorted
 
In-place algorithms are particularly useful in Lean due to the way it manages memory.
In some cases, operations that would normally copy an array can be optimized into mutation.
This includes swapping elements in an array.

Most languages and run-time systems with automatic memory management, including JavaScript, the JVM, and .NET, use tracing garbage collection.
When memory needs to be reclaimed, the system starts at a number of _roots_ (such as the call stack and global values) and then determines which values can be reached by recursively chasing pointers.
Any values that can't be reached are deallocated, freeing memory.

Reference counting is an alternative to tracing garbage collection that is used by a number of languages, including Python, Swift, and Lean.
In a system with reference counting, each object in memory has a field that tracks how many references there are to it.
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
```lean
{{#example_in Examples/ProgramsProofs/InsertionSort.lean dbgTraceIfSharedSig}}
```
```output info
{{#example_out Examples/ProgramsProofs/InsertionSort.lean dbgTraceIfSharedSig}}
```
It takes a string and a value as arguments, and prints a message that uses the string to standard error if the value has more than one reference, returning the value.
This is not, strictly speaking, a pure function.
However, it is intended to be used only during development to check that a function is in fact able to re-use memory rather than allocating and copying.

When learning to use `dbgTraceIfShared`, it's important to know that `#eval` will report that many more values are shared than in compiled code.
This can be confusing.
It's important to build an executable with `lake` rather than experimenting in an editor.

Insertion sort consists of two loops.
The outer loop moves a pointer from left to right across the array to be sorted.
After each iteration, the region of the array to the left of the pointer is sorted, while the region to the right may not yet be sorted.
The inner loop takes the element pointed to by the pointer and moves it to the left until the appropriate location has been found and the loop invariant has been restored.
In other words, each iteration inserts the next element of the array into the appropriate location in the sorted region.

## The Inner Loop

The inner loop of insertion sort can be implemented as a tail-recursive function that takes the array and the index of the element being inserted as arguments.
The element being inserted is repeatedly swapped with the element to its left until either the element to the left is smaller or the beginning of the array is reached.
The inner loop is structurally recursive on the `Nat` that is inside the `Fin` used to index into the array:
```leantac
{{#example_decl Examples/ProgramsProofs/InsertionSort.lean insertSorted}}
```
If the index `i` is `0`, then the element being inserted into the sorted region has reached the beginning of the region and is the smallest.
If the index is `i' + 1`, then the element at `i'` should be compared to the element at `i`.
Note that while `i` is a `Fin arr.size`, `i'` is just a `Nat` because it results from the `val` field of `i`.
Nonetheless, the proof automation used for checking array index notation includes `omega`, so `i'` is automatically usable as an index.

The two elements are looked up and compared. 
If the element to the left is less than or equal to the element being inserted, then the loop is finished and the invariant has been restored.
If the element to the left is greater than the element being inserted, then the elements are swapped and the inner loop begins again.
`Array.swap` takes both of its indices as `Nat`s, using the same tactics as array indexing behind the scenes to ensure that they are in bounds.

Nonetheless, the `Fin` used for the recursive call needs a proof that `i'` is in bounds for the result of swapping two elements.
The `simp` tactic's database contains the fact that swapping two elements of an array doesn't change its size, and the `[*]` argument instructs it to additionally use the assumption introduced by `have`.
Omitting the `have`-expression with the proof that `i' < arr.size` reveals the following goal:
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insertSortedNoProof}}
```



## The Outer Loop

The outer loop of insertion sort moves the pointer from left to right, invoking `insertSorted` at each iteration to insert the element at the pointer into the correct position in the array.
The basic form of the loop resembles the implementation of `Array.map`:
```lean
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insertionSortLoopTermination}}
```
An error occurs because there is no argument that decreases at every recursive call:
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insertionSortLoopTermination}}
```
While Lean can prove that a `Nat` that increases towards a constant bound at each iteration leads to a terminating function, this function has no constant bound because the array is replaced with the result of calling `insertSorted` at each iteration.

Before constructing the termination proof, it can be convenient to test the definition with a `partial` modifier to make sure that it returns the expected answers:
```lean
{{#example_decl Examples/ProgramsProofs/InsertionSort.lean partialInsertionSortLoop}}
```
```lean
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insertionSortPartialOne}}
```
```output info
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insertionSortPartialOne}}
```
```lean
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insertionSortPartialTwo}}
```
```output info
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insertionSortPartialTwo}}
```

### Termination

Once again, the function terminates because the difference between the index and the size of the array being processed decreases on each recursive call.
This time, however, Lean does not accept the `termination_by`:
```lean
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insertionSortLoopProof1}}
```
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insertionSortLoopProof1}}
```
The problem is that Lean has no way to know that `insertSorted` returns an array that's the same size as the one it is passed.
In order to prove that `insertionSortLoop` terminates, it is necessary to first prove that `insertSorted` doesn't change the size of the array.
Copying the unproved termination condition from the error message to the function and "proving" it with `sorry` allows the function to be temporarily accepted:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insertionSortLoopSorry}}
```
```output warning
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insertionSortLoopSorry}}
```

Because `insertSorted` is structurally recursive on the index of the element being inserted, the proof should be by induction on the index.
In the base case, the array is returned unchanged, so its length certainly does not change.
For the inductive step, the induction hypothesis is that a recursive call on the next smaller index will not change the length of the array.
There are two cases two consider: either the element has been fully inserted into the sorted region and the array is returned unchanged, in which case the length is also unchanged, or the element is swapped with the next one before the recursive call.
However, swapping two elements in an array doesn't change the size of it, and the induction hypothesis states that the recursive call with the next index returns an array that's the same size as its argument.
Thus, the size remains unchanged.

Translating this English-language theorem statement to Lean and proceeding using the techniques from this chapter is enough to prove the base case and make progress in the inductive step:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_0}}
```
The simplification using `insertSorted` in the inductive step revealed the pattern match in `insertSorted`:
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_0}}
```
When faced with a goal that includes `if` or `match`, the `split` tactic (not to be confused with the `split` function used in the definition of merge sort) replaces the goal with one new goal for each path of control flow:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_1}}
```
Because it typically doesn't matter _how_ a statement was proved, but only _that_ it was proved, proofs in Lean's output are typically replaced by `⋯`.
Additionally, each new goal has an assumption that indicates which branch led to that goal, named `heq✝` in this case:
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_1}}
```
Rather than write proofs for both simple cases, adding `<;> try rfl` after `split` causes the two straightforward cases to disappear immediately, leaving only a single goal:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_2}}
```
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_2}}
```

Unfortunately, the induction hypothesis is not strong enough to prove this goal.
The induction hypothesis states that calling `insertSorted` on `arr` leaves the size unchanged, but the proof goal is to show that the result of the recursive call with the result of swapping leaves the size unchanged.
Successfully completing the proof requires an induction hypothesis that works for _any_ array that is passed to `insertSorted` together with the smaller index as an argument

It is possible to get a strong induction hypothesis by using the `generalizing` option to the `induction` tactic.
This option brings additional assumptions from the context into the statement that's used to generate the base case, the induction hypothesis, and the goal to be shown in the inductive step.
Generalizing over `arr` leads to a stronger hypothesis:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_3}}
```
In the resulting goal, `arr` is now part of a "for all" statement in the inductive hypothesis:
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_3}}
```

However, this whole proof is beginning to get unmanageable.
The next step would be to introduce a variable standing for the length of the result of swapping, show that it is equal to `arr.size`, and then show that this variable is also equal to the length of the array that results from the recursive call.
These equality statements can then be chained together to prove the goal.
It's much easier, however, to carefully reformulate the theorem statement such that the induction hypothesis is automatically strong enough and the variables are already introduced.
The reformulated statement reads:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_0}}
```
This version of the theorem statement is easier to prove for a few reasons:
 1. Rather than bundling up the index and the proof of its validity in a `Fin`, the index comes before the array.
    This allows the induction hypothesis to naturally generalize over the array and the proof that `i` is in bounds.
 2. An abstract length `len` is introduced to stand for `array.size`.
    Proof automation is often better at working with explicit statements of equality.

The resulting proof state shows the statement that will be used to generate the induction hypothesis, as well as the base case and the goal of the inductive step:
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_0}}
```

Compare the statement with the goals that result from the `induction` tactic:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_1a}}
```
In the base case, each occurrence of `i` has been replaced by `0`.
Using `intro` to introduce each assumption and then simplifying using `insertSorted` will prove the goal, because `insertSorted` at index `zero` returns its argument unchanged:
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_1a}}
```
In the inductive step, the induction hypothesis has exactly the right strength.
It will be useful for _any_ array, so long as that array has length `len`:
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_1b}}
```

In the base case, `simp` reduces the goal to `arr.size = len`:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_2}}
```
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_2}}
```
This can be proved using the assumption `hLen`.
Adding the `*` parameter to `simp` instructs it to additionally use assumptions, which solves the goal:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_2b}}
```

In the inductive step, introducing assumptions and simplifying the goal results once again in a goal that contains a pattern match:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_3}}
```
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_3}}
```
Using the `split` tactic results in one goal for each pattern.
Once again, the first two goals result from branches without recursive calls, so the induction hypothesis is not necessary:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_4}}
```
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_4}}
```
Running `try assumption` in each goal that results from `split` eliminates both of the non-recursive goals:
```leantac
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_5}}
```
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_5}}
```

The new formulation of the proof goal, in which a constant `len` is used for the lengths of all the arrays involved in the recursive function, falls nicely within the kinds of problems that `simp` can solve.
This final proof goal can be solved by `simp [*]`, because the assumptions that relate the array's length to `len` are important:
```leantac
{{#example_decl Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo_6}}
```

Finally, because `simp [*]` can use assumptions, the `try assumption` line can be replaced by `simp [*]`, shortening the proof:
```leantac
{{#example_decl Examples/ProgramsProofs/InsertionSort.lean insert_sorted_size_eq_redo}}
```

This proof can now be used to replace the `sorry` in `insertionSortLoop`.
Providing `arr.size` as the `len` argument to the theorem causes the final conclusion to be `(insertSorted arr ⟨i, isLt⟩).size = arr.size`, so the rewrite ends with a very manageable proof goal:
```leantacnorfl
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insertionSortLoopRw}}
```
```output error
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insertionSortLoopRw}}
```
The `omega` tactic can prove this:
```leantacnorfl
{{#example_decl Examples/ProgramsProofs/InsertionSort.lean insertionSortLoop}}
```


## The Driver Function

Insertion sort itself calls `insertionSortLoop`, initializing the index that demarcates the sorted region of the array from the unsorted region to `0`:
```lean
{{#example_decl Examples/ProgramsProofs/InsertionSort.lean insertionSort}}
```

A few quick tests show the function is at least not blatantly wrong:
```lean
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insertionSortNums}}
```
```output info
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insertionSortNums}}
```
```lean
{{#example_in Examples/ProgramsProofs/InsertionSort.lean insertionSortStrings}}
```
```output info
{{#example_out Examples/ProgramsProofs/InsertionSort.lean insertionSortStrings}}
```

## Is This Really Insertion Sort?

Insertion sort is _defined_ to be an in-place sorting algorithm.
What makes it useful, despite its quadratic worst-case run time, is that it is a stable sorting algorithm that doesn't allocate extra space and that handles almost-sorted data efficiently.
If each iteration of the inner loop allocated a new array, then the algorithm wouldn't _really_ be insertion sort.

Lean's array operations, such as `Array.set` and `Array.swap`, check whether the array in question has a reference count that is greater than one.
If so, then the array is visible to multiple parts of the code, which means that it must be copied.
Otherwise, Lean would no longer be a pure functional language.
However, when the reference count is exactly one, there are no other potential observers of the value.
In these cases, the array primitives mutate the array in place.
What other parts of the program don't know can't hurt them.

Lean's proof logic works at the level of pure functional programs, not the underlying implementation.
This means that the best way to discover whether a program unnecessarily copies data is to test it.
Adding calls to `dbgTraceIfShared` at each point where mutation is desired causes the provided message to be printed to `stderr` when the value in question has more than one reference.

Insertion sort has precisely one place that is at risk of copying rather than mutating: the call to `Array.swap`.
Replacing `arr.swap ⟨i', by assumption⟩ i` with `((dbgTraceIfShared "array to swap" arr).swap ⟨i', by assumption⟩ i)` causes the program to emit `shared RC array to swap` whenever it is unable to mutate the array.
However, this change to the program changes the proofs as well, because now there's a call to an additional function.
Adding a local assumption that `dbgTraceIfShared` preserves the length of its argument and adding it to some calls to `simp` is enough to fix the program and proofs.

The complete instrumented code for insertion sort is:
```leantacnorfl
{{#include ../../../examples/Examples/ProgramsProofs/InstrumentedInsertionSort.lean:InstrumentedInsertionSort}}
```

A bit of cleverness is required to check whether the instrumentation actually works.
First off, the Lean compiler aggressively optimizes function calls away when all their arguments are known at compile time.
Simply writing a program that applies `insertionSort` to a large array is not sufficient, because the resulting compiled code may contain only the sorted array as a constant.
The easiest way to ensure that the compiler doesn't optimize away the sorting routine is to read the array from `stdin`.
Secondly, the compiler performs dead code elimination.
Adding extra `let`s to the program won't necessarily result in more references in running code if the `let`-bound variables are never used.
To ensure that the extra reference is not eliminated entirely, it's important to ensure that the extra reference is somehow used.

The first step in testing the instrumentation is to write `getLines`, which reads an array of lines from standard input:
```lean
{{#include ../../../examples/Examples/ProgramsProofs/InstrumentedInsertionSort.lean:getLines}}
```
`IO.FS.Stream.getLine` returns a complete line of text, including the trailing newline.
It returns `""` when the end-of-file marker has been reached.

Next, two separate `main` routines are needed.
Both read the array to be sorted from standard input, ensuring that the calls to `insertionSort` won't be replaced by their return values at compile time.
Both then print to the console, ensuring that the calls to `insertionSort` won't be optimized away entirely.
One of them prints only the sorted array, while the other prints both the sorted array and the original array.
The second function should trigger a warning that `Array.swap` had to allocate a new array:
```lean
{{#include ../../../examples/Examples/ProgramsProofs/InstrumentedInsertionSort.lean:mains}}
```

The actual `main` simply selects one of the two main actions based on the provided command-line arguments:
```lean
{{#include ../../../examples/Examples/ProgramsProofs/InstrumentedInsertionSort.lean:main}}
```

Running it with no arguments produces the expected usage information:
```
$ {{#command {sort-demo} {sort-sharing} {./run-usage} {sort}}}
{{#command_out {sort-sharing} {./run-usage} }}
```

The file `test-data` contains the following rocks:
```
{{#file_contents {sort-sharing} {sort-demo/test-data}}}
```

Using the instrumented insertion sort on these rocks results them being printed in alphabetical order:
```
$ {{#command {sort-demo} {sort-sharing} {sort --unique < test-data}}}
{{#command_out {sort-sharing} {sort --unique < test-data} }}
```

However, the version in which a reference is retained to the original array results in a notification on `stderr` (namely, `shared RC array to swap`) from the first call to `Array.swap`:
```
$ {{#command {sort-demo} {sort-sharing} {sort --shared < test-data}}}
{{#command_out {sort-sharing} {sort --shared < test-data} }}
```
The fact that only a single `shared RC` notification appears means that the array is copied only once.
This is because the copy that results from the call to `Array.swap` is itself unique, so no further copies need to be made.
In an imperative language, subtle bugs can result from forgetting to explicitly copy an array before passing it by reference.
When running `sort --shared`, the array is copied as needed to preserve the pure functional meaning of Lean programs, but no more.


## Other Opportunities for Mutation

The use of mutation instead of copying when references are unique is not limited to array update operators.
Lean also attempts to "recycle" constructors whose reference counts are about to fall to zero, reusing them instead of allocating new data.
This means, for instance, that `List.map` will mutate a linked list in place, at least in cases when nobody could possibly notice.
One of the most important steps in optimizing hot loops in Lean code is making sure that the data being modified is not referred to from multiple locations.

## Exercises

 * Write a function that reverses arrays. Test that if the input array has a reference count of one, then your function does not allocate a new array.

* Implement either merge sort or quicksort for arrays. Prove that your implementation terminates, and test that it doesn't allocate more arrays than expected. This is a challenging exercise!
 
   
