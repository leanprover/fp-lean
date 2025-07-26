import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.InsertionSort"

#doc (Manual) "Insertion Sort and Array Mutation" =>

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
If object $`A` references object $`B` , and object $`B` references object $`A`, they will never be deallocated, even if nothing else in the program references either $`A` or $`B`.
Circular references result either from uncontrolled recursion or from mutable references.
Because Lean supports neither, it is impossible to construct circular references.

Reference counting means that the Lean runtime system's primitives for allocating and deallocating data structures can check whether a reference count is about to fall to zero, and re-use an existing object instead of allocating a new one.
This is particularly important when working with large arrays.


An implementation of insertion sort for Lean arrays should satisfy the following criteria:
 1. Lean should accept the function without a {kw}`partial` annotation
 2. If passed an array to which there are no other references, it should modify the array in-place rather than allocating a new one

The first criterion is easy to check: if Lean accepts the definition, then it is satisfied.
The second, however, requires a means of testing it.
Lean provides a built-in function called {anchorName dbgTraceIfSharedSig}`dbgTraceIfShared` with the following signature:
```anchor dbgTraceIfSharedSig
#check dbgTraceIfShared
```
```anchorInfo dbgTraceIfSharedSig
dbgTraceIfShared.{u} {α : Type u} (s : String) (a : α) : α
```
It takes a string and a value as arguments, and prints a message that uses the string to standard error if the value has more than one reference, returning the value.
This is not, strictly speaking, a pure function.
However, it is intended to be used only during development to check that a function is in fact able to re-use memory rather than allocating and copying.

When learning to use {anchorName dbgTraceIfSharedSig}`dbgTraceIfShared`, it's important to know that {kw}`#eval` will report that many more values are shared than in compiled code.
This can be confusing.
It's important to build an executable with {lit}`lake` rather than experimenting in an editor.

Insertion sort consists of two loops.
The outer loop moves a pointer from left to right across the array to be sorted.
After each iteration, the region of the array to the left of the pointer is sorted, while the region to the right may not yet be sorted.
The inner loop takes the element pointed to by the pointer and moves it to the left until the appropriate location has been found and the loop invariant has been restored.
In other words, each iteration inserts the next element of the array into the appropriate location in the sorted region.

# The Inner Loop

The inner loop of insertion sort can be implemented as a tail-recursive function that takes the array and the index of the element being inserted as arguments.
The element being inserted is repeatedly swapped with the element to its left until either the element to the left is smaller or the beginning of the array is reached.
The inner loop is structurally recursive on the {anchorName insertionSortLoop}`Nat` that is inside the {anchorName insertSorted}`Fin` used to index into the array:

```anchor insertSorted
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by
      omega
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted (arr.swap i' i) ⟨i', by simp [*]⟩
```
If the index {anchorName insertSorted}`i` is {anchorTerm insertSorted}`0`, then the element being inserted into the sorted region has reached the beginning of the region and is the smallest.
If the index is {anchorTerm insertSorted}`i' + 1`, then the element at {anchorName insertSorted}`i'` should be compared to the element at {anchorName insertSorted}`i`.
Note that while {anchorName insertSorted}`i` is a {anchorTerm insertSorted}`Fin arr.size`, {anchorName insertSorted}`i'` is just a {anchorName insertionSortLoop}`Nat` because it results from the {anchorName names}`val` field of {anchorName insertSorted}`i`.
Nonetheless, the proof automation used for checking array index notation includes {anchorTerm insertSorted}`omega`, so {anchorName insertSorted}`i'` is automatically usable as an index.

The two elements are looked up and compared.
If the element to the left is less than or equal to the element being inserted, then the loop is finished and the invariant has been restored.
If the element to the left is greater than the element being inserted, then the elements are swapped and the inner loop begins again.
{anchorName names}`Array.swap` takes both of its indices as {anchorName names}`Nat`s, using the same tactics as array indexing behind the scenes to ensure that they are in bounds.

Nonetheless, the {anchorName names}`Fin` used for the recursive call needs a proof that {anchorName insertSorted}`i'` is in bounds for the result of swapping two elements.
The {anchorTerm insertSorted}`simp` tactic's database contains the fact that swapping two elements of an array doesn't change its size, and the {anchorTerm insertSorted}`[*]` argument instructs it to additionally use the assumption introduced by {kw}`have`.
Omitting the {kw}`have`-expression with the proof that {anchorTerm insertSorted}`i' < arr.size` reveals the following goal:
```anchorError insertSortedNoProof
unsolved goals
α : Type ?u.7
inst✝ : Ord α
arr : Array α
i : Fin arr.size
i' : Nat
isLt✝ : i' + 1 < arr.size
⊢ i' < arr.size
```



# The Outer Loop

The outer loop of insertion sort moves the pointer from left to right, invoking {anchorName insertionSortLoop}`insertSorted` at each iteration to insert the element at the pointer into the correct position in the array.
The basic form of the loop resembles the implementation of {anchorTerm etc}`Array.map`:
```anchor insertionSortLoopTermination
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
```
An error occurs because there is no argument that decreases at every recursive call:
```anchorError insertionSortLoopTermination
fail to show termination for
  insertionSortLoop
with errors
failed to infer structural recursion:
Not considering parameter α of insertionSortLoop:
  it is unchanged in the recursive calls
Not considering parameter #2 of insertionSortLoop:
  it is unchanged in the recursive calls
Cannot use parameter arr:
  the type Array α does not have a `.brecOn` recursor
Cannot use parameter i:
  failed to eliminate recursive application
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
            arr i #1
1) 569:4-55   ? ?  ?

#1: arr.size - i

Please use `termination_by` to specify a decreasing measure.
```
While Lean can prove that a {anchorName insertionSortLoop}`Nat` that increases towards a constant bound at each iteration leads to a terminating function, this function has no constant bound because the array is replaced with the result of calling {anchorName insertionSortLoop}`insertSorted` at each iteration.

Before constructing the termination proof, it can be convenient to test the definition with a {kw}`partial` modifier to make sure that it returns the expected answers:

```anchor partialInsertionSortLoop
partial def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
```
```anchor insertionSortPartialOne
#eval insertionSortLoop #[5, 17, 3, 8] 0
```
```anchorInfo insertionSortPartialOne
#[3, 5, 8, 17]
```
```anchor insertionSortPartialTwo
#eval insertionSortLoop #["metamorphic", "igneous", "sedentary"] 0
```
```anchorInfo insertionSortPartialTwo
#["igneous", "metamorphic", "sedentary"]
```

## Termination

Once again, the function terminates because the difference between the index and the size of the array being processed decreases on each recursive call.
This time, however, Lean does not accept the {kw}`termination_by`:
```anchor insertionSortLoopProof1
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
```
```anchorError insertionSortLoopProof1
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Nat
h : i < arr.size
⊢ (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i
```
The problem is that Lean has no way to know that {anchorName insertionSortLoop}`insertSorted` returns an array that's the same size as the one it is passed.
In order to prove that {anchorName insertionSortLoop}`insertionSortLoop` terminates, it is necessary to first prove that {anchorName insertionSortLoop}`insertSorted` doesn't change the size of the array.
Copying the unproved termination condition from the error message to the function and “proving” it with {anchorTerm insertionSortLoopSorry}`sorry` allows the function to be temporarily accepted:
```anchor insertionSortLoopSorry
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      sorry
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
```
```anchorWarning insertionSortLoopSorry
declaration uses 'sorry'
```

Because {anchorName insertionSortLoop}`insertSorted` is structurally recursive on the index of the element being inserted, the proof should be by induction on the index.
In the base case, the array is returned unchanged, so its length certainly does not change.
For the inductive step, the induction hypothesis is that a recursive call on the next smaller index will not change the length of the array.
There are two cases two consider: either the element has been fully inserted into the sorted region and the array is returned unchanged, in which case the length is also unchanged, or the element is swapped with the next one before the recursive call.
However, swapping two elements in an array doesn't change the size of it, and the induction hypothesis states that the recursive call with the next index returns an array that's the same size as its argument.
Thus, the size remains unchanged.

Translating this English-language theorem statement to Lean and proceeding using the techniques from this chapter is enough to prove the base case and make progress in the inductive step:
```anchor insert_sorted_size_eq_0
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
```
The simplification using {anchorName insert_sorted_size_eq_0}`insertSorted` in the inductive step revealed the pattern match in {anchorName insert_sorted_size_eq_0}`insertSorted`:
```anchorError insert_sorted_size_eq_0
unsolved goals
case succ
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
⊢ (match compare arr[j'] arr[j' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size =
  arr.size
```
When faced with a goal that includes {kw}`if` or {kw}`match`, the {anchorTerm insert_sorted_size_eq_1}`split` tactic (not to be confused with the {anchorName splitList (module := Examples.ProgramsProofs.Inequalities)}`splitList` function used in the definition of merge sort) replaces the goal with one new goal for each path of control flow:
```anchor insert_sorted_size_eq_1
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split
```
Because it typically doesn't matter _how_ a statement was proved, but only _that_ it was proved, proofs in Lean's output are typically replaced by {lit}`⋯`.
Additionally, each new goal has an assumption that indicates which branch led to that goal, named {lit}`heq✝` in this case:
```anchorError insert_sorted_size_eq_1
unsolved goals
case h_1
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.lt
⊢ arr.size = arr.size

case h_2
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.eq
⊢ arr.size = arr.size

case h_3
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.gt
⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
```
Rather than write proofs for both simple cases, adding {anchorTerm insert_sorted_size_eq_2}`<;> try rfl` after {anchorTerm insert_sorted_size_eq_2}`split` causes the two straightforward cases to disappear immediately, leaving only a single goal:
```anchor insert_sorted_size_eq_2
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split <;> try rfl
```
```anchorError insert_sorted_size_eq_2
unsolved goals
case h_3
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin arr.size
j' : Nat
ih : ∀ (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.gt
⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
```

Unfortunately, the induction hypothesis is not strong enough to prove this goal.
The induction hypothesis states that calling {anchorName insert_sorted_size_eq_3}`insertSorted` on {anchorName insert_sorted_size_eq_3}`arr` leaves the size unchanged, but the proof goal is to show that the result of the recursive call with the result of swapping leaves the size unchanged.
Successfully completing the proof requires an induction hypothesis that works for _any_ array that is passed to {anchorName insert_sorted_size_eq_3}`insertSorted` together with the smaller index as an argument

It is possible to get a strong induction hypothesis by using the {anchorTerm insert_sorted_size_eq_3}`generalizing` option to the {anchorTerm insert_sorted_size_eq_3}`induction` tactic.
This option brings additional assumptions from the context into the statement that's used to generate the base case, the induction hypothesis, and the goal to be shown in the inductive step.
Generalizing over {anchorName insert_sorted_size_eq_3}`arr` leads to a stronger hypothesis:
```anchor insert_sorted_size_eq_3
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j generalizing arr with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split <;> try rfl
```
In the resulting goal, {anchorName insert_sorted_size_eq_3}`arr` is now part of a “for all” statement in the inductive hypothesis:
```anchorError insert_sorted_size_eq_3
unsolved goals
case h_3
α : Type u_1
inst✝ : Ord α
j' : Nat
ih : ∀ (arr : Array α) (i : Fin arr.size) (isLt : j' < arr.size), (insertSorted arr ⟨j', isLt⟩).size = arr.size
arr : Array α
i : Fin arr.size
isLt : j' + 1 < arr.size
x✝ : Ordering
heq✝ : compare arr[j'] arr[j' + 1] = Ordering.gt
⊢ (insertSorted (arr.swap j' (j' + 1) ⋯ ⋯) ⟨j', ⋯⟩).size = arr.size
```

However, this whole proof is beginning to get unmanageable.
The next step would be to introduce a variable standing for the length of the result of swapping, show that it is equal to {anchorTerm insert_sorted_size_eq_3}`arr.size`, and then show that this variable is also equal to the length of the array that results from the recursive call.
These equality statements can then be chained together to prove the goal.
It's much easier, however, to carefully reformulate the theorem statement such that the induction hypothesis is automatically strong enough and the variables are already introduced.
The reformulated statement reads:
```anchor insert_sorted_size_eq_redo_0
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  skip
```
This version of the theorem statement is easier to prove for a few reasons:
 1. Rather than bundling up the index and the proof of its validity in a {anchorName insertSorted}`Fin`, the index comes before the array.
    This allows the induction hypothesis to naturally generalize over the array and the proof that {anchorName insert_sorted_size_eq_redo_0}`i` is in bounds.
 2. An abstract length {anchorName insert_sorted_size_eq_redo_0}`len` is introduced to stand for {anchorTerm insert_sorted_size_eq_redo_0}`arr.size`.
    Proof automation is often better at working with explicit statements of equality.

The resulting proof state shows the statement that will be used to generate the induction hypothesis, as well as the base case and the goal of the inductive step:
```anchorError insert_sorted_size_eq_redo_0
unsolved goals
α : Type u_1
inst✝ : Ord α
len i : Nat
⊢ ∀ (arr : Array α) (isLt : i < arr.size), arr.size = len → (insertSorted arr ⟨i, isLt⟩).size = len
```

Compare the statement with the goals that result from the {anchorTerm insert_sorted_size_eq_redo_1a}`induction` tactic:
```anchor insert_sorted_size_eq_redo_1a
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero => skip
  | succ i' ih => skip
```
In the base case, each occurrence of {anchorName insert_sorted_size_eq_redo_1a}`i` has been replaced by {lit}`0`.
Using {anchorTerm insert_sorted_size_eq_redo_2}`intro` to introduce each assumption and then simplifying using {anchorName insert_sorted_size_eq_redo_2}`insertSorted` will prove the goal, because {anchorName insert_sorted_size_eq_redo_2}`insertSorted` at index {lit}`0` returns its argument unchanged:
```anchorError insert_sorted_size_eq_redo_1a
unsolved goals
case zero
α : Type u_1
inst✝ : Ord α
len : Nat
⊢ ∀ (arr : Array α) (isLt : 0 < arr.size), arr.size = len → (insertSorted arr ⟨0, isLt⟩).size = len
```
In the inductive step, the induction hypothesis has exactly the right strength.
It will be useful for _any_ array, so long as that array has length {anchorName insert_sorted_size_eq_redo_2}`len`:
```anchorError insert_sorted_size_eq_redo_1b
unsolved goals
case succ
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih : ∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = len
⊢ ∀ (arr : Array α) (isLt : i' + 1 < arr.size), arr.size = len → (insertSorted arr ⟨i' + 1, isLt⟩).size = len
```

In the base case, {anchorTerm insert_sorted_size_eq_redo_2}`simp` reduces the goal to {anchorTerm insert_sorted_size_eq_redo_2}`arr.size = len`:
```anchor insert_sorted_size_eq_redo_2
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted]
  | succ i' ih => skip
```
```anchorError insert_sorted_size_eq_redo_2
unsolved goals
case zero
α : Type u_1
inst✝ : Ord α
len : Nat
arr : Array α
isLt : 0 < arr.size
hLen : arr.size = len
⊢ arr.size = len
```
This can be proved using the assumption {anchorName insert_sorted_size_eq_redo_2b}`hLen`.
Adding the {anchorTerm insert_sorted_size_eq_redo_2b}`*` parameter to {anchorTerm insert_sorted_size_eq_redo_2b}`simp` instructs it to additionally use assumptions, which solves the goal:
```anchor insert_sorted_size_eq_redo_2b
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, *]
  | succ i' ih => skip
```

In the inductive step, introducing assumptions and simplifying the goal results once again in a goal that contains a pattern match:
```anchor insert_sorted_size_eq_redo_3
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, *]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted]
```
```anchorError insert_sorted_size_eq_redo_3
unsolved goals
case succ
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih : ∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = len
arr : Array α
isLt : i' + 1 < arr.size
hLen : arr.size = len
⊢ (match compare arr[i'] arr[i' + 1] with
    | Ordering.lt => arr
    | Ordering.eq => arr
    | Ordering.gt => insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size =
  len
```
Using the {anchorTerm insert_sorted_size_eq_redo_4}`split` tactic results in one goal for each pattern.
Once again, the first two goals result from branches without recursive calls, so the induction hypothesis is not necessary:
```anchor insert_sorted_size_eq_redo_4
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, *]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted]
    split
```
```anchorError insert_sorted_size_eq_redo_4
unsolved goals
case h_1
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih : ∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = len
arr : Array α
isLt : i' + 1 < arr.size
hLen : arr.size = len
x✝ : Ordering
heq✝ : compare arr[i'] arr[i' + 1] = Ordering.lt
⊢ arr.size = len

case h_2
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih : ∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = len
arr : Array α
isLt : i' + 1 < arr.size
hLen : arr.size = len
x✝ : Ordering
heq✝ : compare arr[i'] arr[i' + 1] = Ordering.eq
⊢ arr.size = len

case h_3
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih : ∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = len
arr : Array α
isLt : i' + 1 < arr.size
hLen : arr.size = len
x✝ : Ordering
heq✝ : compare arr[i'] arr[i' + 1] = Ordering.gt
⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len
```
Running {anchorTerm insert_sorted_size_eq_redo_5}`try assumption` in each goal that results from {anchorTerm insert_sorted_size_eq_redo_5}`split` eliminates both of the non-recursive goals:
```anchor insert_sorted_size_eq_redo_5
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, *]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted]
    split <;> try assumption
```
```anchorError insert_sorted_size_eq_redo_5
unsolved goals
case h_3
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih : ∀ (arr : Array α) (isLt : i' < arr.size), arr.size = len → (insertSorted arr ⟨i', isLt⟩).size = len
arr : Array α
isLt : i' + 1 < arr.size
hLen : arr.size = len
x✝ : Ordering
heq✝ : compare arr[i'] arr[i' + 1] = Ordering.gt
⊢ (insertSorted (arr.swap i' (i' + 1) ⋯ ⋯) ⟨i', ⋯⟩).size = len
```

The new formulation of the proof goal, in which a constant {anchorName insert_sorted_size_eq_redo_6}`len` is used for the lengths of all the arrays involved in the recursive function, falls nicely within the kinds of problems that {anchorTerm insert_sorted_size_eq_redo_6}`simp` can solve.
This final proof goal can be solved by {anchorTerm insert_sorted_size_eq_redo_6}`simp [*]`, because the assumptions that relate the array's length to {anchorName insert_sorted_size_eq_redo_6}`len` are important:

```anchor insert_sorted_size_eq_redo_6
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, *]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted]
    split <;> try assumption
    simp [*]
```

Finally, because {anchorTerm insert_sorted_size_eq_redo}`simp [*]` can use assumptions, the {anchorTerm insert_sorted_size_eq_redo_6}`try assumption` line can be replaced by {anchorTerm insert_sorted_size_eq_redo}`simp [*]`, shortening the proof:

```anchor insert_sorted_size_eq_redo
theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, *]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted]
    split <;> simp [*]
```

This proof can now be used to replace the {anchorTerm insertionSortLoopSorry}`sorry` in {anchorName insertionSortLoopSorry}`insertionSortLoop`.
Providing {anchorTerm insertionSortLoopRw}`arr.size` as the {anchorName insert_sorted_size_eq_redo}`len` argument to the theorem causes the final conclusion to be {lit}`(insertSorted arr ⟨i, isLt⟩).size = arr.size`, so the rewrite ends with a very manageable proof goal:
```anchor insertionSortLoopRw
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      rw [insert_sorted_size_eq arr.size i arr h rfl]
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
```
```anchorError insertionSortLoopRw
unsolved goals
α : Type ?u.130721
inst✝ : Ord α
arr : Array α
i : Nat
h : i < arr.size
⊢ arr.size - (i + 1) < arr.size - i
```
The {anchorTerm insertionSortLoop}`omega` tactic can prove this:

```anchor insertionSortLoop
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      rw [insert_sorted_size_eq arr.size i arr h rfl]
      omega
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
```


# The Driver Function

Insertion sort itself calls {anchorName insertionSort}`insertionSortLoop`, initializing the index that demarcates the sorted region of the array from the unsorted region to {anchorTerm insertionSort}`0`:

```anchor insertionSort
def insertionSort [Ord α] (arr : Array α) : Array α :=
   insertionSortLoop arr 0
```

A few quick tests show the function is at least not blatantly wrong:
```anchor insertionSortNums
#eval insertionSort #[3, 1, 7, 4]
```
```anchorInfo insertionSortNums
#[1, 3, 4, 7]
```
```anchor insertionSortStrings
#eval insertionSort #[ "quartz", "marble", "granite", "hematite"]
```
```anchorInfo insertionSortStrings
#["granite", "hematite", "marble", "quartz"]
```

# Is This Really Insertion Sort?

Insertion sort is _defined_ to be an in-place sorting algorithm.
What makes it useful, despite its quadratic worst-case run time, is that it is a stable sorting algorithm that doesn't allocate extra space and that handles almost-sorted data efficiently.
If each iteration of the inner loop allocated a new array, then the algorithm wouldn't _really_ be insertion sort.

Lean's array operations, such as {anchorName names}`Array.set` and {anchorName names}`Array.swap`, check whether the array in question has a reference count that is greater than one.
If so, then the array is visible to multiple parts of the code, which means that it must be copied.
Otherwise, Lean would no longer be a pure functional language.
However, when the reference count is exactly one, there are no other potential observers of the value.
In these cases, the array primitives mutate the array in place.
What other parts of the program don't know can't hurt them.

Lean's proof logic works at the level of pure functional programs, not the underlying implementation.
This means that the best way to discover whether a program unnecessarily copies data is to test it.
Adding calls to {anchorName dbgTraceIfSharedSig}`dbgTraceIfShared` at each point where mutation is desired causes the provided message to be printed to {lit}`stderr` when the value in question has more than one reference.

Insertion sort has precisely one place that is at risk of copying rather than mutating: the call to {anchorName names}`Array.swap`.
Replacing {anchorTerm insertSorted}`arr.swap i' i` with {anchorTerm InstrumentedInsertionSort (module := Examples.ProgramsProofs.InstrumentedInsertionSort)}`(dbgTraceIfShared "array to swap" arr).swap i' i` causes the program to emit {lit}`shared RC array to swap` whenever it is unable to mutate the array.
However, this change to the program changes the proofs as well, because now there's a call to an additional function.
Adding a local assumption that {anchorName dbgTraceIfSharedSig}`dbgTraceIfShared` preserves the length of its argument and adding it to some calls to {anchorTerm InstrumentedInsertionSort (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`simp` is enough to fix the program and proofs.

The complete instrumented code for insertion sort is:
```anchor InstrumentedInsertionSort (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by
      omega
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      have : (dbgTraceIfShared "array to swap" arr).size = arr.size := by
        simp [dbgTraceIfShared]
      insertSorted
        ((dbgTraceIfShared "array to swap" arr).swap i' i)
        ⟨i', by simp [*]⟩

theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
    (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) →
    (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, *]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted, dbgTraceIfShared]
    split <;> simp [*]

def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      rw [insert_sorted_size_eq arr.size i arr h rfl]
      omega
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i

def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0
```

A bit of cleverness is required to check whether the instrumentation actually works.
First off, the Lean compiler aggressively optimizes function calls away when all their arguments are known at compile time.
Simply writing a program that applies {anchorName InstrumentedInsertionSort (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`insertionSort` to a large array is not sufficient, because the resulting compiled code may contain only the sorted array as a constant.
The easiest way to ensure that the compiler doesn't optimize away the sorting routine is to read the array from {anchorName getLines (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`stdin`.
Secondly, the compiler performs dead code elimination.
Adding extra {kw}`let`s to the program won't necessarily result in more references in running code if the {kw}`let`-bound variables are never used.
To ensure that the extra reference is not eliminated entirely, it's important to ensure that the extra reference is somehow used.

The first step in testing the instrumentation is to write {anchorName getLines (module := Examples.ProgramsProofs.InstrumentedInsertionSort)}`getLines`, which reads an array of lines from standard input:
```anchor getLines (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def getLines : IO (Array String) := do
  let stdin ← IO.getStdin
  let mut lines : Array String := #[]
  let mut currLine ← stdin.getLine
  while !currLine.isEmpty do
     -- Drop trailing newline:
    lines := lines.push (currLine.dropRight 1)
    currLine ← stdin.getLine
  pure lines
```
{anchorName various (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`IO.FS.Stream.getLine` returns a complete line of text, including the trailing newline.
It returns {anchorTerm mains (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`""` when the end-of-file marker has been reached.

Next, two separate {anchorName main (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`main` routines are needed.
Both read the array to be sorted from standard input, ensuring that the calls to {anchorName mains (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`insertionSort` won't be replaced by their return values at compile time.
Both then print to the console, ensuring that the calls to {anchorName insertionSort}`insertionSort` won't be optimized away entirely.
One of them prints only the sorted array, while the other prints both the sorted array and the original array.
The second function should trigger a warning that {anchorName names}`Array.swap` had to allocate a new array:
```anchor mains (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def mainUnique : IO Unit := do
  let lines ← getLines
  for line in insertionSort lines do
    IO.println line

def mainShared : IO Unit := do
  let lines ← getLines
  IO.println "--- Sorted lines: ---"
  for line in insertionSort lines do
    IO.println line

  IO.println ""
  IO.println "--- Original data: ---"
  for line in lines do
    IO.println line
```

The actual {anchorName main (module:=Examples.ProgramsProofs.InstrumentedInsertionSort)}`main` simply selects one of the two main actions based on the provided command-line arguments:
```anchor main (module := Examples.ProgramsProofs.InstrumentedInsertionSort)
def main (args : List String) : IO UInt32 := do
  match args with
  | ["--shared"] => mainShared; pure 0
  | ["--unique"] => mainUnique; pure 0
  | _ =>
    IO.println "Expected single argument, either \"--shared\" or \"--unique\""
    pure 1
```

Running it with no arguments produces the expected usage information:
```commands «sort-sharing» "sort-demo"
$ expect -f ./run-usage # sort
Expected single argument, either "--shared" or "--unique"
```

The file {lit}`test-data` contains the following rocks:
```file «sort-sharing» "sort-demo/test-data"
schist
feldspar
diorite
pumice
obsidian
shale
gneiss
marble
flint
```

Using the instrumented insertion sort on these rocks results them being printed in alphabetical order:
```commands «sort-sharing» "sort-demo"
$ sort --unique < test-data
diorite
feldspar
flint
gneiss
marble
obsidian
pumice
schist
shale
```

However, the version in which a reference is retained to the original array results in a notification on {lit}`stderr` (namely, {lit}`shared RC array to swap`) from the first call to {anchorName names}`Array.swap`:
```commands «sort-sharing» "sort-demo"
$ sort --shared < test-data
--- Sorted lines: ---
diorite
feldspar
flint
gneiss
marble
obsidian
pumice
schist
shale

--- Original data: ---
schist
feldspar
diorite
pumice
obsidian
shale
gneiss
marble
flint
shared RC array to swap
```
The fact that only a single {lit}`shared RC` notification appears means that the array is copied only once.
This is because the copy that results from the call to {anchorName names}`Array.swap` is itself unique, so no further copies need to be made.
In an imperative language, subtle bugs can result from forgetting to explicitly copy an array before passing it by reference.
When running {lit}`sort --shared`, the array is copied as needed to preserve the pure functional meaning of Lean programs, but no more.


# Other Opportunities for Mutation

The use of mutation instead of copying when references are unique is not limited to array update operators.
Lean also attempts to “recycle” constructors whose reference counts are about to fall to zero, reusing them instead of allocating new data.
This means, for instance, that {anchorName names}`List.map` will mutate a linked list in place, at least in cases when nobody could possibly notice.
One of the most important steps in optimizing hot loops in Lean code is making sure that the data being modified is not referred to from multiple locations.

# Exercises

 * Write a function that reverses arrays. Test that if the input array has a reference count of one, then your function does not allocate a new array.

* Implement either merge sort or quicksort for arrays. Prove that your implementation terminates, and test that it doesn't allocate more arrays than expected. This is a challenging exercise!
