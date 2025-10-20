import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso.Code.External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.ProgramsProofs.Inequalities"

#doc (Manual) "More Inequalities" =>
%%%
tag := "more-inequalities"
%%%

Lean's built-in proof automation is sufficient to check that {anchorName ArrayMapHelperOk (module:=Examples.ProgramsProofs.Arrays)}`arrayMapHelper` and {anchorName ArrayFindHelper (module:=Examples.ProgramsProofs.Arrays)}`findHelper` terminate.
All that was needed was to provide an expression whose value decreases with each recursive call.
However, Lean's built-in automation is not magic, and it often needs some help.

# Merge Sort
%%%
tag := "merge-sort"
%%%


One example of a function whose termination proof is non-trivial is merge sort on {moduleName}`List`.
Merge sort consists of two phases: first, a list is split in half.
Each half is sorted using merge sort, and then the results are merged using a function that combines two sorted lists into a larger sorted list.
The base cases are the empty list and the singleton list, both of which are already considered to be sorted.

To merge two sorted lists, there are two basic cases to consider:
 1. If one of the input lists is empty, then the result is the other list.
 2. If both lists are non-empty, then their heads should be compared. The result of the function is the smaller of the two heads, followed by the result of merging the remaining entries of both lists.

This is not structurally recursive on either list.
The recursion terminates because an entry is removed from one of the two lists in each recursive call, but it could be either list.
Behind the scenes, Lean uses this fact to prove that it terminates:

```anchor merge
def merge [Ord α] (xs : List α) (ys : List α) : List α :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x'::xs', y'::ys' =>
    match Ord.compare x' y' with
    | .lt | .eq => x' :: merge xs' (y' :: ys')
    | .gt => y' :: merge (x'::xs') ys'
```


A simple way to split a list is to add each entry in the input list to two alternating output lists:

```anchor splitList
def splitList (lst : List α) : (List α × List α) :=
  match lst with
  | [] => ([], [])
  | x :: xs =>
    let (a, b) := splitList xs
    (x :: b, a)
```
This splitting function is structurally recursive.

Merge sort checks whether a base case has been reached.
If so, it returns the input list.
If not, it splits the input, and merges the result of sorting each half:
```anchor mergeSortNoTerm
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    merge (mergeSort halves.fst) (mergeSort halves.snd)
```
Lean's pattern match compiler is able to tell that the assumption {anchorName mergeSortNoTerm}`h` introduced by the {kw}`if` that tests whether {anchorTerm mergeSortNoTerm}`xs.length < 2` rules out lists longer than one entry, so there is no “missing cases” error.
However, even though this program always terminates, it is not structurally recursive, and Lean is unable to automatically discover a decreasing measure:
```anchorError mergeSortNoTerm
fail to show termination for
  mergeSort
with errors
failed to infer structural recursion:
Not considering parameter α of mergeSort:
  it is unchanged in the recursive calls
Not considering parameter #2 of mergeSort:
  it is unchanged in the recursive calls
Cannot use parameter xs:
  failed to eliminate recursive application
    mergeSort halves.fst


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
            xs #1
1) 70:11-31  ?  ?
2) 70:34-54  _  _

#1: xs.length

Please use `termination_by` to specify a decreasing measure.
```
The reason it terminates is that {anchorName mergeSortNoTerm}`splitList` always returns lists that are shorter than its input, at least when applied to lists that contain at least two elements.
Thus, the length of {anchorTerm mergeSortNoTerm}`halves.fst` and {anchorTerm mergeSortNoTerm}`halves.snd` are less than the length of {anchorName mergeSortNoTerm}`xs`.
This can be expressed using a {kw}`termination_by` clause:
```anchor mergeSortGottaProveIt
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
With this clause, the error message changes.
Instead of complaining that the function isn't structurally recursive, Lean instead points out that it was unable to automatically prove that {lit}`(splitList xs).fst.length < xs.length`:
```anchorError mergeSortGottaProveIt
failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
xs : List α
h : ¬xs.length < 2
halves : List α × List α := splitList xs
⊢ (splitList xs).fst.length < xs.length
```

# Splitting a List Makes it Shorter
%%%
tag := "splitting-shortens"
%%%

It will also be necessary to prove that {lit}`(splitList xs).snd.length < xs.length`.
Because {anchorName splitList}`splitList` alternates between adding entries to the two lists, it is easiest to prove both statements at once, so the structure of the proof can follow the algorithm used to implement {anchorName splitList}`splitList`.
In other words, it is easiest to prove that {anchorTerm splitList_shorter_bad_ty}`∀(lst : List α), (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length`.

Unfortunately, the statement is false.
In particular, {anchorTerm splitListEmpty}`splitList []` is {anchorTerm splitListEmpty}`([], [])`. Both output lists have length {anchorTerm ArrayMap (module:=Examples.ProgramsProofs.Arrays)}`0`, which is not less than {anchorTerm ArrayMap (module:=Examples.ProgramsProofs.Arrays)}`0`, the length of the input list.
Similarly, {anchorTerm splitListOne}`splitList ["basalt"]` evaluates to {anchorTerm splitListOne}`(["basalt"], [])`, and {anchorTerm splitListOne}`["basalt"]` is not shorter than {anchorTerm splitListOne}`["basalt"]`.
However, {anchorTerm splitListTwo}`splitList ["basalt", "granite"]` evaluates to {anchorTerm splitListTwo}`(["basalt"], ["granite"])`, and both of these output lists are shorter than the input list.

It turns out that the lengths of the output lists are always less than or equal to the length of the input list, but they are only strictly shorter when the input list contains at least two entries.
It turns out to be easiest to prove the former statement, then extend it to the latter statement.
Begin with a theorem statement:
```anchor splitList_shorter_le0
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  skip
```
```anchorError splitList_shorter_le0
unsolved goals
α : Type u_1
lst : List α
⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length
```
Because {anchorName splitList}`splitList` is structurally recursive on the list, the proof should use induction.
The structural recursion in {anchorName splitList}`splitList` fits a proof by induction perfectly: the base case of the induction matches the base case of the recursion, and the inductive step matches the recursive call.
The {kw}`induction` tactic gives two goals:
```anchor splitList_shorter_le1a
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => skip
  | cons x xs ih => skip
```
```anchorError splitList_shorter_le1a
unsolved goals
case nil
α : Type u_1
⊢ (splitList []).fst.length ≤ [].length ∧ (splitList []).snd.length ≤ [].length
```
```anchorError splitList_shorter_le1b
unsolved goals
case cons
α : Type u_1
x : α
xs : List α
ih : (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
⊢ (splitList (x :: xs)).fst.length ≤ (x :: xs).length ∧ (splitList (x :: xs)).snd.length ≤ (x :: xs).length
```

The goal for the {anchorName splitList_shorter_le2}`nil` case can be proved by invoking the simplifier and instructing it to unfold the definition of {anchorName splitList}`splitList`, because the length of the empty list is less than or equal to the length of the empty list.
Similarly, simplifying with {anchorName splitList}`splitList` in the {anchorName splitList_shorter_le2}`cons` case places {anchorName various}`Nat.succ` around the lengths in the goal:
```anchor splitList_shorter_le2
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
```
```anchorError splitList_shorter_le2
unsolved goals
case cons
α : Type u_1
x : α
xs : List α
ih : (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
```
This is because the call to {anchorName various}`List.length` consumes the head of the list {anchorTerm splitList}`x :: xs`, converting it to a {anchorName various}`Nat.succ`, in both the length of the input list and the length of the first output list.

Writing {anchorTerm various}`A ∧ B` in Lean is short for {anchorTerm various}`And A B`.
{anchorName And}`And` is a structure type in the {anchorTerm And}`Prop` universe:

```anchor And
structure And (a b : Prop) : Prop where
  intro ::
  left : a
  right : b
```
In other words, a proof of {anchorTerm various}`A ∧ B` consists of the {anchorName AndUse}`And.intro` constructor applied to a proof of {anchorName AndUse}`A` in the {anchorName And}`left` field and a proof of {anchorName AndUse}`B` in the {anchorName And}`right` field.

The {kw}`cases` tactic allows a proof to consider each constructor of a datatype or each potential proof of a proposition in turn.
It corresponds to a {kw}`match` expression without recursion.
Using {kw}`cases` on a structure results in the structure being broken apart, with an assumption added for each field of the structure, just as a pattern match expression extracts the field of a structure for use in a program.
Because structures have only one constructor, using {kw}`cases` on a structure does not result in additional goals.

Because {anchorName splitList_shorter_le3}`ih` is a proof of {lit}`List.length (splitList xs).fst ≤ List.length xs ∧ List.length (splitList xs).snd ≤ List.length xs`, using {anchorTerm splitList_shorter_le3}`cases ih` results in an assumption that {lit}`List.length (splitList xs).fst ≤ List.length xs` and an assumption that {lit}`List.length (splitList xs).snd ≤ List.length xs`:
```anchor splitList_shorter_le3
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
```
```anchorError splitList_shorter_le3
unsolved goals
case cons.intro
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1
```

Because the goal of the proof is also an {anchorName AndUse}`And`, the {kw}`constructor` tactic can be used to apply {anchorName AndUse}`And.intro`, resulting in a goal for each argument:
```anchor splitList_shorter_le4
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
```
```anchorError splitList_shorter_le4
unsolved goals
case cons.intro.left
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).snd.length ≤ xs.length

case cons.intro.right
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).fst.length ≤ xs.length + 1
```

The {anchorTerm splitList_shorter_le5}`left` goal is identical to the {lit}`left✝` assumption, so the {kw}`assumption` tactic dispatches it:
```anchor splitList_shorter_le5
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
    case left => assumption
```
```anchorError splitList_shorter_le5
unsolved goals
case cons.intro.right
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).fst.length ≤ xs.length + 1
```


The {anchorTerm splitList_shorter_le}`right` goal resembles the {lit}`right✝` assumption, except the goal adds a {anchorTerm le_succ_of_le}`+ 1` only to the length of the input list.
It's time to prove that the inequality holds.

## Adding One to the Greater Side
%%%
tag := "le-succ-of-le"
%%%

The inequality needed to prove {anchorName splitList_shorter_le}`splitList_shorter_le` is {anchorTerm le_succ_of_le_statement}`∀(n m : Nat), n ≤ m → n ≤ m + 1`.
The incoming assumption that {anchorTerm le_succ_of_le_statement}`n ≤ m` essentially tracks the difference between {anchorName le_succ_of_le_statement}`n` and {anchorName le_succ_of_le_statement}`m` in the number of {anchorName le_succ_of_le_apply}`Nat.le.step` constructors.
Thus, the proof should add an extra {anchorName le_succ_of_le_apply}`Nat.le.step` in the base case.

Starting out, the statement reads:
```anchor le_succ_of_le0
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  skip
```
```anchorError le_succ_of_le0
unsolved goals
n m : Nat
⊢ n ≤ m → n ≤ m + 1
```

The first step is to introduce a name for the assumption that {anchorTerm le_succ_of_le1}`n ≤ m`:
```anchor le_succ_of_le1
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
```
```anchorError le_succ_of_le1
unsolved goals
n m : Nat
h : n ≤ m
⊢ n ≤ m + 1
```

The proof is by induction on this assumption:
```anchor le_succ_of_le2a
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => skip
  | step _ ih => skip
```
In the case for {anchorName le_succ_of_le2a}`refl`, where {lit}`n = m`, the goal is to prove that {lit}`n ≤ n + 1`:
```anchorError le_succ_of_le2a
unsolved goals
case refl
n m : Nat
⊢ n ≤ n + 1
```
In the case for {anchorName le_succ_of_le2b}`step`, the goal is to prove that {anchorTerm le_succ_of_le2b}`n ≤ m + 1` under the assumption that {anchorTerm le_succ_of_le2b}`n ≤ m`:
```anchorError le_succ_of_le2b
unsolved goals
case step
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n ≤ m✝.succ + 1
```

For the {anchorName le_succ_of_le3}`refl` case, the {anchorName le_succ_of_le3}`step` constructor can be applied:
```anchor le_succ_of_le3
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor
  | step _ ih => skip
```
```anchorError le_succ_of_le3
unsolved goals
case refl.a
n m : Nat
⊢ n.le n
```
After {anchorName Nat.le_ctors}`step`, {anchorName Nat.le_ctors}`refl` can be used, which leaves only the goal for {anchorName le_succ_of_le4}`step`:
```anchor le_succ_of_le4
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor; constructor
  | step _ ih => skip
```
```anchorError le_succ_of_le4
unsolved goals
case step
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n ≤ m✝.succ + 1
```

For the step, applying the {anchorName Nat.le_ctors}`step` constructor transforms the goal into the induction hypothesis:
```anchor le_succ_of_le5
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor; constructor
  | step _ ih => constructor
```
```anchorError le_succ_of_le5
unsolved goals
case step.a
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n.le (m✝ + 1)
```

The final proof is as follows:

```anchor le_succ_of_le
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => constructor; constructor
  | step => constructor; assumption
```

To reveal what's going on behind the scenes, the {kw}`apply` and {kw}`exact` tactics can be used to indicate exactly which constructor is being applied.
The {kw}`apply` tactic solves the current goal by applying a function or constructor whose return type matches, creating new goals for each argument that was not provided, while {kw}`exact` fails if any new goals would be needed:

```anchor le_succ_of_le_apply
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
  intro h
  induction h with
  | refl => apply Nat.le.step; exact Nat.le.refl
  | step _ ih => apply Nat.le.step; exact ih
```

The proof can be golfed:

```anchor le_succ_of_le_golf
theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= by
  induction h <;> repeat (first | constructor | assumption)
```
In this short tactic script, both goals introduced by {kw}`induction` are addressed using {anchorTerm le_succ_of_le_golf}`repeat (first | constructor | assumption)`.
The tactic {lit}`first | T1 | T2 | ... | Tn` means to use try {lit}`T1` through {lit}`Tn` in order, using the first tactic that succeeds.
In other words, {anchorTerm le_succ_of_le_golf}`repeat (first | constructor | assumption)` applies constructors as long as it can, and then attempts to solve the goal using an assumption.

The proof can be shortened even further by using {tactic}`grind`, which includes a solver for linear arithmetic:

```anchor le_succ_of_le_grind
theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= by
  grind
```

Finally, the proof can be written as a recursive function:

```anchor le_succ_of_le_recursive
theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1
  | .refl => .step .refl
  | .step h => .step (Nat.le_succ_of_le h)
```

Each style of proof can be appropriate to different circumstances.
The detailed proof script is useful in cases where beginners may be reading the code, or where the steps of the proof provide some kind of insight.
The short, highly-automated proof script is typically easier to maintain, because automation is frequently both flexible and robust in the face of small changes to definitions and datatypes.
The recursive function is typically both harder to understand from the perspective of mathematical proofs and harder to maintain, but it can be a useful bridge for programmers who are beginning to work with interactive theorem proving.

## Finishing the Proof
%%%
tag := "finishing-splitList-shorter-proof"
%%%

Now that both helper theorems have been proved, the rest of {anchorName splitList_shorter_le5}`splitList_shorter_le` will be completed quickly.
The current proof state has one goal remaining:
```anchorError splitList_shorter_le5
unsolved goals
case cons.intro.right
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).fst.length ≤ xs.length + 1
```

Using {anchorName splitList_shorter_le}`Nat.le_succ_of_le` together with the {lit}`right✝` assumption completes the proof:

```anchor splitList_shorter_le
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [splitList]
  | cons x xs ih =>
    simp [splitList]
    cases ih
    constructor
    case left => assumption
    case right =>
      apply Nat.le_succ_of_le
      assumption
```

The next step is to return to the actual theorem that is needed to prove that merge sort terminates: that so long as a list has at least two entries, both results of splitting it are strictly shorter.
```anchor splitList_shorter_start
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  skip
```
```anchorError splitList_shorter_start
unsolved goals
α : Type u_1
lst : List α
x✝ : lst.length ≥ 2
⊢ (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length
```
Pattern matching works just as well in tactic scripts as it does in programs.
Because {anchorName splitList_shorter_1}`lst` has at least two entries, they can be exposed with {kw}`match`, which also refines the type through dependent pattern matching:
```anchor splitList_shorter_1
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    skip
```
```anchorError splitList_shorter_1
unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList (x :: y :: xs)).fst.length < (x :: y :: xs).length ∧
  (splitList (x :: y :: xs)).snd.length < (x :: y :: xs).length
```
Simplifying using {anchorName splitList}`splitList` removes {anchorName splitList_shorter_2}`x` and {anchorName splitList_shorter_2}`y`, resulting in the computed lengths of lists each gaining a {anchorTerm le_succ_of_le}`+ 1`:
```anchor splitList_shorter_2
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp [splitList]
```
```anchorError splitList_shorter_2
unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList xs).fst.length < xs.length + 1 ∧ (splitList xs).snd.length < xs.length + 1
```
Replacing {anchorTerm splitList_shorter_2b}`simp` with {anchorTerm splitList_shorter_2b}`simp +arith` removes these {anchorTerm le_succ_of_le}`+ 1`s, because {anchorTerm splitList_shorter_2b}`simp +arith` makes use of the fact that {anchorTerm Nat.lt_imp}`n + 1 < m + 1` implies {anchorTerm Nat.lt_imp}`n < m`:
```anchor splitList_shorter_2b
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp +arith [splitList]
```
```anchorError splitList_shorter_2b
unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
```
This goal now matches {anchorName splitList_shorter}`splitList_shorter_le`, which can be used to conclude the proof:

```anchor splitList_shorter
theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length ∧
      (splitList lst).snd.length < lst.length := by
  match lst with
  | x :: y :: xs =>
    simp +arith [splitList]
    apply splitList_shorter_le
```

The facts needed to prove that {anchorName mergeSort}`mergeSort` terminates can be pulled out of the resulting {anchorName AndUse}`And`:

```anchor splitList_shorter_sides
theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).fst.length < lst.length :=
  splitList_shorter lst h |>.left

theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) :
    (splitList lst).snd.length < lst.length :=
  splitList_shorter lst h |>.right
```

## A Simpler Proof
%%%
tag := "splitList-shorter-le-simpler-proof"
%%%


:::paragraph
Instead of using ordinary induction, {anchorName splitList_shorter_le_funInd1}`splitList_shorter_le` can be proved using functional induction, resulting in one case for each branch of {anchorName splitList}`splitList`:
```anchor splitList_shorter_le_funInd1
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList with
  | case1 => skip
  | case2 x xs a b splitEq ih => skip
```
The first case matches the base case of {anchorName splitList}`splitList`.
_Both_ applications of {anchorName splitList}`splitList` have been replaced by the result of this first branch:
```anchorError splitList_shorter_le_funInd1
unsolved goals
case case1
α : Type u_1
⊢ ([], []).fst.length ≤ [].length ∧ ([], []).snd.length ≤ [].length
```
The second case matches the recursive branch of {anchorName splitList}`splitList`.
In addition to the induction hypothesis, the value of the {anchorTerm splitList}`let` in {anchorName splitList}`splitList` is tracked in an assumption:
```anchorError splitList_shorter_le_funInd1
unsolved goals
case case2
α : Type u_1
x : α
xs a b : List α
splitEq : splitList xs = (a, b)
ih : (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
⊢ (x :: b, a).fst.length ≤ (x :: xs).length ∧ (x :: b, a).snd.length ≤ (x :: xs).length
```
:::

While the second case looks a bit complicated, everything needed to complete the proof is present.
Indeed, {tactic}`grind` can prove both goals immediately:
```anchor splitList_shorter_le_funInd2
theorem splitList_shorter_le (lst : List α) :
    (splitList lst).fst.length ≤ lst.length ∧
      (splitList lst).snd.length ≤ lst.length := by
  fun_induction splitList <;> grind
```

# Merge Sort Terminates
%%%
tag := "merge-sort-terminates"
%%%

Merge sort has two recursive calls, one for each sub-list returned by {anchorName splitList}`splitList`.
Each recursive call will require a proof that the length of the list being passed to it is shorter than the length of the input list.
It's usually convenient to write a termination proof in two steps: first, write down the propositions that will allow Lean to verify termination, and then prove them.
Otherwise, it's possible to put a lot of effort into proving the propositions, only to find out that they aren't quite what's needed to establish that the recursive calls are on smaller inputs.

The {lit}`sorry` tactic can prove any goal, even false ones.
It isn't intended for use in production code or final proofs, but it is a convenient way to “sketch out” a proof or program ahead of time.
Any definitions or theorems that use {lit}`sorry` are annotated with a warning.

The initial sketch of {anchorName mergeSortSorry}`mergeSort`'s termination argument that uses {lit}`sorry` can be written by copying the goals that Lean couldn't prove into {kw}`have`-expressions.
In Lean, {kw}`have` is similar to {kw}`let`.
When using {kw}`have`, the name is optional.
Typically, {kw}`let` is used to define names that refer to interesting values, while {kw}`have` is used to locally prove propositions that can be found when Lean is searching for evidence that an array lookup is in-bounds or that a function terminates.
```anchor mergeSortSorry
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : halves.fst.length < xs.length := by
      sorry
    have : halves.snd.length < xs.length := by
      sorry
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
The warning is located on the name {anchorName mergeSortSorry}`mergeSort`:
```anchorWarning mergeSortSorry
declaration uses 'sorry'
```
Because there are no errors, the proposed propositions are enough to establish termination.

The proofs begin by applying the helper theorems:
```anchor mergeSortNeedsGte
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : halves.fst.length < xs.length := by
      apply splitList_shorter_fst
    have : halves.snd.length < xs.length := by
      apply splitList_shorter_snd
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
Both proofs fail, because {anchorName mergeSortNeedsGte}`splitList_shorter_fst` and {anchorName mergeSortNeedsGte}`splitList_shorter_snd` both require a proof that {anchorTerm mergeSortGteStarted}`xs.length ≥ 2`:
```anchorError mergeSortNeedsGte
unsolved goals
case h
α : Type ?u.80367
inst✝ : Ord α
xs : List α
h : ¬xs.length < 2
halves : List α × List α := ⋯
⊢ xs.length ≥ 2
```
To check that this will be enough to complete the proof, add it using {lit}`sorry` and check for errors:
```anchor mergeSortGteStarted
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := by sorry
    have : halves.fst.length < xs.length := by
      apply splitList_shorter_fst
      assumption
    have : halves.snd.length < xs.length := by
      apply splitList_shorter_snd
      assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```
Once again, there is only a warning.
```anchorWarning mergeSortGteStarted
declaration uses 'sorry'
```

There is one promising assumption available: {lit}`h : ¬List.length xs < 2`, which comes from the {kw}`if`.
Clearly, if it is not the case that {anchorTerm mergeSort}`xs.length < 2`, then {anchorTerm mergeSort}`xs.length ≥ 2`.
The {anchorTerm mergeSort}`grind` tactic solves this goal, and the program is now complete:

```anchor mergeSort
def mergeSort [Ord α] (xs : List α) : List α :=
  if h : xs.length < 2 then
    match xs with
    | [] => []
    | [x] => [x]
  else
    let halves := splitList xs
    have : xs.length ≥ 2 := by
      grind
    have : halves.fst.length < xs.length := by
      apply splitList_shorter_fst
      assumption
    have : halves.snd.length < xs.length := by
      apply splitList_shorter_snd
      assumption
    merge (mergeSort halves.fst) (mergeSort halves.snd)
termination_by xs.length
```

The function can be tested on examples:
```anchor mergeSortRocks
#eval mergeSort ["soapstone", "geode", "mica", "limestone"]
```
```anchorInfo mergeSortRocks
["geode", "limestone", "mica", "soapstone"]
```
```anchor mergeSortNumbers
#eval mergeSort [5, 3, 22, 15]
```
```anchorInfo mergeSortNumbers
[3, 5, 15, 22]
```

# Division as Iterated Subtraction
%%%
tag := "division-as-iterated-subtraction"
%%%

Just as multiplication is iterated addition and exponentiation is iterated multiplication, division can be understood as iterated subtraction.
The {ref "recursive-functions"}[very first description of recursive functions in this book] presents a version of division that terminates when the divisor is not zero, but that Lean does not accept.
Proving that division terminates requires the use of a fact about inequalities.

Lean cannot prove that this definition of division terminates:
```anchor divTermination (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) : Nat :=
  if n < k then
    0
  else
    1 + div (n - k) k
```

```anchorError divTermination (module := Examples.ProgramsProofs.Div)
fail to show termination for
  div
with errors
failed to infer structural recursion:
Not considering parameter k of div:
  it is unchanged in the recursive calls
Cannot use parameter k:
  failed to eliminate recursive application
    div (n - k) k


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
k n : Nat
h✝ : ¬n < k
⊢ n - k < n
```

That's a good thing, because it doesn't!
When {anchorName divTermination (module:=Examples.ProgramsProofs.Div)}`k` is {anchorTerm divTermination (module:=Examples.ProgramsProofs.Div)}`0`, value of {anchorName divTermination (module:=Examples.ProgramsProofs.Div)}`n` does not decrease, so the program is an infinite loop.

:::paragraph
Rewriting the function to take evidence that {anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`k` is not {anchorTerm divRecursiveNeedsProof (module:=Examples.ProgramsProofs.Div)}`0` allows Lean to automatically prove termination:

```anchor divRecursiveNeedsProof (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
```
:::

This definition of {anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`div` terminates because the first argument {anchorName divRecursiveWithProof (module:=Examples.ProgramsProofs.Div)}`n` is smaller on each recursive call.
This can be expressed using a {kw}`termination_by` clause:


```anchor divRecursiveWithProof (module := Examples.ProgramsProofs.Div)
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
termination_by n
```


# Exercises
%%%
tag := "inequalities-exercises"
%%%

Prove the following theorems without using {tactic}`grind`:

 * For all natural numbers $`n`, $`0 < n + 1`.
 * For all natural numbers $`n`, $`0 \leq n`.
 * For all natural numbers $`n` and $`k`, $`(n + 1) - (k + 1) = n - k`
 * For all natural numbers $`n` and $`k`, if $`k < n` then $`n \neq 0`
 * For all natural numbers $`n`, $`n - n = 0`
 * For all natural numbers $`n` and $`k`, if $`n + 1 < k` then $`n < k`
