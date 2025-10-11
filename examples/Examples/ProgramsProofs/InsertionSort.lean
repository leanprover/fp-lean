import ExampleSupport


/-- info:
dbgTraceIfShared.{u} {α : Type u} (s : String) (a : α) : α
-/
#check_msgs in
-- ANCHOR: dbgTraceIfSharedSig
#check dbgTraceIfShared
-- ANCHOR_END: dbgTraceIfSharedSig


discarding
/-- error:
unsolved goals
α : Type ?u.7
inst✝ : Ord α
arr : Array α
i : Fin arr.size
i' : Nat
isLt✝ : i' + 1 < arr.size
⊢ i' < arr.size
-/
#check_msgs in
-- ANCHOR: insertSortedNoProof
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted (arr.swap i' i) ⟨i', by simp [*]⟩
-- ANCHOR_END: insertSortedNoProof
stop discarding


/-- info:
Nat.lt_of_succ_lt {n m : Nat} : n.succ < m → n < m
-/
#check_msgs in
-- ANCHOR: lt_of_succ_lt_type
#check Nat.lt_of_succ_lt
-- ANCHOR_END: lt_of_succ_lt_type

-- Precondition: array positions 0 .. i-1 are sorted
-- Postcondition: array positions 0 .. i are sorted
-- ANCHOR: insertSorted
def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
  match i with
  | ⟨0, _⟩ => arr
  | ⟨i' + 1, _⟩ =>
    have : i' < arr.size := by
      grind
    match Ord.compare arr[i'] arr[i] with
    | .lt | .eq => arr
    | .gt =>
      insertSorted (arr.swap i' i) ⟨i', by simp [*]⟩
-- ANCHOR_END: insertSorted

-- theorem insert_sorted_size_eq' [Ord α] (len : Nat) (i : Nat) :
--     (arr : Array α) → (isLt : i < arr.size) →
--     arr.size = (insertSorted arr ⟨i, isLt⟩).size := by
--   induction i with
--   | zero =>
--     intro arr isLt
--     simp [insertSorted, *]
--   | succ i' ih =>
--     intro arr isLt
--     simp [insertSorted]
--     split <;> simp [*]


discarding
/-- error:
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
-/
#check_msgs in
-- ANCHOR: insert_sorted_size_eq_0
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
-- ANCHOR_END: insert_sorted_size_eq_0
stop discarding

discarding
/--
error: unsolved goals
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
-/
#check_msgs in
-- ANCHOR: insert_sorted_size_eq_1
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split
-- ANCHOR_END: insert_sorted_size_eq_1
stop discarding


discarding
/--
error: unsolved goals
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
-/
#check_msgs in
-- ANCHOR: insert_sorted_size_eq_2
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split <;> try rfl
-- ANCHOR_END: insert_sorted_size_eq_2
stop discarding

discarding
/--
error: unsolved goals
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
-/
#check_msgs in
-- ANCHOR: insert_sorted_size_eq_3
theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  match i with
  | ⟨j, isLt⟩ =>
    induction j generalizing arr with
    | zero => simp [insertSorted]
    | succ j' ih =>
      simp [insertSorted]
      split <;> try rfl
-- ANCHOR_END: insert_sorted_size_eq_3
stop discarding

discarding
/--
error: unsolved goals
case case1
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
isLt : 0 < arr.size
⊢ arr.size = arr.size
---
error: unsolved goals
case case2
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
i : Nat
isLt✝ : i + 1 < arr.size
this : i < arr.size
isLt : compare arr[i] arr[⟨i.succ, isLt✝⟩] = Ordering.lt
⊢ (match compare arr[i] arr[⟨i.succ, isLt✝⟩] with
      | Ordering.lt => arr
      | Ordering.eq => arr
      | Ordering.gt => insertSorted (arr.swap i (↑⟨i.succ, isLt✝⟩) this ⋯) ⟨i, ⋯⟩).size =
    arr.size
---
error: unsolved goals
case case3
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
i : Nat
isLt : i + 1 < arr.size
this : i < arr.size
isEq : compare arr[i] arr[⟨i.succ, isLt⟩] = Ordering.eq
⊢ (match compare arr[i] arr[⟨i.succ, isLt⟩] with
      | Ordering.lt => arr
      | Ordering.eq => arr
      | Ordering.gt => insertSorted (arr.swap i (↑⟨i.succ, isLt⟩) this ⋯) ⟨i, ⋯⟩).size =
    arr.size
---
error: unsolved goals
case case4
α : Type u_1
inst✝ : Ord α
arr✝ arr : Array α
i : Nat
isLt : i + 1 < arr.size
this : i < arr.size
isGt : compare arr[i] arr[⟨i.succ, isLt⟩] = Ordering.gt
ih : (insertSorted (arr.swap i (↑⟨i.succ, isLt⟩) this ⋯) ⟨i, ⋯⟩).size = (arr.swap i (↑⟨i.succ, isLt⟩) this ⋯).size
⊢ (match compare arr[i] arr[⟨i.succ, isLt⟩] with
      | Ordering.lt => arr
      | Ordering.eq => arr
      | Ordering.gt => insertSorted (arr.swap i (↑⟨i.succ, isLt⟩) this ⋯) ⟨i, ⋯⟩).size =
    arr.size
-/
#check_msgs in
-- ANCHOR: insert_sorted_size_eq_funInd1
theorem insert_sorted_size_eq [Ord α]
    (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  fun_induction insertSorted with
  | case1 arr isLt => skip
  | case2 arr i isLt this isLt => skip
  | case3 arr i isLt this isEq => skip
  | case4 arr i isLt this isGt ih => skip
-- ANCHOR_END: insert_sorted_size_eq_funInd1
stop discarding


-- ANCHOR: insert_sorted_size_eq_funInd
theorem insert_sorted_size_eq [Ord α]
    (arr : Array α) (i : Fin arr.size) :
    (insertSorted arr i).size = arr.size := by
  fun_induction insertSorted <;> grind [Array.size_swap]
-- ANCHOR_END: insert_sorted_size_eq_funInd

discarding
/--
error: fail to show termination for
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
1) 324:4-55   ? ?  ?

#1: arr.size - i

Please use `termination_by` to specify a decreasing measure.
-/
#check_msgs in
-- ANCHOR: insertionSortLoopTermination
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
-- ANCHOR_END: insertionSortLoopTermination
stop discarding

namespace Partial

-- ANCHOR: partialInsertionSortLoop
partial def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
-- ANCHOR_END: partialInsertionSortLoop


/-- info:
#[3, 5, 8, 17]
-/
#check_msgs in
-- ANCHOR: insertionSortPartialOne
#eval insertionSortLoop #[5, 17, 3, 8] 0
-- ANCHOR_END: insertionSortPartialOne

/-- info:
#["igneous", "metamorphic", "sedimentary"]
-/
#check_msgs in
-- ANCHOR: insertionSortPartialTwo
#eval insertionSortLoop #["metamorphic", "igneous", "sedimentary"] 0
-- ANCHOR_END: insertionSortPartialTwo
end Partial

discarding
/-- error:
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
-/
#check_msgs in
-- ANCHOR: insertionSortLoopProof1
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
-- ANCHOR_END: insertionSortLoopProof1
stop discarding


discarding
/--
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
---
warning: declaration uses 'sorry'
-/
#check_msgs in
--ANCHOR: insertionSortLoopSorry
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      sorry
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
--ANCHOR_END: insertionSortLoopSorry
stop discarding

discarding
/-- error:
unsolved goals
α : Type ?u.23737
inst✝ : Ord α
arr : Array α
i : Nat
h : i < arr.size
⊢ arr.size - (i + 1) < arr.size - i
-/
#check_msgs in
-- ANCHOR: insertionSortLoopRw
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      rw [insert_sorted_size_eq]
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
-- ANCHOR_END: insertionSortLoopRw
stop discarding

-- ANCHOR: sub_succ_lt_self_type
example : ∀ (a i : Nat), i < a → a - (i + 1) < a - i := Nat.sub_succ_lt_self
-- ANCHOR_END: sub_succ_lt_self_type


-- ANCHOR: insertionSortLoop
def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
      grind [insert_sorted_size_eq]
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by arr.size - i
-- ANCHOR_END: insertionSortLoop

-- ANCHOR: insertionSort
def insertionSort [Ord α] (arr : Array α) : Array α :=
   insertionSortLoop arr 0
-- ANCHOR_END: insertionSort

-- ANCHOR: names

example := @List.map
example := @Array.swap
example := (@Array.swap : {α : Type _} → (xs : Array α) → (i j : Nat) → (h1 : autoParam (i < xs.size) _) → (h2 : autoParam (j < xs.size) _) → Array α)
example : Fin 1 := {val := 0, isLt := by grind}
example := @Array.set
example {n} := Fin n
example := Fin 0
section
variable (arr : Array α)
example := Fin arr.size
example := OfNat
/-- warning: declaration uses 'sorry' -/
#guard_msgs in
theorem ohNoNotReallyTrue : 3 < 2 := by sorry
end
-- ANCHOR_END: names


/-- info:
#[1, 3, 4, 7]
-/
#check_msgs in
-- ANCHOR: insertionSortNums
#eval insertionSort #[3, 1, 7, 4]
-- ANCHOR_END: insertionSortNums


/-- info:
#["granite", "hematite", "marble", "quartz"]
-/
#check_msgs in
-- ANCHOR: insertionSortStrings
#eval insertionSort #[ "quartz", "marble", "granite", "hematite"]
-- ANCHOR_END: insertionSortStrings


--ANCHOR: etc
example := @Array.map
--ANCHOR_END: etc
