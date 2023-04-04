import Examples.Support


expect info {{{ dbgTraceIfSharedSig }}}
  #check dbgTraceIfShared
message
"dbgTraceIfShared.{u} {α : Type u} (s : String) (a : α) : α"
end expect



expect error {{{ insertSortedNoProof }}}
  def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
    match i with
    | ⟨0, _⟩ => arr
    | ⟨i' + 1, _⟩ =>
      have : i' < arr.size := by
        skip
      match Ord.compare arr[i'] arr[i] with
      | .lt | .eq => arr
      | .gt =>
        insertSorted (arr.swap ⟨i', by assumption⟩ i) ⟨i', by simp [*]⟩
message
"unsolved goals
α : Type ?u.7
inst✝ : Ord α
arr : Array α
i : Fin (Array.size arr)
i' : Nat
isLt✝ : i' + 1 < Array.size arr
⊢ i' < Array.size arr"
end expect


expect info {{{ lt_of_succ_lt_type }}}
  #check Nat.lt_of_succ_lt
message
"Nat.lt_of_succ_lt {n m : Nat} (a✝ : Nat.succ n < m) : n < m"
end expect

-- Precondition: array positions 0 .. i-1 are sorted
-- Postcondition: array positions 0 .. i are sorted
book declaration {{{ insertSorted }}}
  def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
    match i with
    | ⟨0, _⟩ => arr
    | ⟨i' + 1, _⟩ =>
      have : i' < arr.size := by
        simp [Nat.lt_of_succ_lt, *]
      match Ord.compare arr[i'] arr[i] with
      | .lt | .eq => arr
      | .gt =>
        insertSorted (arr.swap ⟨i', by assumption⟩ i) ⟨i', by simp [*]⟩
stop book declaration

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


expect error {{{ insertionSortLoopTermination }}}
  def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
    if h : i < arr.size then
      insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
    else
      arr
message
"fail to show termination for
  insertionSortLoop
with errors
argument #4 was not used for structural recursion
  failed to eliminate recursive application
    insertionSortLoop (insertSorted arr { val := i, isLt := h }) (i + 1)

structural recursion cannot be used

failed to prove termination, use `termination_by` to specify a well-founded relation"
end expect

namespace Partial

book declaration {{{ partialInsertionSortLoop }}}
  partial def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
    if h : i < arr.size then
      insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
    else
      arr
stop book declaration


expect info {{{ insertionSortPartialOne }}}
  #eval insertionSortLoop #[5, 17, 3, 8] 0
message
"#[3, 5, 8, 17]"
end expect

expect info {{{ insertionSortPartialTwo }}}
  #eval insertionSortLoop #["metamorphic", "igneous", "sedentary"] 0
message
"#[\"igneous\", \"metamorphic\", \"sedentary\"]"
end expect
end Partial


expect error {{{ insertionSortLoopProof1 }}}
  def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
    if h : i < arr.size then
      insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
    else
      arr
  termination_by insertionSortLoop arr i => arr.size - i
message
"failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Nat
h : i < Array.size arr
⊢ Array.size (insertSorted arr { val := i, isLt := h }) - (i + 1) < Array.size arr - i"
end expect

def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have : (insertSorted arr { val := i, isLt := h }).size - (i + 1) < arr.size - i := by
      rw [insert_sorted_size_eq arr.size i arr h rfl]
      simp [Nat.sub_succ_lt_self, *]
    insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
  else
    arr
termination_by insertionSortLoop arr i => arr.size - i

def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0

#eval insertionSort #[3, 1, 7, 4]

-- namespace Instrumented

-- def insertSorted [Ord α] (arr : Array α) (i : Nat) (_ : i < arr.size) : Array α :=
--   match i with
--   | 0 => arr
--   | i' + 1 =>
--     have : i' < arr.size := by
--       simp [Nat.lt_of_succ_lt, *]
--     match Ord.compare arr[i'] arr[i' + 1] with
--     | .lt | .eq => arr
--     | .gt =>
--       let j : Fin arr.size := ⟨i', by assumption⟩
--       let j' : Fin arr.size := ⟨i' + 1, by assumption⟩
--       insertSorted ((dbgTraceIfShared "shared" arr).swap j j') i' (by simp [dbgTraceIfShared, *])

-- partial def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
--   if h : i < arr.size then
--     insertionSortLoop (insertSorted arr i h) (i + 1)
--   else
--     arr

-- def insertionSort [Ord α] (arr : Array α) : Array α :=
--   insertionSortLoop arr 0

-- -- #eval insertionSort #[1,2,3]
-- -- def foo := #[3, 1, 2]
-- -- #eval insertionSort foo

-- end Instrumented
