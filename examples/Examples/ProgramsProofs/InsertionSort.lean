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


theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) : (arr : Array α) → (isLt : i < arr.size) → (arr.size = len) → (insertSorted arr ⟨i, isLt⟩).size = len := by
  induction i with
  | zero =>
    intro arr isLt hLen
    simp [insertSorted, *]
  | succ i' ih =>
    intro arr isLt hLen
    simp [insertSorted]
    split <;> simp [*]

def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    have size_eq : (insertSorted arr { val := i, isLt := h }).size = arr.size := by
      apply insert_sorted_size_eq arr.size i arr h rfl
    have : (insertSorted arr { val := i, isLt := h }).size - (i + 1) < arr.size - i := by
      rw [size_eq]
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
