


  def insertSorted [Ord α] (arr : Array α) (i : Fin arr.size) : Array α :=
    match i with
    | ⟨0, _⟩ => arr
    | ⟨i' + 1, _⟩ =>
      have : i' < arr.size := by
        simp [Nat.lt_of_succ_lt, *]
      match Ord.compare arr[i'] arr[i] with
      | .lt | .eq => arr
      | .gt =>
        insertSorted ((dbgTraceIfShared "array to swap" arr).swap ⟨i', by assumption⟩ i) ⟨i', by simp [dbgTraceIfShared, *]⟩

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
      have : (insertSorted arr { val := i, isLt := h }).size - (i + 1) < arr.size - i := by
        rw [insert_sorted_size_eq arr.size i arr h rfl]
        simp [Nat.sub_succ_lt_self, *]
      insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
    else
      arr
  termination_by insertionSortLoop arr i => arr.size - i


 def insertionSort [Ord α] (arr : Array α) : Array α :=
    insertionSortLoop arr 0

def numbers := #[3, 1, 2]

partial def getStrings (arr : Array String) : IO (Array String) := do
  IO.println "Str?"
  let str := (← (← IO.getStdin).getLine).trim
  if str.isEmpty then
    pure arr
  else
    getStrings (arr.push str)


def main : IO Unit := do
  let strs ← getStrings #[]
  IO.println (insertionSort strs)
  IO.println strs
