import Examples.Support



-- Precondition: array positions 0 .. i-1 are sorted
-- Postcondition: array positions 0 .. i are sorted
def insertSorted [Ord α] (arr : Array α) (i : Nat) (_ : i < arr.size) : Array α :=
  match i with
  | 0 => arr
  | i' + 1 =>
    have : i' < arr.size := by
      simp [Nat.lt_of_succ_lt, *]
    match Ord.compare arr[i'] arr[i' + 1] with
    | .lt | .eq => arr
    | .gt =>
      let j : Fin arr.size := ⟨i', by assumption⟩
      let j' : Fin arr.size := ⟨i' + 1, by assumption⟩
      insertSorted (arr.swap j j') i' (by simp [*])

partial def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr i h) (i + 1)
  else
    arr

def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0

namespace Instrumented

def insertSorted [Ord α] (arr : Array α) (i : Nat) (_ : i < arr.size) : Array α :=
  match i with
  | 0 => arr
  | i' + 1 =>
    have : i' < arr.size := by
      simp [Nat.lt_of_succ_lt, *]
    match Ord.compare arr[i'] arr[i' + 1] with
    | .lt | .eq => arr
    | .gt =>
      let j : Fin arr.size := ⟨i', by assumption⟩
      let j' : Fin arr.size := ⟨i' + 1, by assumption⟩
      insertSorted ((dbgTraceIfShared "shared" arr).swap j j') i' (by simp [dbgTraceIfShared, *])

partial def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
  if h : i < arr.size then
    insertionSortLoop (insertSorted arr i h) (i + 1)
  else
    arr

def insertionSort [Ord α] (arr : Array α) : Array α :=
  insertionSortLoop arr 0

#eval insertionSort #[1,2,3]
def foo := #[3, 1, 2]
#eval insertionSort foo

end Instrumented
