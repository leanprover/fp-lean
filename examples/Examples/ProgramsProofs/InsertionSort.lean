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



expect error {{{ insert_sorted_size_eq_0 }}}
  theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
      (insertSorted arr i).size = arr.size := by
    match i with
    | ⟨j, isLt⟩ =>
      induction j with
      | zero => simp [insertSorted]
      | succ j' ih =>
        simp [insertSorted]
message
"unsolved goals
case succ
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin (Array.size arr)
j' : Nat
ih : ∀ (isLt : j' < Array.size arr), Array.size (insertSorted arr { val := j', isLt := isLt }) = Array.size arr
isLt : Nat.succ j' < Array.size arr
⊢ Array.size
      (match compare arr[j'] arr[{ val := Nat.succ j', isLt := isLt }] with
      | Ordering.lt => arr
      | Ordering.eq => arr
      | Ordering.gt =>
        insertSorted
          (Array.swap arr { val := j', isLt := (_ : j' < Array.size arr) } { val := Nat.succ j', isLt := isLt })
          { val := j',
            isLt :=
              (_ :
                j' <
                  Array.size
                    (Array.swap arr { val := j', isLt := (_ : j' < Array.size arr) }
                      { val := Nat.succ j', isLt := isLt })) }) =
    Array.size arr"
end expect


expect error {{{ insert_sorted_size_eq_1 }}}
  theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
      (insertSorted arr i).size = arr.size := by
    match i with
    | ⟨j, isLt⟩ =>
      induction j with
      | zero => simp [insertSorted]
      | succ j' ih =>
        simp [insertSorted]
        split
message
"unsolved goals
case succ.h_1
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin (Array.size arr)
j' : Nat
ih : ∀ (isLt : j' < Array.size arr), Array.size (insertSorted arr { val := j', isLt := isLt }) = Array.size arr
isLt : Nat.succ j' < Array.size arr
x✝ : Ordering
heq✝ : compare arr[j'] arr[{ val := Nat.succ j', isLt := isLt }] = Ordering.lt
⊢ Array.size arr = Array.size arr

case succ.h_2
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin (Array.size arr)
j' : Nat
ih : ∀ (isLt : j' < Array.size arr), Array.size (insertSorted arr { val := j', isLt := isLt }) = Array.size arr
isLt : Nat.succ j' < Array.size arr
x✝ : Ordering
heq✝ : compare arr[j'] arr[{ val := Nat.succ j', isLt := isLt }] = Ordering.eq
⊢ Array.size arr = Array.size arr

case succ.h_3
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin (Array.size arr)
j' : Nat
ih : ∀ (isLt : j' < Array.size arr), Array.size (insertSorted arr { val := j', isLt := isLt }) = Array.size arr
isLt : Nat.succ j' < Array.size arr
x✝ : Ordering
heq✝ : compare arr[j'] arr[{ val := Nat.succ j', isLt := isLt }] = Ordering.gt
⊢ Array.size
      (insertSorted
        (Array.swap arr { val := j', isLt := (_ : j' < Array.size arr) } { val := Nat.succ j', isLt := isLt })
        { val := j',
          isLt :=
            (_ :
              j' <
                Array.size
                  (Array.swap arr { val := j', isLt := (_ : j' < Array.size arr) }
                    { val := Nat.succ j', isLt := isLt })) }) =
    Array.size arr"
end expect


expect error {{{ insert_sorted_size_eq_2 }}}
  theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
      (insertSorted arr i).size = arr.size := by
    match i with
    | ⟨j, isLt⟩ =>
      induction j with
      | zero => simp [insertSorted]
      | succ j' ih =>
        simp [insertSorted]
        split <;> try rfl
message
"unsolved goals
case succ.h_3
α : Type u_1
inst✝ : Ord α
arr : Array α
i : Fin (Array.size arr)
j' : Nat
ih : ∀ (isLt : j' < Array.size arr), Array.size (insertSorted arr { val := j', isLt := isLt }) = Array.size arr
isLt : Nat.succ j' < Array.size arr
x✝ : Ordering
heq✝ : compare arr[j'] arr[{ val := Nat.succ j', isLt := isLt }] = Ordering.gt
⊢ Array.size
      (insertSorted
        (Array.swap arr { val := j', isLt := (_ : j' < Array.size arr) } { val := Nat.succ j', isLt := isLt })
        { val := j',
          isLt :=
            (_ :
              j' <
                Array.size
                  (Array.swap arr { val := j', isLt := (_ : j' < Array.size arr) }
                    { val := Nat.succ j', isLt := isLt })) }) =
    Array.size arr"
end expect


expect error {{{ insert_sorted_size_eq_3 }}}
  theorem insert_sorted_size_eq [Ord α] (arr : Array α) (i : Fin arr.size) :
      (insertSorted arr i).size = arr.size := by
    match i with
    | ⟨j, isLt⟩ =>
      induction j generalizing arr with
      | zero => simp [insertSorted]
      | succ j' ih =>
        simp [insertSorted]
        split <;> try rfl
message
"unsolved goals
case succ.h_3
α : Type u_1
inst✝ : Ord α
j' : Nat
ih :
  ∀ (arr : Array α),
    Fin (Array.size arr) →
      ∀ (isLt : j' < Array.size arr), Array.size (insertSorted arr { val := j', isLt := isLt }) = Array.size arr
arr : Array α
i : Fin (Array.size arr)
isLt : Nat.succ j' < Array.size arr
x✝ : Ordering
heq✝ : compare arr[j'] arr[{ val := Nat.succ j', isLt := isLt }] = Ordering.gt
⊢ Array.size
      (insertSorted
        (Array.swap arr { val := j', isLt := (_ : j' < Array.size arr) } { val := Nat.succ j', isLt := isLt })
        { val := j',
          isLt :=
            (_ :
              j' <
                Array.size
                  (Array.swap arr { val := j', isLt := (_ : j' < Array.size arr) }
                    { val := Nat.succ j', isLt := isLt })) }) =
    Array.size arr"
end expect


expect error {{{ insert_sorted_size_eq_redo_0 }}}
  theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
      (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
      (insertSorted arr ⟨i, isLt⟩).size = len := by
    skip
message
"unsolved goals
α : Type u_1
inst✝ : Ord α
len i : Nat
⊢ ∀ (arr : Array α) (isLt : i < Array.size arr),
    Array.size arr = len → Array.size (insertSorted arr { val := i, isLt := isLt }) = len"
end expect


expect error {{{ insert_sorted_size_eq_redo_1a }}}
  theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
      (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
      (insertSorted arr ⟨i, isLt⟩).size = len := by
    induction i with
    | zero => skip
    | succ i' ih => skip
message
"unsolved goals
case zero
α : Type u_1
inst✝ : Ord α
len : Nat
⊢ ∀ (arr : Array α) (isLt : Nat.zero < Array.size arr),
    Array.size arr = len → Array.size (insertSorted arr { val := Nat.zero, isLt := isLt }) = len"
end expect

expect error {{{ insert_sorted_size_eq_redo_1b }}}
  theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
      (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
      (insertSorted arr ⟨i, isLt⟩).size = len := by
    induction i with
    | zero => skip
    | succ i' ih => skip
message
"unsolved goals
case succ
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih :
  ∀ (arr : Array α) (isLt : i' < Array.size arr),
    Array.size arr = len → Array.size (insertSorted arr { val := i', isLt := isLt }) = len
⊢ ∀ (arr : Array α) (isLt : Nat.succ i' < Array.size arr),
    Array.size arr = len → Array.size (insertSorted arr { val := Nat.succ i', isLt := isLt }) = len"
end expect


expect error {{{ insert_sorted_size_eq_redo_2 }}}
  theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
      (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
      (insertSorted arr ⟨i, isLt⟩).size = len := by
    induction i with
    | zero =>
      intro arr isLt hLen
      simp [insertSorted]
    | succ i' ih => skip
message
"unsolved goals
case zero
α : Type u_1
inst✝ : Ord α
len : Nat
arr : Array α
isLt : Nat.zero < Array.size arr
hLen : Array.size arr = len
⊢ Array.size arr = len"
end expect


expect error {{{ insert_sorted_size_eq_redo_2b }}}
  theorem insert_sorted_size_eq [Ord α] (len : Nat) (i : Nat) :
      (arr : Array α) → (isLt : i < arr.size) → arr.size = len →
      (insertSorted arr ⟨i, isLt⟩).size = len := by
    induction i with
    | zero =>
      intro arr isLt hLen
      simp [insertSorted, *]
    | succ i' ih => skip
message
"unsolved goals
case succ
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih :
  ∀ (arr : Array α) (isLt : i' < Array.size arr),
    Array.size arr = len → Array.size (insertSorted arr { val := i', isLt := isLt }) = len
⊢ ∀ (arr : Array α) (isLt : Nat.succ i' < Array.size arr),
    Array.size arr = len → Array.size (insertSorted arr { val := Nat.succ i', isLt := isLt }) = len"
end expect


expect error {{{ insert_sorted_size_eq_redo_3 }}}
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
message
"unsolved goals
case succ
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih :
  ∀ (arr : Array α) (isLt : i' < Array.size arr),
    Array.size arr = len → Array.size (insertSorted arr { val := i', isLt := isLt }) = len
arr : Array α
isLt : Nat.succ i' < Array.size arr
hLen : Array.size arr = len
⊢ Array.size
      (match compare arr[i'] arr[{ val := Nat.succ i', isLt := isLt }] with
      | Ordering.lt => arr
      | Ordering.eq => arr
      | Ordering.gt =>
        insertSorted
          (Array.swap arr { val := i', isLt := (_ : i' < Array.size arr) } { val := Nat.succ i', isLt := isLt })
          { val := i',
            isLt :=
              (_ :
                i' <
                  Array.size
                    (Array.swap arr { val := i', isLt := (_ : i' < Array.size arr) }
                      { val := Nat.succ i', isLt := isLt })) }) =
    len"
end expect


expect error {{{ insert_sorted_size_eq_redo_4 }}}
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
message
"unsolved goals
case succ.h_1
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih :
  ∀ (arr : Array α) (isLt : i' < Array.size arr),
    Array.size arr = len → Array.size (insertSorted arr { val := i', isLt := isLt }) = len
arr : Array α
isLt : Nat.succ i' < Array.size arr
hLen : Array.size arr = len
x✝ : Ordering
heq✝ : compare arr[i'] arr[{ val := Nat.succ i', isLt := isLt }] = Ordering.lt
⊢ Array.size arr = len

case succ.h_2
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih :
  ∀ (arr : Array α) (isLt : i' < Array.size arr),
    Array.size arr = len → Array.size (insertSorted arr { val := i', isLt := isLt }) = len
arr : Array α
isLt : Nat.succ i' < Array.size arr
hLen : Array.size arr = len
x✝ : Ordering
heq✝ : compare arr[i'] arr[{ val := Nat.succ i', isLt := isLt }] = Ordering.eq
⊢ Array.size arr = len

case succ.h_3
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih :
  ∀ (arr : Array α) (isLt : i' < Array.size arr),
    Array.size arr = len → Array.size (insertSorted arr { val := i', isLt := isLt }) = len
arr : Array α
isLt : Nat.succ i' < Array.size arr
hLen : Array.size arr = len
x✝ : Ordering
heq✝ : compare arr[i'] arr[{ val := Nat.succ i', isLt := isLt }] = Ordering.gt
⊢ Array.size
      (insertSorted
        (Array.swap arr { val := i', isLt := (_ : i' < Array.size arr) } { val := Nat.succ i', isLt := isLt })
        { val := i',
          isLt :=
            (_ :
              i' <
                Array.size
                  (Array.swap arr { val := i', isLt := (_ : i' < Array.size arr) }
                    { val := Nat.succ i', isLt := isLt })) }) =
    len"
end expect


expect error {{{ insert_sorted_size_eq_redo_5 }}}
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
message
"unsolved goals
case succ.h_3
α : Type u_1
inst✝ : Ord α
len i' : Nat
ih :
  ∀ (arr : Array α) (isLt : i' < Array.size arr),
    Array.size arr = len → Array.size (insertSorted arr { val := i', isLt := isLt }) = len
arr : Array α
isLt : Nat.succ i' < Array.size arr
hLen : Array.size arr = len
x✝ : Ordering
heq✝ : compare arr[i'] arr[{ val := Nat.succ i', isLt := isLt }] = Ordering.gt
⊢ Array.size
      (insertSorted
        (Array.swap arr { val := i', isLt := (_ : i' < Array.size arr) } { val := Nat.succ i', isLt := isLt })
        { val := i',
          isLt :=
            (_ :
              i' <
                Array.size
                  (Array.swap arr { val := i', isLt := (_ : i' < Array.size arr) }
                    { val := Nat.succ i', isLt := isLt })) }) =
    len"
end expect

namespace Wak

expect error {{{ isnert_sorted_size_eq_partial_redo }}}
  theorem insert_sorted_size_eq [Ord α] (i : Nat) :
      (arr : Array α) → (isLt : i < arr.size) →
      arr.size = (insertSorted arr ⟨i, isLt⟩).size := by
    induction i with
    | zero =>
      intro arr isLt
      simp [insertSorted, *]
    | succ i' ih =>
      intro arr isLt
      simp [insertSorted]
      split <;> try assumption
      simp [*]
message
"unsolved goals
case succ.h_2
α : Type u_1
inst✝ : Ord α
i' : Nat
ih :
  ∀ (arr : Array α) (isLt : i' < Array.size arr),
    Array.size arr = Array.size (insertSorted arr { val := i', isLt := isLt })
arr : Array α
isLt : Nat.succ i' < Array.size arr
x✝ : Ordering
heq✝ : compare arr[i'] arr[{ val := Nat.succ i', isLt := isLt }] = Ordering.eq
⊢ Array.size arr = Array.size arr

case succ.h_3
α : Type u_1
inst✝ : Ord α
i' : Nat
ih :
  ∀ (arr : Array α) (isLt : i' < Array.size arr),
    Array.size arr = Array.size (insertSorted arr { val := i', isLt := isLt })
arr : Array α
isLt : Nat.succ i' < Array.size arr
x✝ : Ordering
heq✝ : compare arr[i'] arr[{ val := Nat.succ i', isLt := isLt }] = Ordering.gt
⊢ Array.size arr =
    Array.size
      (insertSorted
        (Array.swap arr { val := i', isLt := (_ : i' < Array.size arr) } { val := Nat.succ i', isLt := isLt })
        { val := i',
          isLt :=
            (_ :
              i' <
                Array.size
                  (Array.swap arr { val := i', isLt := (_ : i' < Array.size arr) }
                    { val := Nat.succ i', isLt := isLt })) })"
end expect
end Wak

namespace Alt


book declaration {{{ insert_sorted_size_eq_redo_6 }}}
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
stop book declaration
end Alt


book declaration {{{ insert_sorted_size_eq_redo }}}
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
stop book declaration

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




expect warning {{{ insertionSortLoopSorry }}}
  def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
    if h : i < arr.size then
      have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
        sorry
      insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
    else
      arr
  termination_by insertionSortLoop arr i => arr.size - i
message
"declaration uses 'sorry'"
end expect


expect error {{{ insertionSortLoopRw }}}
  def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
    if h : i < arr.size then
      have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
        rw [insert_sorted_size_eq arr.size i arr h rfl]
      insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
    else
      arr
termination_by insertionSortLoop arr i => arr.size - i
message
"unsolved goals
α : Type ?u.22173
inst✝ : Ord α
arr : Array α
i : Nat
h : i < Array.size arr
⊢ Array.size arr - (i + 1) < Array.size arr - i"
end expect

bookExample type {{{ sub_succ_lt_self_type }}}
  Nat.sub_succ_lt_self
  ===>
  ∀ (a i : Nat), i < a → a - (i + 1) < a - i
end bookExample



book declaration {{{ insertionSortLoop }}}
  def insertionSortLoop [Ord α] (arr : Array α) (i : Nat) : Array α :=
    if h : i < arr.size then
      have : (insertSorted arr ⟨i, h⟩).size - (i + 1) < arr.size - i := by
        rw [insert_sorted_size_eq arr.size i arr h rfl]
        simp [Nat.sub_succ_lt_self, *]
      insertionSortLoop (insertSorted arr ⟨i, h⟩) (i + 1)
    else
      arr
  termination_by insertionSortLoop arr i => arr.size - i
stop book declaration


book declaration {{{ insertionSort }}}
 def insertionSort [Ord α] (arr : Array α) : Array α :=
    insertionSortLoop arr 0
stop book declaration


expect info {{{ insertionSortNums }}}
  #eval insertionSort #[3, 1, 7, 4]
message
"#[1, 3, 4, 7]"
end expect


expect info {{{ insertionSortStrings }}}
  #eval insertionSort #[ "quartz", "marble", "granite", "hematite"]
message
"#[\"granite\", \"hematite\", \"marble\", \"quartz\"]"
end expect

