import Examples.Support



book declaration {{{ merge }}}
  def merge [Ord α] (xs : List α) (ys : List α) : List α :=
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x'::xs', y'::ys' =>
      match Ord.compare x' y' with
      | .lt | .eq => x' :: merge xs' (y' :: ys')
      | .gt => y' :: merge (x'::xs') ys'
stop book declaration


book declaration {{{ splitList }}}
  def splitList (lst : List α) : (List α × List α) :=
    match lst with
    | [] => ([], [])
    | x :: xs =>
      let (a, b) := splitList xs
      (x :: b, a)
stop book declaration


expect error {{{ mergeSortNoTerm }}}
  def mergeSort [Ord α] (xs : List α) : List α :=
    if h : xs.length < 2 then
      match xs with
      | [] => []
      | [x] => [x]
    else
      let halves := splitList xs
      merge (mergeSort halves.fst) (mergeSort halves.snd)
message
"fail to show termination for
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


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
xs : List α
h : ¬xs.length < 2
halves : List α × List α := splitList xs
⊢ sizeOf (splitList xs).fst < sizeOf xs"
end expect



expect error {{{ mergeSortGottaProveIt }}}
  def mergeSort [Ord α] (xs : List α) : List α :=
    if h : xs.length < 2 then
      match xs with
      | [] => []
      | [x] => [x]
    else
      let halves := splitList xs
      merge (mergeSort halves.fst) (mergeSort halves.snd)
  termination_by xs.length
message
"failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
xs : List α
h : ¬xs.length < 2
halves : List α × List α := splitList xs
⊢ (splitList xs).fst.length < xs.length"
end expect

bookExample {{{ splitListEmpty }}}
  splitList []
  ===>
  ([], [])
end bookExample

bookExample {{{ splitListOne }}}
  splitList ["basalt"]
  ===>
  (["basalt"], [])
end bookExample

bookExample {{{ splitListTwo }}}
  splitList ["basalt", "granite"]
  ===>
  (["basalt"], ["granite"])
end bookExample


expect error {{{ splitList_shorter_le0 }}}
  theorem splitList_shorter_le (lst : List α) :
      (splitList lst).fst.length ≤ lst.length ∧
        (splitList lst).snd.length ≤ lst.length := by
    skip
message
"unsolved goals
α : Type u_1
lst : List α
⊢ (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length"
end expect



expect error {{{ splitList_shorter_le1a }}}
  theorem splitList_shorter_le (lst : List α) :
      (splitList lst).fst.length ≤ lst.length ∧
        (splitList lst).snd.length ≤ lst.length := by
    induction lst with
    | nil => skip
    | cons x xs ih => skip
message
"unsolved goals
case nil
α : Type u_1
⊢ (splitList []).fst.length ≤ [].length ∧ (splitList []).snd.length ≤ [].length"
end expect

expect error {{{ splitList_shorter_le1b }}}
  theorem splitList_shorter_le (lst : List α) :
      (splitList lst).fst.length ≤ lst.length ∧
        (splitList lst).snd.length ≤ lst.length := by
    induction lst with
    | nil => skip
    | cons x xs ih => skip
message
"unsolved goals
case cons
α : Type u_1
x : α
xs : List α
ih : (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
⊢ (splitList (x :: xs)).fst.length ≤ (x :: xs).length ∧ (splitList (x :: xs)).snd.length ≤ (x :: xs).length"
end expect


expect error {{{ splitList_shorter_le2 }}}
  theorem splitList_shorter_le (lst : List α) :
      (splitList lst).fst.length ≤ lst.length ∧
        (splitList lst).snd.length ≤ lst.length := by
    induction lst with
    | nil => simp [splitList]
    | cons x xs ih =>
      simp [splitList]
message
"unsolved goals
case cons
α : Type u_1
x : α
xs : List α
ih : (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1"
end expect


namespace AndDef

book declaration {{{ And }}}
  structure And (a b : Prop) : Prop where
    intro ::
    left : a
    right : b
stop book declaration

end AndDef


expect error {{{ splitList_shorter_le3 }}}
  theorem splitList_shorter_le (lst : List α) :
      (splitList lst).fst.length ≤ lst.length ∧
        (splitList lst).snd.length ≤ lst.length := by
    induction lst with
    | nil => simp [splitList]
    | cons x xs ih =>
      simp [splitList]
      cases ih
message
"unsolved goals
case cons.intro
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).snd.length ≤ xs.length ∧ (splitList xs).fst.length ≤ xs.length + 1"
end expect


expect error {{{ splitList_shorter_le4 }}}
  theorem splitList_shorter_le (lst : List α) :
      (splitList lst).fst.length ≤ lst.length ∧
        (splitList lst).snd.length ≤ lst.length := by
    induction lst with
    | nil => simp [splitList]
    | cons x xs ih =>
      simp [splitList]
      cases ih
      constructor
message
"unsolved goals
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
⊢ (splitList xs).fst.length ≤ xs.length + 1"
end expect

expect error {{{ splitList_shorter_le5 }}}
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
message
"unsolved goals
case cons.intro.right
α : Type u_1
x : α
xs : List α
left✝ : (splitList xs).fst.length ≤ xs.length
right✝ : (splitList xs).snd.length ≤ xs.length
⊢ (splitList xs).fst.length ≤ xs.length + 1"
end expect

namespace Extras

expect error {{{ le_succ_of_le0 }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
    skip
message
"unsolved goals
n m : Nat
⊢ n ≤ m → n ≤ m + 1"
end expect

expect error {{{ le_succ_of_le1 }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
    intro h
message
"unsolved goals
n m : Nat
h : n ≤ m
⊢ n ≤ m + 1"
end expect

expect error {{{ le_succ_of_le2a }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
    intro h
    induction h with
    | refl => skip
    | step _ ih => skip
message
"unsolved goals
case refl
n m : Nat
⊢ n ≤ n + 1"
end expect

expect error {{{ le_succ_of_le2b }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
    intro h
    induction h with
    | refl => skip
    | step _ ih => skip
message
"unsolved goals
case step
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n ≤ m✝.succ + 1"
end expect

expect error {{{ le_succ_of_le3 }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
    intro h
    induction h with
    | refl => constructor
    | step _ ih => skip
message
"unsolved goals
case refl.a
n m : Nat
⊢ n.le n"
end expect

expect error {{{ le_succ_of_le4 }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
    intro h
    induction h with
    | refl => constructor; constructor
    | step _ ih => skip
message
"unsolved goals
case step
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n ≤ m✝.succ + 1"
end expect

expect error {{{ le_succ_of_le5 }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
    intro h
    induction h with
    | refl => constructor; constructor
    | step _ ih => constructor
message
"unsolved goals
case step.a
n m m✝ : Nat
a✝ : n.le m✝
ih : n ≤ m✝ + 1
⊢ n.le (m✝ + 1)"
end expect

book declaration {{{ le_succ_of_le }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
    intro h
    induction h with
    | refl => constructor; constructor
    | step => constructor; assumption
stop book declaration

namespace Apply
book declaration {{{ le_succ_of_le_apply }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1 := by
    intro h
    induction h with
    | refl => apply Nat.le.step; exact Nat.le.refl
    | step _ ih => apply Nat.le.step; exact ih
stop book declaration
end Apply

namespace Golf
book declaration {{{ le_succ_of_le_golf }}}
  theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= by
    induction h <;> repeat (first | constructor | assumption)
stop book declaration
end Golf

namespace Golf'
book declaration {{{ le_succ_of_le_omega }}}
  theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ m + 1:= by
    omega
stop book declaration
end Golf'

namespace NoTac

book declaration {{{ le_succ_of_le_recursive }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ m + 1
    | .refl => .step .refl
    | .step h => .step (Nat.le_succ_of_le h)
stop book declaration
end NoTac
end Extras

book declaration {{{ splitList_shorter_le }}}
  theorem splitList_shorter_le (lst : List α) :
      (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length := by
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
stop book declaration


expect error {{{ splitList_shorter_start }}}
  theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
      (splitList lst).fst.length < lst.length ∧
        (splitList lst).snd.length < lst.length := by
    skip
message
"unsolved goals
α : Type u_1
lst : List α
x✝ : lst.length ≥ 2
⊢ (splitList lst).fst.length < lst.length ∧ (splitList lst).snd.length < lst.length"
end expect


expect error {{{ splitList_shorter_1 }}}
  theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
      (splitList lst).fst.length < lst.length ∧
        (splitList lst).snd.length < lst.length := by
    match lst with
    | x :: y :: xs =>
      skip
message
"unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList (x :: y :: xs)).fst.length < (x :: y :: xs).length ∧
    (splitList (x :: y :: xs)).snd.length < (x :: y :: xs).length"
end expect


expect error {{{ splitList_shorter_2 }}}
  theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
      (splitList lst).fst.length < lst.length ∧
        (splitList lst).snd.length < lst.length := by
    match lst with
    | x :: y :: xs =>
      simp [splitList]
message
"unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList xs).fst.length < xs.length + 1 ∧ (splitList xs).snd.length < xs.length + 1"
end expect


expect error {{{ splitList_shorter_2b }}}
  theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
      (splitList lst).fst.length < lst.length ∧
        (splitList lst).snd.length < lst.length := by
    match lst with
    | x :: y :: xs =>
      simp +arith [splitList]
message
"unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : (x :: y :: xs).length ≥ 2
⊢ (splitList xs).fst.length ≤ xs.length ∧ (splitList xs).snd.length ≤ xs.length"
end expect


book declaration {{{ splitList_shorter }}}
  theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
      (splitList lst).fst.length < lst.length ∧
        (splitList lst).snd.length < lst.length := by
    match lst with
    | x :: y :: xs =>
      simp +arith [splitList]
      apply splitList_shorter_le
stop book declaration


book declaration {{{ splitList_shorter_sides }}}
  theorem splitList_shorter_fst (lst : List α) (h : lst.length ≥ 2) :
      (splitList lst).fst.length < lst.length :=
    splitList_shorter lst h |>.left

  theorem splitList_shorter_snd (lst : List α) (h : lst.length ≥ 2) :
      (splitList lst).snd.length < lst.length :=
    splitList_shorter lst h |>.right
stop book declaration



expect warning {{{ mergeSortSorry }}}
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
message
"declaration uses 'sorry'"
end expect


expect error {{{ mergeSortNeedsGte }}}
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
message
"unsolved goals
case h
α : Type ?u.31067
inst✝ : Ord α
xs : List α
h : ¬xs.length < 2
halves : List α × List α := splitList xs
⊢ xs.length ≥ 2"
end expect


expect warning {{{ mergeSortGteStarted }}}
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
message
"declaration uses 'sorry'"
end expect


book declaration {{{ mergeSort }}}
  def mergeSort [Ord α] (xs : List α) : List α :=
    if h : xs.length < 2 then
      match xs with
      | [] => []
      | [x] => [x]
    else
      let halves := splitList xs
      have : xs.length ≥ 2 := by
        omega
      have : halves.fst.length < xs.length := by
        apply splitList_shorter_fst
        assumption
      have : halves.snd.length < xs.length := by
        apply splitList_shorter_snd
        assumption
      merge (mergeSort halves.fst) (mergeSort halves.snd)
  termination_by xs.length
stop book declaration


expect info {{{ mergeSortRocks }}}
  #eval mergeSort ["soapstone", "geode", "mica", "limestone"]
message
"[\"geode\", \"limestone\", \"mica\", \"soapstone\"]"
end expect


expect info {{{ mergeSortNumbers }}}
  #eval mergeSort [5, 3, 22, 15]
message
"[3, 5, 15, 22]"
end expect


theorem zero_lt_succ : 0 < Nat.succ n := by
  induction n with
  | zero => constructor
  | succ n' ih => constructor; exact ih

namespace Proofs

theorem Nat.succ_sub_succ_eq_sub (n m : Nat) : Nat.succ n - Nat.succ m = n - m := by simp

theorem sub_le (n k : Nat) : n - k ≤ n := by
  induction k with
  | zero => simp
  | succ k' ih =>
    calc
      n - Nat.succ k' ≤ n - k' := by apply Nat.pred_le
      n - k' ≤ n := ih

-- def sub_lt (n k : Nat) : ¬ n < k → n - k < n := by
--   induction k with
--   | zero => intro h

-- def divide (n k : Nat) (nonZero : k ≠ 0) : Nat :=
--   if hLt : n < k then
--     0
--   else
--     have : n - k < n := by
--       apply Nat.sub_lt
--       . cases k with
--         | zero => contradiction
--         | succ k' =>
--     1 + divide (n - k) k nonZero
-- termination_by divide n k _ => n





theorem Nat.lt_of_succ_lt : n + 1 < m → n < m := by
  intro h
  induction h with
  | refl => repeat constructor
  | step => constructor; assumption

theorem Nat.sub_self_zero (n : Nat) : n - n = 0 := by
  cases n <;> simp

theorem not_eq_zero_of_lt (h : b < a) : a ≠ 0 := by
  cases h <;> simp

theorem Nat.add_succ (n k : Nat) : n + k.succ = (n + k).succ := by
  rfl

theorem Nat.sub_succ (n k : Nat) : n - k.succ = (n - k).pred := by
  rfl

theorem Nat.sub_zero (n : Nat) : n - 0 = n := by rfl

theorem Nat.pred_lt (n : Nat) : n ≠ 0 → n.pred < n := by
  intro h
  cases n <;> simp_all

theorem Nat.not_eq_zero_of_lt (n k : Nat) : n < k → k ≠ 0 := by
  intro h
  cases h <;> simp


theorem Nat.sub_succ_lt_self (a i : Nat) : i < a → a - (i + 1) < a - i := by
  intro h
  rw [Nat.add_succ, Nat.sub_succ]
  apply Nat.pred_lt
  apply Nat.not_eq_zero_of_lt
  apply Nat.zero_lt_sub_of_lt
  assumption



end Proofs
