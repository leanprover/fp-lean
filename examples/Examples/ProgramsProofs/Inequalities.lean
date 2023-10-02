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
  termination_by merge xs ys => xs.length + ys.length
stop book declaration

namespace Other
book declaration {{{ mergePairTerm }}}
  def merge [Ord α] (xs : List α) (ys : List α) : List α :=
    match xs, ys with
    | [], _ => ys
    | _, [] => xs
    | x'::xs', y'::ys' =>
      match Ord.compare x' y' with
      | .lt | .eq => x' :: merge xs' (y' :: ys')
      | .gt => y' :: merge (x'::xs') ys'
  termination_by merge xs ys => (xs, ys)
stop book declaration
end Other

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
argument #3 was not used for structural recursion
  failed to eliminate recursive application
    mergeSort halves.fst

structural recursion cannot be used

failed to prove termination, use `termination_by` to specify a well-founded relation"
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
  termination_by mergeSort xs => xs.length
message
"failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
α : Type u_1
xs : List α
h : ¬List.length xs < 2
halves : List α × List α := splitList xs
⊢ List.length (splitList xs).fst < List.length xs"
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
⊢ List.length (splitList lst).fst ≤ List.length lst ∧ List.length (splitList lst).snd ≤ List.length lst"
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
⊢ List.length (splitList []).fst ≤ List.length [] ∧ List.length (splitList []).snd ≤ List.length []"
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
ih : List.length (splitList xs).fst ≤ List.length xs ∧ List.length (splitList xs).snd ≤ List.length xs
⊢ List.length (splitList (x :: xs)).fst ≤ List.length (x :: xs) ∧
    List.length (splitList (x :: xs)).snd ≤ List.length (x :: xs)"
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
ih : List.length (splitList xs).fst ≤ List.length xs ∧ List.length (splitList xs).snd ≤ List.length xs
⊢ Nat.succ (List.length (splitList xs).snd) ≤ Nat.succ (List.length xs) ∧
    List.length (splitList xs).fst ≤ Nat.succ (List.length xs)"
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
left✝ : List.length (splitList xs).fst ≤ List.length xs
right✝ : List.length (splitList xs).snd ≤ List.length xs
⊢ Nat.succ (List.length (splitList xs).snd) ≤ Nat.succ (List.length xs) ∧
    List.length (splitList xs).fst ≤ Nat.succ (List.length xs)"
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
left✝ : List.length (splitList xs).fst ≤ List.length xs
right✝ : List.length (splitList xs).snd ≤ List.length xs
⊢ Nat.succ (List.length (splitList xs).snd) ≤ Nat.succ (List.length xs)

case cons.intro.right
α : Type u_1
x : α
xs : List α
left✝ : List.length (splitList xs).fst ≤ List.length xs
right✝ : List.length (splitList xs).snd ≤ List.length xs
⊢ List.length (splitList xs).fst ≤ Nat.succ (List.length xs)"
end expect

namespace Extras


expect error {{{ succ_le_succ0 }}}
  theorem Nat.succ_le_succ : n ≤ m → Nat.succ n ≤ Nat.succ m := by
    skip
message
"unsolved goals
n m : Nat
⊢ n ≤ m → Nat.succ n ≤ Nat.succ m"
end expect


expect error {{{ succ_le_succ1 }}}
  theorem Nat.succ_le_succ : n ≤ m → Nat.succ n ≤ Nat.succ m := by
    intro h
message
"unsolved goals
n m : Nat
h : n ≤ m
⊢ Nat.succ n ≤ Nat.succ m"
end expect


expect error {{{ succ_le_succ2 }}}
  theorem Nat.succ_le_succ : n ≤ m → Nat.succ n ≤ Nat.succ m := by
    intro h
    cases h
message
"unsolved goals
case refl
n : Nat
⊢ Nat.succ n ≤ Nat.succ n

case step
n m✝ : Nat
a✝ : Nat.le n m✝
⊢ Nat.succ n ≤ Nat.succ (Nat.succ m✝)"
end expect




expect error {{{ succ_le_succ3 }}}
  theorem Nat.succ_le_succ : n ≤ m → Nat.succ n ≤ Nat.succ m := by
    intro h
    induction h
message
"unsolved goals
case refl
n m : Nat
⊢ Nat.succ n ≤ Nat.succ n

case step
n m m✝ : Nat
a✝ : Nat.le n m✝
a_ih✝ : Nat.succ n ≤ Nat.succ m✝
⊢ Nat.succ n ≤ Nat.succ (Nat.succ m✝)"
end expect


expect error {{{ succ_le_succ4 }}}
  theorem Nat.succ_le_succ : n ≤ m → Nat.succ n ≤ Nat.succ m := by
    intro h
    induction h with
    | refl => constructor
    | step h' ih => constructor
message
"unsolved goals
case step.a
n m m✝ : Nat
h' : Nat.le n m✝
ih : Nat.succ n ≤ Nat.succ m✝
⊢ Nat.le (Nat.succ n) (m✝ + 1)"
end expect


book declaration {{{ succ_le_succ5 }}}
  theorem Nat.succ_le_succ : n ≤ m → Nat.succ n ≤ Nat.succ m := by
    intro h
    induction h with
    | refl => constructor
    | step h' ih =>
      constructor
      assumption
stop book declaration

namespace more


book declaration {{{ succ_le_succ_recursive }}}
  theorem Nat.succ_le_succ : n ≤ m → Nat.succ n ≤ Nat.succ m
    | .refl => .refl
    | .step h' => .step (Nat.succ_le_succ h')
stop book declaration

end more


book declaration {{{ le_succ_of_le }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ Nat.succ m := by
    intro h
    induction h with
    | refl => constructor; constructor
    | step => constructor; assumption
stop book declaration

namespace Apply
book declaration {{{ le_succ_of_le_apply }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ Nat.succ m := by
    intro h
    induction h with
    | refl => apply Nat.le.step; exact Nat.le.refl
    | step _ ih => apply Nat.le.step; exact ih
stop book declaration
end Apply

namespace Golf
book declaration {{{ le_succ_of_le_golf }}}
  theorem Nat.le_succ_of_le (h : n ≤ m) : n ≤ Nat.succ m := by
    induction h <;> repeat (first | constructor | assumption)
stop book declaration
end Golf

namespace NoTac

book declaration {{{ le_succ_of_le_recursive }}}
  theorem Nat.le_succ_of_le : n ≤ m → n ≤ Nat.succ m
    | .refl => .step .refl
    | .step h => .step (Nat.le_succ_of_le h)
stop book declaration
end NoTac
end Extras


expect error {{{ splitList_shorter_le5a }}}
  theorem splitList_shorter_le (lst : List α) :
      (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length := by
    induction lst with
    | nil => simp [splitList]
    | cons x xs ih =>
      simp [splitList]
      cases ih
      constructor
      case left => skip
      case right => skip
message
"unsolved goals
α : Type u_1
x : α
xs : List α
left✝ : List.length (splitList xs).fst ≤ List.length xs
right✝ : List.length (splitList xs).snd ≤ List.length xs
⊢ Nat.succ (List.length (splitList xs).snd) ≤ Nat.succ (List.length xs)"
end expect

expect error {{{ splitList_shorter_le5b }}}
  theorem splitList_shorter_le (lst : List α) :
      (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length := by
    induction lst with
    | nil => simp [splitList]
    | cons x xs ih =>
      simp [splitList]
      cases ih
      constructor
      case left => skip
      case right => skip
message
"unsolved goals
α : Type u_1
x : α
xs : List α
left✝ : List.length (splitList xs).fst ≤ List.length xs
right✝ : List.length (splitList xs).snd ≤ List.length xs
⊢ List.length (splitList xs).fst ≤ Nat.succ (List.length xs)"
end expect


book declaration {{{ splitList_shorter_le }}}
  theorem splitList_shorter_le (lst : List α) :
      (splitList lst).fst.length ≤ lst.length ∧ (splitList lst).snd.length ≤ lst.length := by
    induction lst with
    | nil => simp [splitList]
    | cons x xs ih =>
      simp [splitList]
      cases ih
      constructor
      case left => apply Nat.succ_le_succ; assumption
      case right => apply Nat.le_succ_of_le; assumption
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
x✝ : List.length lst ≥ 2
⊢ List.length (splitList lst).fst < List.length lst ∧ List.length (splitList lst).snd < List.length lst"
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
x✝ : List.length (x :: y :: xs) ≥ 2
⊢ List.length (splitList (x :: y :: xs)).fst < List.length (x :: y :: xs) ∧
    List.length (splitList (x :: y :: xs)).snd < List.length (x :: y :: xs)"
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
x✝ : List.length (x :: y :: xs) ≥ 2
⊢ Nat.succ (List.length (splitList xs).fst) < Nat.succ (Nat.succ (List.length xs)) ∧
    Nat.succ (List.length (splitList xs).snd) < Nat.succ (Nat.succ (List.length xs))"
end expect


expect error {{{ splitList_shorter_2b }}}
  theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
      (splitList lst).fst.length < lst.length ∧
        (splitList lst).snd.length < lst.length := by
    match lst with
    | x :: y :: xs =>
      simp_arith [splitList]
message
"unsolved goals
α : Type u_1
lst : List α
x y : α
xs : List α
x✝ : List.length (x :: y :: xs) ≥ 2
⊢ List.length (splitList xs).fst ≤ List.length xs ∧ List.length (splitList xs).snd ≤ List.length xs"
end expect


book declaration {{{ splitList_shorter }}}
  theorem splitList_shorter (lst : List α) (_ : lst.length ≥ 2) :
      (splitList lst).fst.length < lst.length ∧
        (splitList lst).snd.length < lst.length := by
    match lst with
    | x :: y :: xs =>
      simp_arith [splitList]
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
  termination_by mergeSort xs => xs.length
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
  termination_by mergeSort xs => xs.length
message
"unsolved goals
case h
α : Type ?u.37732
inst✝ : Ord α
xs : List α
h : ¬List.length xs < 2
halves : List α × List α := splitList xs
⊢ List.length xs ≥ 2"
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
  termination_by mergeSort xs => xs.length
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
        apply Nat.ge_of_not_lt
        assumption
      have : halves.fst.length < xs.length := by
        apply splitList_shorter_fst
        assumption
      have : halves.snd.length < xs.length := by
        apply splitList_shorter_snd
        assumption
      merge (mergeSort halves.fst) (mergeSort halves.snd)
  termination_by mergeSort xs => xs.length
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

theorem Nat.succ_sub_succ_eq_sub (n m : Nat) : Nat.succ n - Nat.succ m = n - m := by
  induction m with
  | zero      => rfl
  | succ m ih =>
    simp [(· - ·), Sub.sub, Nat.sub]
    rw [←ih]
    simp [(· - ·), Sub.sub, Nat.sub]


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
  cases n <;> simp
  case zero => contradiction
  case succ n' => apply Nat.le.refl

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
