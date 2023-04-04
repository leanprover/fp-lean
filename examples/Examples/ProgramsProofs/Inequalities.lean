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

book declaration {{{ split }}}
  def split (lst : List α) : (List α × List α) :=
    match lst with
    | [] => ([], [])
    | x :: xs =>
      let (a, b) := split xs
      (x :: b, a)
stop book declaration


expect error {{{ mergeSortNoTerm }}}
  def mergeSort [Ord α] (xs : List α) : List α :=
    if h : xs.length < 2 then
      match xs with
      | [] => []
      | [x] => [x]
    else
      let halves := split xs
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
      let halves := split xs
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
halves : List α × List α := split xs
⊢ List.length (split xs).fst < List.length xs"
end expect

theorem split_shorter_le (lst : List α) : (split lst).fst.length ≤ lst.length ∧ (split lst).snd.length ≤ lst.length := by
  induction lst with
  | nil => simp [split]
  | cons x xs ih =>
    simp [split]
    cases ih
    constructor
    case left => apply Nat.succ_le_succ; assumption
    case right => apply Nat.le_succ_of_le; assumption

theorem split_shorter (lst : List α) (_ : lst.length ≥ 2) : (split lst).fst.length < lst.length ∧ (split lst).snd.length < lst.length :=
  match lst with
  | x :: y :: xs => by
    induction xs with
    | nil => simp [split]
    | cons z zs ih =>
      simp [split]
      have : List.length (x :: y :: zs) ≥ 2 := by simp_arith
      cases ih this
      constructor
      case left => apply Nat.succ_le_succ; assumption
      case right => apply Nat.le_succ_of_le; assumption


theorem zero_lt_succ : 0 < Nat.succ n := by
  induction n with
  | zero => constructor
  | succ n' ih => constructor; exact ih

theorem not_lt_ge : (n k : Nat) → ¬ n < k → n ≥ k
  | .zero, .zero, _ => by simp
  | .zero, .succ k', _ => by
    have : 0 < k'.succ := by apply zero_lt_succ
    contradiction
  | .succ n', .zero, notLT => by
    simp
  | .succ n', .succ k', notLT => by sorry

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

def sub_lt (n k : Nat) : ¬ n < k → n - k < n := by
  induction k with
  | zero => intro h

def divide (n k : Nat) (nonZero : k ≠ 0) : Nat :=
  if hLt : n < k then
    0
  else
    have : n - k < n := by
      apply Nat.sub_lt
      . cases k with
        | zero => contradiction
        | succ k' =>
    1 + divide (n - k) k nonZero
termination_by divide n k _ => n





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
