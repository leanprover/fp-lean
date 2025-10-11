import ExampleSupport
import Examples.Classes
import Examples.Monads.Conveniences
import Examples.DependentTypes.Pitfalls

namespace Tactical

discarding
/-- error:
unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0

case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ + 1 = Nat.plusR 0 (n✝ + 1)
-/
#check_msgs in
-- ANCHOR: plusR_ind_zero_left_1
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k
-- ANCHOR_END: plusR_ind_zero_left_1
stop discarding

discarding
/--
error: unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0
---
error: unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 (n + 1)
-/
#check_msgs in
-- ANCHOR: plusR_ind_zero_left_2a
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => skip
  | succ n ih => skip
-- ANCHOR_END: plusR_ind_zero_left_2a
stop discarding

discarding
/--
error: unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0
---
error: unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 (n + 1)
-/
#check_msgs in
-- ANCHOR: plusR_ind_zero_left_2b
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => skip
  | succ n ih => skip
-- ANCHOR_END: plusR_ind_zero_left_2b
stop discarding

discarding
/--
error: unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0
---
error: Too many variable names provided at alternative 'succ': 5 provided, but 2 expected
---
error: unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 (n + 1)
-/
#check_msgs in
-- ANCHOR: plusR_ind_zero_left_3
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => skip
  | succ n ih lots of names => skip
-- ANCHOR_END: plusR_ind_zero_left_3
stop discarding

discarding
/-- error:
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 (n + 1)
-/
#check_msgs in
-- ANCHOR: plusR_ind_zero_left_4
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih => skip
-- ANCHOR_END: plusR_ind_zero_left_4
stop discarding

discarding
/-- error:
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 n + 1
-/
#check_msgs in
-- ANCHOR: plusR_ind_zero_left_5
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
-- ANCHOR_END: plusR_ind_zero_left_5
stop discarding

discarding
/-- error:
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ Nat.plusR 0 n + 1 = Nat.plusR 0 (Nat.plusR 0 n) + 1
-/
#check_msgs in
-- ANCHOR: plusR_ind_zero_left_6
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [ih]
-- ANCHOR_END: plusR_ind_zero_left_6
stop discarding

-- ANCHOR: plusR_zero_left_done
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR
    rw [←ih]
-- ANCHOR_END: plusR_zero_left_done

namespace Golf

discarding
/-- error: `simp` made no progress -/
#check_msgs in
-- ANCHOR: plusR_zero_left_golf_1
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp
-- ANCHOR_END: plusR_zero_left_golf_1
stop discarding

discarding
/-- error:
unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n = Nat.plusR 0 n
-/
#check_msgs in
-- ANCHOR: plusR_zero_left_golf_2
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
-- ANCHOR_END: plusR_zero_left_golf_2
stop discarding


namespace One
-- ANCHOR: plusR_zero_left_golf_3
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    exact ih
-- ANCHOR_END: plusR_zero_left_golf_3
end One


namespace Two

-- ANCHOR: plusR_zero_left_golf_4
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with
  | zero => rfl
  | succ n ih =>
    simp [Nat.plusR]
    assumption
-- ANCHOR_END: plusR_zero_left_golf_4
end Two

namespace Three

-- ANCHOR: plusR_zero_left_golf_5
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k
  case zero => rfl
  case succ n ih =>
    simp [Nat.plusR]
    assumption
-- ANCHOR_END: plusR_zero_left_golf_5
end Three

discarding
/-- error:
unsolved goals
case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ = Nat.plusR 0 n✝
-/
#check_msgs in
-- ANCHOR: plusR_zero_left_golf_6a
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR]
-- ANCHOR_END: plusR_zero_left_golf_6a
stop discarding

discarding
-- ANCHOR: plusR_zero_left_golf_6
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> simp [Nat.plusR] <;> assumption
-- ANCHOR_END: plusR_zero_left_golf_6
stop discarding

-- ANCHOR: plusR_zero_left_golf_7
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k <;> grind [Nat.plusR]
-- ANCHOR_END: plusR_zero_left_golf_7
end Golf

discarding
/--
error: unsolved goals
case nil
α : Type u_1
⊢ [] ++ [] = []
---
error: unsolved goals
case cons
α : Type u_1
y : α
ys : List α
ih : ys ++ [] = ys
⊢ y :: ys ++ [] = y :: ys
-/
#check_msgs in
-- ANCHOR: append_nil_0b
theorem List.append_nil (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => skip
  | cons y ys ih => skip
-- ANCHOR_END: append_nil_0b
stop discarding

discarding
/--
error: unsolved goals
case nil
α : Type u_1
⊢ [] ++ [] = []
---
error: unsolved goals
case cons
α : Type u_1
y : α
ys : List α
ih : ys ++ [] = ys
⊢ y :: ys ++ [] = y :: ys
-/
#check_msgs in
-- ANCHOR: append_nil_0a
theorem List.append_nil (xs : List α) : xs ++ [] = xs := by
  induction xs with
  | nil => skip
  | cons y ys ih => skip
-- ANCHOR_END: append_nil_0a
stop discarding

  theorem List.append_nil (xs : List α) : xs ++ [] = xs := by
    induction xs with
    | nil => rfl
    | cons y ys ih =>
      simp

theorem List.append_assoc (xs ys zs : List α) : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by
  induction xs <;> simp only [List.nil_append, List.cons_append, *]

end Tactical

-- ANCHOR: TreeCtors
example := @BinTree.leaf
example := @BinTree.branch
example {l : BinTree α} {x r} := BinTree.branch l x r
-- ANCHOR_END: TreeCtors


-- ANCHOR: BinTree_count
def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count
-- ANCHOR_END: BinTree_count

discarding
/--
error: unsolved goals
case leaf
α : Type
⊢ leaf.mirror.count = leaf.count
---
error: unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ (l.branch x r).mirror.count = (l.branch x r).count
-/
#check_msgs in
-- ANCHOR: mirror_count_0a
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => skip
  | branch l x r ihl ihr => skip
-- ANCHOR_END: mirror_count_0a
stop discarding

discarding
/--
error: unsolved goals
case leaf
α : Type
⊢ leaf.mirror.count = leaf.count
---
error: unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ (l.branch x r).mirror.count = (l.branch x r).count
-/
#check_msgs in
-- ANCHOR: mirror_count_0b
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => skip
  | branch l x r ihl ihr => skip
-- ANCHOR_END: mirror_count_0b
stop discarding

discarding
/-- error:
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ (l.branch x r).mirror.count = (l.branch x r).count
-/
#check_msgs in
-- ANCHOR: mirror_count_1
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr => skip
-- ANCHOR_END: mirror_count_1
stop discarding

discarding
/-- error:
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ 1 + r.mirror.count + l.mirror.count = 1 + l.count + r.count
-/
#check_msgs in
-- ANCHOR: mirror_count_2
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
-- ANCHOR_END: mirror_count_2
stop discarding

discarding
/-- error:
unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ 1 + r.count + l.count = 1 + l.count + r.count
-/
#check_msgs in
-- ANCHOR: mirror_count_3
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
    rw [ihl, ihr]
-- ANCHOR_END: mirror_count_3
stop discarding

-- ANCHOR: mirror_count_4
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp [BinTree.mirror, BinTree.count]
    rw [ihl, ihr]
    simp +arith
-- ANCHOR_END: mirror_count_4

namespace Golf


-- ANCHOR: mirror_count_5
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp +arith [BinTree.mirror, BinTree.count, ihl, ihr]
-- ANCHOR_END: mirror_count_5

namespace B
-- ANCHOR: mirror_count_6
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t with
  | leaf => simp [BinTree.mirror]
  | branch l x r ihl ihr =>
    simp +arith [BinTree.mirror, BinTree.count, *]
-- ANCHOR_END: mirror_count_6
end B


namespace A
discarding
-- ANCHOR: mirror_count_7
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t <;> simp +arith [BinTree.mirror, BinTree.count, *]
-- ANCHOR_END: mirror_count_7
stop discarding

-- ANCHOR: mirror_count_8
theorem BinTree.mirror_count (t : BinTree α) :
    t.mirror.count = t.count := by
  induction t <;> grind [BinTree.mirror, BinTree.count]
-- ANCHOR_END: mirror_count_8
end A

end Golf

-- ANCHOR: others
example := Nat.zero = Nat.plusR 0 Nat.zero
example {A B : Nat} : Nat.succ A = Nat.succ B → A = B := by simp
example [Monad m] : m Unit := pure ()
example {n} := Nat.plusR 0 n
example {n} := Nat.plusR 0 n + 1
example {n} := Nat.plusR 0 (Nat.succ n)
-- ANCHOR_END: others

namespace Ex
-- ANCHOR: ex
theorem List.append_assoc (xs ys zs : List α) :
    xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by simp
-- ANCHOR_END: ex
end Ex

def BinTree.graftLeft (root newBranch : BinTree α) : BinTree α :=
  match root with
  | .leaf => newBranch
  | .branch l x r => .branch (l.graftLeft newBranch) x r

theorem BinTree.count_graftLeft_eq_sum_count' (root newBranch : BinTree α) :
    (root.graftLeft newBranch).count = root.count + newBranch.count := by
  induction root with
  | leaf => simp [BinTree.graftLeft, BinTree.count]
  | branch l x r ihl ihr =>
    simp +arith [BinTree.graftLeft, BinTree.count, *]



theorem BinTree.count_graftLeft_eq_sum_count (root newBranch : BinTree α) :
    (root.graftLeft newBranch).count = root.count + newBranch.count := by
  induction root <;> grind [BinTree.graftLeft, BinTree.count]
