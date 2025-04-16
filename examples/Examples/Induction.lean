import Examples.Support
import Examples.Classes
import Examples.Monads.Conveniences
import Examples.DependentTypes.Pitfalls

namespace Tactical

expect error {{{ plusR_ind_zero_left_1 }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k
message
"unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0

case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ + 1 = Nat.plusR 0 (n✝ + 1)"
end expect

expect error {{{ plusR_ind_zero_left_2a }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k with
    | zero => skip
    | succ n ih => skip
message
"unsolved goals
case zero
⊢ 0 = Nat.plusR 0 0"
end expect

expect error {{{ plusR_ind_zero_left_2b }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k with
    | zero => skip
    | succ n ih => skip
message
"unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 (n + 1)"
end expect


expect error {{{ plusR_ind_zero_left_3 }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k with
    | zero => skip
    | succ n ih lots of names => skip
message
"too many variable names provided at alternative 'succ', #5 provided, but #2 expected"
end expect

expect error {{{ plusR_ind_zero_left_4 }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k with
    | zero => rfl
    | succ n ih => skip
message
"unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 (n + 1)"
end expect


expect error {{{ plusR_ind_zero_left_5 }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k with
    | zero => rfl
    | succ n ih =>
      unfold Nat.plusR
message
"unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n + 1 = Nat.plusR 0 n + 1"
end expect


expect error {{{ plusR_ind_zero_left_6 }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k with
    | zero => rfl
    | succ n ih =>
      unfold Nat.plusR
      rw [ih]
message
"unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ Nat.plusR 0 n + 1 = Nat.plusR 0 (Nat.plusR 0 n) + 1"
end expect


book declaration {{{ plusR_zero_left_done }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k with
    | zero => rfl
    | succ n ih =>
      unfold Nat.plusR
      rw [←ih]
stop book declaration

namespace Golf


expect error {{{ plusR_zero_left_golf_1 }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k with
    | zero => rfl
    | succ n ih =>
      simp
message
"simp made no progress"
end expect


expect error {{{ plusR_zero_left_golf_2 }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k with
    | zero => rfl
    | succ n ih =>
      simp [Nat.plusR]
message
"unsolved goals
case succ
n : Nat
ih : n = Nat.plusR 0 n
⊢ n = Nat.plusR 0 n"
end expect

namespace One
book declaration {{{ plusR_zero_left_golf_3 }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k with
    | zero => rfl
    | succ n ih =>
      simp [Nat.plusR]
      exact ih
stop book declaration
end One

namespace Two

book declaration {{{ plusR_zero_left_golf_4 }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k with
    | zero => rfl
    | succ n ih =>
      simp [Nat.plusR]
      assumption
stop book declaration
end Two

namespace Three

book declaration {{{ plusR_zero_left_golf_5 }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k
    case zero => rfl
    case succ n ih =>
      simp [Nat.plusR]
      assumption
stop book declaration
end Three


expect error {{{ plusR_zero_left_golf_6a }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k <;> simp [Nat.plusR]
message
"unsolved goals
case succ
n✝ : Nat
a✝ : n✝ = Nat.plusR 0 n✝
⊢ n✝ = Nat.plusR 0 n✝"
end expect

book declaration {{{ plusR_zero_left_golf_6 }}}
  theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
    induction k <;> simp [Nat.plusR] <;> assumption
stop book declaration
end Golf

expect error {{{ append_nil_0b }}}
  theorem List.append_nil (xs : List α) : xs ++ [] = xs := by
    induction xs with
    | nil => skip
    | cons y ys ih => skip
message
"unsolved goals
case cons
α : Type u_1
y : α
ys : List α
ih : ys ++ [] = ys
⊢ y :: ys ++ [] = y :: ys"
end expect

expect error {{{ append_nil_0a }}}
  theorem List.append_nil (xs : List α) : xs ++ [] = xs := by
    induction xs with
    | nil => skip
    | cons y ys ih => skip
message
"unsolved goals
case nil
α : Type u_1
⊢ [] ++ [] = []"
end expect

  theorem List.append_nil (xs : List α) : xs ++ [] = xs := by
    induction xs with
    | nil => rfl
    | cons y ys ih =>
      simp

theorem List.append_assoc (xs ys zs : List α) : xs ++ (ys ++ zs) = (xs ++ ys) ++ zs := by
  induction xs <;> simp only [List.nil_append, List.cons_append, *]

end Tactical


book declaration {{{ BinTree_count }}}
  def BinTree.count : BinTree α → Nat
    | .leaf => 0
    | .branch l _ r =>
      1 + l.count + r.count
stop book declaration


expect error {{{ mirror_count_0a }}}
  theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
    induction t with
    | leaf => skip
    | branch l x r ihl ihr => skip
message
"unsolved goals
case leaf
α : Type
⊢ leaf.mirror.count = leaf.count"
end expect

expect error {{{ mirror_count_0b }}}
  theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
    induction t with
    | leaf => skip
    | branch l x r ihl ihr => skip
message
"unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ (l.branch x r).mirror.count = (l.branch x r).count"
end expect

expect error {{{ mirror_count_1 }}}
  theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
    induction t with
    | leaf => simp [BinTree.mirror]
    | branch l x r ihl ihr => skip
message
"unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ (l.branch x r).mirror.count = (l.branch x r).count"
end expect


expect error {{{ mirror_count_2 }}}
  theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
    induction t with
    | leaf => simp [BinTree.mirror]
    | branch l x r ihl ihr =>
      simp [BinTree.mirror, BinTree.count]
message
"unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ 1 + r.mirror.count + l.mirror.count = 1 + l.count + r.count"
end expect


expect error {{{ mirror_count_3 }}}
  theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
    induction t with
    | leaf => simp [BinTree.mirror]
    | branch l x r ihl ihr =>
      simp [BinTree.mirror, BinTree.count]
      rw [ihl, ihr]
message
"unsolved goals
case branch
α : Type
l : BinTree α
x : α
r : BinTree α
ihl : l.mirror.count = l.count
ihr : r.mirror.count = r.count
⊢ 1 + r.count + l.count = 1 + l.count + r.count"
end expect

book declaration {{{ mirror_count_4 }}}
  theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
    induction t with
    | leaf => simp [BinTree.mirror]
    | branch l x r ihl ihr =>
      simp [BinTree.mirror, BinTree.count]
      rw [ihl, ihr]
      simp +arith
stop book declaration

namespace Golf


book declaration {{{ mirror_count_5 }}}
  theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
    induction t with
    | leaf => simp [BinTree.mirror]
    | branch l x r ihl ihr =>
      simp +arith [BinTree.mirror, BinTree.count, ihl, ihr]
stop book declaration

namespace B
book declaration {{{ mirror_count_6 }}}
  theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
    induction t with
    | leaf => simp [BinTree.mirror]
    | branch l x r ihl ihr =>
      simp +arith [BinTree.mirror, BinTree.count, *]
stop book declaration
end B


namespace A
book declaration {{{ mirror_count_7 }}}
  theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
    induction t <;> simp +arith [BinTree.mirror, BinTree.count, *]
stop book declaration
end A

end Golf
