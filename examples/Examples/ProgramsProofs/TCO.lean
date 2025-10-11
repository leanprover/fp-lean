import ExampleSupport
import Examples.Monads.Conveniences


-- ANCHOR: NonTailSum
def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs
-- ANCHOR_END: NonTailSum

evaluation steps : Nat {{{ NonTailSumOneTwoThree }}}
-- ANCHOR: NonTailSumOneTwoThree
NonTail.sum [1, 2, 3]
===>
1 + (NonTail.sum [2, 3])
===>
1 + (2 + (NonTail.sum [3]))
===>
1 + (2 + (3 + (NonTail.sum [])))
===>
1 + (2 + (3 + 0))
===>
1 + (2 + 3)
===>
1 + 5
===>
6
-- ANCHOR_END: NonTailSumOneTwoThree
end evaluation steps

namespace MoreClear
-- ANCHOR: MoreClearSumHelper
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar + 0
  | x :: xs => sumHelper (x + soFar) xs
-- ANCHOR_END: MoreClearSumHelper
end MoreClear

-- ANCHOR: TailSum
def Tail.sumHelper (soFar : Nat) : List Nat → Nat
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs
-- ANCHOR_END: TailSum

evaluation steps : Nat {{{ TailSumOneTwoThree }}}
-- ANCHOR: TailSumOneTwoThree
Tail.sum [1, 2, 3]
===>
Tail.sumHelper 0 [1, 2, 3]
===>
Tail.sumHelper (0 + 1) [2, 3]
===>
Tail.sumHelper 1 [2, 3]
===>
Tail.sumHelper (1 + 2) [3]
===>
Tail.sumHelper 3 [3]
===>
Tail.sumHelper (3 + 3) []
===>
Tail.sumHelper 6 []
===>
6
-- ANCHOR_END: TailSumOneTwoThree
end evaluation steps




-- ANCHOR: NonTailReverse
def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]
-- ANCHOR_END: NonTailReverse

evaluation steps  {{{ NonTailReverseSteps }}}
-- ANCHOR: NonTailReverseSteps
NonTail.reverse [1, 2, 3]
===>
(NonTail.reverse [2, 3]) ++ [1]
===>
((NonTail.reverse [3]) ++ [2]) ++ [1]
===>
(((NonTail.reverse []) ++ [3]) ++ [2]) ++ [1]
===>
(([] ++ [3]) ++ [2]) ++ [1]
===>
([3] ++ [2]) ++ [1]
===>
[3, 2] ++ [1]
===>
[3, 2, 1]
-- ANCHOR_END: NonTailReverseSteps
end evaluation steps



-- ANCHOR: TailReverse
def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs
-- ANCHOR_END: TailReverse

evaluation steps  {{{ TailReverseSteps }}}
-- ANCHOR: TailReverseSteps
Tail.reverse [1, 2, 3]
===>
Tail.reverseHelper [] [1, 2, 3]
===>
Tail.reverseHelper [1] [2, 3]
===>
Tail.reverseHelper [2, 1] [3]
===>
Tail.reverseHelper [3, 2, 1] []
===>
[3, 2, 1]
-- ANCHOR_END: TailReverseSteps
end evaluation steps


def Slow.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

def CPS.mirror {β : Type u} (k : BinTree α → β) : BinTree α → β
  | .leaf => k .leaf
  | .branch l x r =>
    mirror (fun r' => mirror (fun l' => k (.branch r' x l')) l) r

def CPS.reverse (k : List α → β) : List α → β
  | [] => k []
  | x :: xs => reverse (fun xs' => k (xs' ++ [x])) xs

deriving instance Repr for BinTree

#eval CPS.mirror id (.branch (.branch .leaf 1 .leaf) 4 (.branch (.branch .leaf 2 .leaf) 3 .leaf))

theorem mirror_cps_eq' : @CPS.mirror α (BinTree α) f = f ∘ @Slow.mirror α := by
  funext t
  induction t generalizing f with
  | leaf => simp [Slow.mirror, CPS.mirror]
  | branch l x r ihl ihr =>
    simp [Slow.mirror, CPS.mirror, *]

theorem mirror_cps_eq : @CPS.mirror α (BinTree α) id = @Slow.mirror α := by
  apply mirror_cps_eq'

-- Exercises

-- ANCHOR: NonTailLength
def NonTail.length : List α → Nat
  | [] => 0
  | _ :: xs => NonTail.length xs + 1
-- ANCHOR_END: NonTailLength

def Tail.lengthHelper (soFar : Nat) : List α → Nat
  | [] => soFar
  | _ :: xs => Tail.lengthHelper (soFar + 1) xs

def Tail.length (xs : List α) : Nat :=
  Tail.lengthHelper 0 xs


-- ANCHOR: NonTailFact
def NonTail.factorial : Nat → Nat
  | 0 => 1
  | n + 1 => factorial n * (n + 1)
-- ANCHOR_END: NonTailFact

def Tail.factHelper (soFar : Nat) : Nat → Nat
  | 0 => soFar
  | n + 1 => factHelper (soFar * (n + 1)) n

def Tail.factorial := factHelper 1

-- ANCHOR: NonTailFilter
def NonTail.filter (p : α → Bool) : List α → List α
  | [] => []
  | x :: xs =>
    if p x then
      x :: filter p xs
    else
      filter p xs
-- ANCHOR_END: NonTailFilter

def Tail.filterHelper (accum : List α) (p : α → Bool) : List α → List α
  | [] => accum.reverse
  | x :: xs =>
    if p x then
      filterHelper (x :: accum) p xs
    else
      filterHelper accum p xs

def Tail.filter (p : α → Bool) := filterHelper [] p

-- ANCHOR: tailFilterTest
example : (
Tail.filter (· > 3) [1,2,3,4,5,6]
) = (
[4,5,6]
) := rfl
-- ANCHOR_END: tailFilterTest

discarding
/-- error:
unsolved goals
xs : List Nat
⊢ ∀ (n : Nat), n + Tail.sum xs = Tail.sumHelper n xs
-/
#check_msgs in
-- ANCHOR: sumEqHelper0
theorem helper_add_sum_accum (xs : List Nat) : (n : Nat) → n + Tail.sum xs = Tail.sumHelper n xs := by
  skip
-- ANCHOR_END: sumEqHelper0
stop discarding

discarding
/-- error:
unsolved goals
xs : List Nat
n : Nat
⊢ n + Tail.sum xs = Tail.sumHelper n xs
-/
#check_msgs in
-- ANCHOR: sumEqHelperBad0
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  skip
-- ANCHOR_END: sumEqHelperBad0
stop discarding

discarding
/-- error:
unsolved goals
case cons
n y : Nat
ys : List Nat
ih : n + Tail.sum ys = Tail.sumHelper n ys
⊢ n + Tail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
-/
#check_msgs in
-- ANCHOR: sumEqHelperBad1
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih => skip
-- ANCHOR_END: sumEqHelperBad1
stop discarding

discarding
/-- error:
unsolved goals
case cons
n y : Nat
ys : List Nat
ih : n + Tail.sum ys = Tail.sumHelper n ys
⊢ n + Tail.sumHelper y ys = Tail.sumHelper (y + n) ys
-/
#check_msgs in
-- ANCHOR: sumEqHelperBad2
theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
    n + Tail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [Tail.sum, Tail.sumHelper]
-- ANCHOR_END: sumEqHelperBad2
stop discarding

theorem helper_add_sum_accum (xs : List Nat) :
    (n : Nat) → n + Tail.sumHelper 0 xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => simp [Tail.sumHelper]
  | cons y ys ih =>
    intro n
    simp [Tail.sumHelper]
    rw [←ih]
    rw [←Nat.add_assoc]
    rw [←Nat.add_comm y n]
    apply ih

discarding
/-- error:
unsolved goals
⊢ NonTail.sum = Tail.sum
-/
#check_msgs in
-- ANCHOR: sumEq0
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  skip
-- ANCHOR_END: sumEq0
stop discarding

discarding
/-- error:
unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sum xs
-/
#check_msgs in
-- ANCHOR: sumEq1
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
-- ANCHOR_END: sumEq1
stop discarding

discarding
/--
error: unsolved goals
case h.nil
⊢ NonTail.sum [] = Tail.sum []
---
error: unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ NonTail.sum (y :: ys) = Tail.sum (y :: ys)
-/
#check_msgs in
-- ANCHOR: sumEq2a
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => skip
  | cons y ys ih => skip
-- ANCHOR_END: sumEq2a
stop discarding

discarding
/--
error: unsolved goals
case h.nil
⊢ NonTail.sum [] = Tail.sum []
---
error: unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ NonTail.sum (y :: ys) = Tail.sum (y :: ys)
-/
#check_msgs in
-- ANCHOR: sumEq2b
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => skip
  | cons y ys ih => skip
-- ANCHOR_END: sumEq2b
stop discarding

discarding
/-- error:
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ NonTail.sum (y :: ys) = Tail.sum (y :: ys)
-/
#check_msgs in
-- ANCHOR: sumEq3
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih => skip
-- ANCHOR_END: sumEq3
stop discarding

discarding
/-- error:
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + NonTail.sum ys = Tail.sumHelper 0 (y :: ys)
-/
#check_msgs in
-- ANCHOR: sumEq4
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum]
-- ANCHOR_END: sumEq4
stop discarding

discarding
/-- error:
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + NonTail.sum ys = Tail.sumHelper y ys
-/
#check_msgs in
-- ANCHOR: sumEq5
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]
-- ANCHOR_END: sumEq5
stop discarding

discarding
/-- error:
unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + Tail.sum ys = Tail.sumHelper y ys
-/
#check_msgs in
-- ANCHOR: sumEq6
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  induction xs with
  | nil => rfl
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]
    rw [ih]
-- ANCHOR_END: sumEq6
stop discarding

discarding
/-- error:
unsolved goals
xs : List Nat
⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs
-/
#check_msgs in
-- ANCHOR: nonTailEqHelper0
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  skip
-- ANCHOR_END: nonTailEqHelper0
stop discarding

discarding
/--
error: unsolved goals
case nil
⊢ ∀ (n : Nat), n + NonTail.sum [] = Tail.sumHelper n []
---
error: unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
-/
#check_msgs in
-- ANCHOR: nonTailEqHelper1a
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => skip
  | cons y ys ih => skip
-- ANCHOR_END: nonTailEqHelper1a
stop discarding

discarding
/--
error: unsolved goals
case nil
⊢ ∀ (n : Nat), n + NonTail.sum [] = Tail.sumHelper n []
---
error: unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
-/
#check_msgs in
-- ANCHOR: nonTailEqHelper1b
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => skip
  | cons y ys ih => skip
-- ANCHOR_END: nonTailEqHelper1b
stop discarding

discarding
/--
error: unsolved goals
case nil
n : Nat
⊢ n + NonTail.sum [] = Tail.sumHelper n []
---
error: unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
-/
#check_msgs in
-- ANCHOR: nonTailEqHelper2
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => intro n
  | cons y ys ih => skip
-- ANCHOR_END: nonTailEqHelper2
stop discarding

discarding
/-- error:
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
-/
#check_msgs in
-- ANCHOR: nonTailEqHelper3
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih => skip
-- ANCHOR_END: nonTailEqHelper3
stop discarding

discarding
/-- error:
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)
-/
#check_msgs in
-- ANCHOR: nonTailEqHelper4
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
-- ANCHOR_END: nonTailEqHelper4
stop discarding

discarding
/-- error:
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + (y + NonTail.sum ys) = Tail.sumHelper (y + n) ys
-/
#check_msgs in
-- ANCHOR: nonTailEqHelper5
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
-- ANCHOR_END: nonTailEqHelper5
stop discarding

discarding
/-- error:
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + y + NonTail.sum ys = Tail.sumHelper (y + n) ys
-/
#check_msgs in
-- ANCHOR: nonTailEqHelper6
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
-- ANCHOR_END: nonTailEqHelper6
stop discarding

discarding
/-- error:
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ NonTail.sum ys + (n + y) = Tail.sumHelper (y + n) ys
-/
#check_msgs in
-- ANCHOR: nonTailEqHelper7
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm]
-- ANCHOR_END: nonTailEqHelper7
stop discarding

discarding
/-- error:
unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + y + NonTail.sum ys = Tail.sumHelper (n + y) ys
-/
#check_msgs in
-- ANCHOR: nonTailEqHelper8
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil =>
    intro n
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm y n]
-- ANCHOR_END: nonTailEqHelper8
stop discarding

discarding
-- ANCHOR: nonTailEqHelperDone
theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
    (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => intro n; rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm y n]
    exact ih (n + y)
-- ANCHOR_END: nonTailEqHelperDone
stop discarding

discarding
/--
error: unsolved goals
case case1
n : Nat
⊢ n + NonTail.sum [] = n
---
error: unsolved goals
case case2
n y : Nat
ys : List Nat
ih : y + n + NonTail.sum ys = Tail.sumHelper (y + n) ys
⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper (y + n) ys
-/
#check_msgs in
-- ANCHOR: nonTailEqHelperFunInd1
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper with
  | case1 n => skip
  --           ^ PROOF_STATE: BASE
  | case2 n y ys ih => skip
  --                   ^ PROOF_STATE: STEP
-- ANCHOR_END: nonTailEqHelperFunInd1
stop discarding

discarding
-- ANCHOR: nonTailEqHelperFunInd2
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper with
  | case1 n => simp [NonTail.sum]
  | case2 n y ys ih =>
    simp [NonTail.sum]
    rw [←Nat.add_assoc]
    rw [Nat.add_comm n y]
    assumption
-- ANCHOR_END: nonTailEqHelperFunInd2
stop discarding

-- ANCHOR: nonTailEqHelperFunInd3
theorem non_tail_sum_eq_helper_accum (xs : List Nat) (n : Nat) :
    n + NonTail.sum xs = Tail.sumHelper n xs := by
  fun_induction Tail.sumHelper <;> grind [NonTail.sum]
-- ANCHOR_END: nonTailEqHelperFunInd3

-- ANCHOR: NatAddAssoc
example : (n m k : Nat) → (n + m) + k = n + (m + k) := Nat.add_assoc
-- ANCHOR_END: NatAddAssoc

-- ANCHOR: NatAddComm
example : (n m : Nat) → n + m = m + n := Nat.add_comm
-- ANCHOR_END: NatAddComm


discarding
/-- error:
unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sum xs
-/
#check_msgs in
-- ANCHOR: nonTailEqReal0
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
-- ANCHOR_END: nonTailEqReal0
stop discarding

discarding
/-- error:
unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sumHelper 0 xs
-/
#check_msgs in
-- ANCHOR: nonTailEqReal1
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
-- ANCHOR_END: nonTailEqReal1
stop discarding

-- ANCHOR: NatZeroAdd
example : (n : Nat) → 0 + n = n := Nat.zero_add
-- ANCHOR_END: NatZeroAdd

namespace Wak
axiom xs : List Nat

-- ANCHOR: NatZeroAddApplied
example : 0 + NonTail.sum xs = NonTail.sum xs := Nat.zero_add (NonTail.sum xs)
-- ANCHOR_END: NatZeroAddApplied
end Wak

discarding
/-- error:
unsolved goals
case h
xs : List Nat
⊢ 0 + NonTail.sum xs = Tail.sumHelper 0 xs
-/
#check_msgs in
-- ANCHOR: nonTailEqReal2
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
-- ANCHOR_END: nonTailEqReal2
stop discarding

-- ANCHOR: nonTailEqRealDone
theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [←Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0
-- ANCHOR_END: nonTailEqRealDone


theorem reverse_helper (xs : List α) : (ys : List α) → NonTail.reverse xs ++ ys = Tail.reverseHelper ys xs := by
  induction xs with
  | nil => intro ys; simp [NonTail.reverse, Tail.reverseHelper]
  | cons x xs ih =>
    intro ys
    simp [NonTail.reverse, Tail.reverseHelper, ← ih]

discarding
/-- error:
unsolved goals
case h.h
α : Type u_1
xs : List α
⊢ NonTail.reverse xs = Tail.reverse xs
-/
#check_msgs in
-- ANCHOR: reverseEqStart
theorem non_tail_reverse_eq_tail_reverse :
    @NonTail.reverse = @Tail.reverse := by
  funext α xs
-- ANCHOR_END: reverseEqStart
stop discarding

theorem non_tail_reverse_eq_tail_reverse :
    @NonTail.reverse = @Tail.reverse := by
  funext α xs
  simp [Tail.reverse]
  rw [← List.append_nil (NonTail.reverse xs)]
  apply reverse_helper


-- theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
--   funext xs
--   induction xs with
--   | nil => rfl
--   | cons y ys ih =>
--     simp [NonTail.sum, Tail.sum, Tail.sumHelper]
--     rw [ih]
--     apply helper_simulates_non_tail

def bigList (n : Nat) (soFar : List Nat) : List Nat :=
  match n with
  | 0 => soFar
  | k + 1 =>
    bigList k (2 * n :: soFar)

-- #eval timeit "hello" (IO.println theBigList.length)

-- #eval timeit "a" (IO.println <| Tail.sum theBigList)

-- #eval timeit "b" (IO.println <| NonTail.sum theBigList)

-- ANCHOR: names
section
example := @List.cons
end
-- ANCHOR_END: names


-- ANCHOR: accum_stmt
section
variable {n}
example := Tail.sumHelper n
end
section
variable {ys : List α}
example := Tail.reverseHelper ys
example := Tail.reverseHelper [] ys
end
-- ANCHOR_END: accum_stmt
