import Examples.Support
import Examples.Monads.Conveniences


book declaration {{{ NonTailSum }}}
  def NonTail.sum : List Nat → Nat
    | [] => 0
    | x :: xs => x + sum xs
stop book declaration

evaluation steps : Nat {{{ NonTailSumOneTwoThree }}}
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
end evaluation steps

namespace MoreClear
book declaration {{{ MoreClearSumHelper }}}
  def Tail.sumHelper (soFar : Nat) : List Nat → Nat
    | [] => soFar + 0
    | x :: xs => sumHelper (x + soFar) xs
stop book declaration
end MoreClear

book declaration {{{ TailSum }}}
  def Tail.sumHelper (soFar : Nat) : List Nat → Nat
    | [] => soFar
    | x :: xs => sumHelper (x + soFar) xs

  def Tail.sum (xs : List Nat) : Nat :=
    Tail.sumHelper 0 xs
stop book declaration

evaluation steps : Nat {{{ TailSumOneTwoThree }}}
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
end evaluation steps




book declaration {{{ NonTailReverse }}}
  def NonTail.reverse : List α → List α
    | [] => []
    | x :: xs => reverse xs ++ [x]
stop book declaration

evaluation steps {{{ NonTailReverseSteps }}}
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
end evaluation steps



book declaration {{{ TailReverse }}}
  def Tail.reverseHelper (soFar : List α) : List α → List α
    | [] => soFar
    | x :: xs => reverseHelper (x :: soFar) xs

  def Tail.reverse (xs : List α) : List α :=
    Tail.reverseHelper [] xs
stop book declaration

evaluation steps {{{ TailReverseSteps }}}
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

book declaration {{{ NonTailLength }}}
  def NonTail.length : List α → Nat
    | [] => 0
    | _ :: xs => NonTail.length xs + 1
stop book declaration

def Tail.lengthHelper (soFar : Nat) : List α → Nat
  | [] => soFar
  | _ :: xs => Tail.lengthHelper (soFar + 1) xs

def Tail.length (xs : List α) : Nat :=
  Tail.lengthHelper 0 xs


book declaration {{{ NonTailFact }}}
  def NonTail.factorial : Nat → Nat
    | 0 => 1
    | n + 1 => factorial n * (n + 1)
stop book declaration

def Tail.factHelper (soFar : Nat) : Nat → Nat
  | 0 => soFar
  | n + 1 => factHelper (soFar * (n + 1)) n

def Tail.factorial := factHelper 1

book declaration {{{ NonTailFilter }}}
  def NonTail.filter (p : α → Bool) : List α → List α
    | [] => []
    | x :: xs =>
      if p x then
        x :: filter p xs
      else
        filter p xs
stop book declaration

def Tail.filterHelper (accum : List α) (p : α → Bool) : List α → List α
  | [] => accum.reverse
  | x :: xs =>
    if p x then
      filterHelper (x :: accum) p xs
    else
      filterHelper accum p xs

def Tail.filter (p : α → Bool) := filterHelper [] p

bookExample {{{ tailFilterTest }}}
  Tail.filter (· > 3) [1,2,3,4,5,6]
  ===>
  [4,5,6]
end bookExample


expect error {{{ sumEqHelper0 }}}
  theorem helper_add_sum_accum (xs : List Nat) : (n : Nat) → n + Tail.sum xs = Tail.sumHelper n xs := by
    skip
message
"unsolved goals
xs : List Nat
⊢ ∀ (n : Nat), n + Tail.sum xs = Tail.sumHelper n xs"
end expect


expect error {{{ sumEqHelperBad0 }}}
  theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
      n + Tail.sum xs = Tail.sumHelper n xs := by
    skip
message
"unsolved goals
xs : List Nat
n : Nat
⊢ n + Tail.sum xs = Tail.sumHelper n xs"
end expect


expect error {{{ sumEqHelperBad1 }}}
  theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
      n + Tail.sum xs = Tail.sumHelper n xs := by
    induction xs with
    | nil => rfl
    | cons y ys ih => skip
message
"unsolved goals
case cons
n y : Nat
ys : List Nat
ih : n + Tail.sum ys = Tail.sumHelper n ys
⊢ n + Tail.sum (y :: ys) = Tail.sumHelper n (y :: ys)"
end expect


expect error {{{ sumEqHelperBad2 }}}
  theorem helper_add_sum_accum (xs : List Nat) (n : Nat) :
      n + Tail.sum xs = Tail.sumHelper n xs := by
    induction xs with
    | nil => rfl
    | cons y ys ih =>
      simp [Tail.sum, Tail.sumHelper]
message
"unsolved goals
case cons
n y : Nat
ys : List Nat
ih : n + Tail.sum ys = Tail.sumHelper n ys
⊢ n + Tail.sumHelper y ys = Tail.sumHelper (y + n) ys"
end expect

theorem helper_add_sum_accum (xs : List Nat) :
    (n : Nat) → n + Tail.sumHelper 0 xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => simp [Tail.sum, Tail.sumHelper]
  | cons y ys ih =>
    intro n
    simp [Tail.sumHelper]
    rw [←ih]
    rw [←Nat.add_assoc]
    rw [←Nat.add_comm y n]
    apply ih


expect error {{{ sumEq0 }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    skip
message
"unsolved goals
⊢ NonTail.sum = Tail.sum"
end expect



expect error {{{ sumEq1 }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    funext xs
message
"unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sum xs"
end expect


expect error {{{ sumEq2a }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    funext xs
    induction xs with
    | nil => skip
    | cons y ys ih => skip
message
"unsolved goals
case h.nil
⊢ NonTail.sum [] = Tail.sum []"
end expect

expect error {{{ sumEq2b }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    funext xs
    induction xs with
    | nil => skip
    | cons y ys ih => skip
message
"unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ NonTail.sum (y :: ys) = Tail.sum (y :: ys)"
end expect


expect error {{{ sumEq3 }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    funext xs
    induction xs with
    | nil => rfl
    | cons y ys ih => skip
message
"unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ NonTail.sum (y :: ys) = Tail.sum (y :: ys)"
end expect


expect error {{{ sumEq4 }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    funext xs
    induction xs with
    | nil => rfl
    | cons y ys ih =>
      simp [NonTail.sum, Tail.sum]
message
"unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + NonTail.sum ys = Tail.sumHelper 0 (y :: ys)"
end expect


expect error {{{ sumEq5 }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    funext xs
    induction xs with
    | nil => rfl
    | cons y ys ih =>
      simp [NonTail.sum, Tail.sum, Tail.sumHelper]
message
"unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + NonTail.sum ys = Tail.sumHelper y ys"
end expect


expect error {{{ sumEq6 }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    funext xs
    induction xs with
    | nil => rfl
    | cons y ys ih =>
      simp [NonTail.sum, Tail.sum, Tail.sumHelper]
      rw [ih]
message
"unsolved goals
case h.cons
y : Nat
ys : List Nat
ih : NonTail.sum ys = Tail.sum ys
⊢ y + Tail.sum ys = Tail.sumHelper y ys"
end expect


expect error {{{ nonTailEqHelper0 }}}
  theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
      (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
    skip
message
"unsolved goals
xs : List Nat
⊢ ∀ (n : Nat), n + NonTail.sum xs = Tail.sumHelper n xs"
end expect


expect error {{{ nonTailEqHelper1a }}}
  theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
      (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
    induction xs with
    | nil => skip
    | cons y ys ih => skip
message
"unsolved goals
case nil
⊢ ∀ (n : Nat), n + NonTail.sum [] = Tail.sumHelper n []"
end expect


expect error {{{ nonTailEqHelper1b }}}
  theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
      (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
    induction xs with
    | nil => skip
    | cons y ys ih => skip
message
"unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)"
end expect


expect error {{{ nonTailEqHelper2 }}}
  theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
      (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
    induction xs with
    | nil => intro n
    | cons y ys ih => skip
message
"unsolved goals
case nil
n : Nat
⊢ n + NonTail.sum [] = Tail.sumHelper n []"
end expect


expect error {{{ nonTailEqHelper3 }}}
  theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
      (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
    induction xs with
    | nil =>
      intro n
      rfl
    | cons y ys ih => skip
message
"unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
⊢ ∀ (n : Nat), n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)"
end expect


expect error {{{ nonTailEqHelper4 }}}
  theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
      (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
    induction xs with
    | nil =>
      intro n
      rfl
    | cons y ys ih =>
      intro n
message
"unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + NonTail.sum (y :: ys) = Tail.sumHelper n (y :: ys)"
end expect


expect error {{{ nonTailEqHelper5 }}}
  theorem non_tail_sum_eq_helper_accum (xs : List Nat) :
      (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
    induction xs with
    | nil =>
      intro n
      rfl
    | cons y ys ih =>
      intro n
      simp [NonTail.sum, Tail.sumHelper]
message
"unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + (y + NonTail.sum ys) = Tail.sumHelper (y + n) ys"
end expect


expect error {{{ nonTailEqHelper6 }}}
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
message
"unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + y + NonTail.sum ys = Tail.sumHelper (y + n) ys"
end expect


expect error {{{ nonTailEqHelper7 }}}
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
message
"unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ NonTail.sum ys + (n + y) = Tail.sumHelper (y + n) ys"
end expect


expect error {{{ nonTailEqHelper8 }}}
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
message
"unsolved goals
case cons
y : Nat
ys : List Nat
ih : ∀ (n : Nat), n + NonTail.sum ys = Tail.sumHelper n ys
n : Nat
⊢ n + y + NonTail.sum ys = Tail.sumHelper (n + y) ys"
end expect



book declaration {{{ nonTailEqHelperDone }}}
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
stop book declaration


bookExample type {{{ NatAddAssoc }}}
  Nat.add_assoc
  ===>
  (n m k : Nat) → (n + m) + k = n + (m + k)
end bookExample

bookExample type {{{ NatAddComm }}}
  Nat.add_comm
  ===>
  (n m : Nat) → n + m = m + n
end bookExample



expect error {{{ nonTailEqReal0 }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    funext xs
message
"unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sum xs"
end expect


expect error {{{ nonTailEqReal1 }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    funext xs
    simp [Tail.sum]
message
"unsolved goals
case h
xs : List Nat
⊢ NonTail.sum xs = Tail.sumHelper 0 xs"
end expect

bookExample type {{{ NatZeroAdd }}}
  Nat.zero_add
  ===>
  (n : Nat) → 0 + n = n
end bookExample

namespace Wak
axiom xs : List Nat

bookExample type {{{ NatZeroAddApplied }}}
  Nat.zero_add (NonTail.sum xs)
  ===>
  0 + NonTail.sum xs = NonTail.sum xs
end bookExample
end Wak

expect error {{{ nonTailEqReal2 }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    funext xs
    simp [Tail.sum]
    rw [←Nat.zero_add (NonTail.sum xs)]
message
"unsolved goals
case h
xs : List Nat
⊢ 0 + NonTail.sum xs = Tail.sumHelper 0 xs"
end expect


book declaration {{{ nonTailEqRealDone }}}
  theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
    funext xs
    simp [Tail.sum]
    rw [←Nat.zero_add (NonTail.sum xs)]
    exact non_tail_sum_eq_helper_accum xs 0
stop book declaration


theorem reverse_helper (xs : List α) : (ys : List α) → NonTail.reverse xs ++ ys = Tail.reverseHelper ys xs := by
  induction xs with
  | nil => intro ys; simp [NonTail.reverse, Tail.reverseHelper]
  | cons x xs ih =>
    intro ys
    simp [NonTail.reverse, Tail.reverseHelper, ← ih]

expect error {{{ reverseEqStart }}}
  theorem non_tail_reverse_eq_tail_reverse : @NonTail.reverse = @Tail.reverse := by
    funext α xs
message
"unsolved goals
case h.h
α : Type u_1
xs : List α
⊢ NonTail.reverse xs = Tail.reverse xs"
end expect

theorem non_tail_reverse_eq_tail_reverse : @NonTail.reverse = @Tail.reverse := by
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
