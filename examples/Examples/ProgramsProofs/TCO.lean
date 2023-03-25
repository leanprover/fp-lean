import Examples.Support



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


theorem helper_simulates_non_tail (xs : List Nat) : (n : Nat) → n + Tail.sum xs = Tail.sumHelper n xs := by
  induction xs with
  | nil => simp_arith [Tail.sum, Tail.sumHelper]
  | cons y ys ih =>
    intro n
    simp [Tail.sum, Tail.sumHelper]
    rw [←ih]
    rw [←Nat.add_assoc]
    rw [←Nat.add_comm y n]
    apply ih

theorem non_tail_eq_tail (xs : List Nat) : NonTail.sum xs = Tail.sum xs := by
  induction xs with
  | nil => simp [NonTail.sum, Tail.sum]
  | cons y ys ih =>
    simp [NonTail.sum, Tail.sum, Tail.sumHelper]
    rw [ih]
    apply helper_simulates_non_tail

def bigList (n : Nat) (soFar : List Nat) : List Nat :=
  match n with
  | 0 => soFar
  | k + 1 =>
    bigList k (2 * n :: soFar)

-- #eval timeit "hello" (IO.println theBigList.length)

-- #eval timeit "a" (IO.println <| Tail.sum theBigList)

-- #eval timeit "b" (IO.println <| NonTail.sum theBigList)
