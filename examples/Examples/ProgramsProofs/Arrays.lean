import Examples.Support

namespace Orders
book declaration {{{ less }}}
  class LE (α : Type u) where
    le : α → α → Prop

  class LT (α : Type u) where
    lt : α → α → Prop
stop book declaration


book declaration {{{ NatLe }}}
  inductive Nat.le (n : Nat) : Nat → Prop
    | refl : Nat.le n n
    | step : Nat.le n m → Nat.le n (m + 1)
stop book declaration

book declaration {{{ LENat }}}
  instance : LE Nat where
    le := Nat.le
stop book declaration

end Orders


book declaration {{{ EasyToProve }}}
  inductive EasyToProve : Prop where
    | heresTheProof : EasyToProve
stop book declaration


book declaration {{{ fairlyEasy }}}
  theorem fairlyEasy : EasyToProve := by
    constructor
stop book declaration

namespace Argh
book declaration {{{ True }}}
  inductive True : Prop where
    | intro : True
stop book declaration
end Argh


book declaration {{{ IsThree }}}
  inductive IsThree : Nat → Prop where
    | isThree : IsThree 3
stop book declaration


book declaration {{{ IsFive }}}
  inductive IsFive : Nat → Prop where
    | isFive : IsFive 5
stop book declaration


book declaration {{{ threeIsThree }}}
  theorem three_is_three : IsThree 3 := by
    constructor
stop book declaration


expect error {{{ threePlusTwoFive0 }}}
  theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
    skip
message
"unsolved goals
n : Nat
⊢ IsThree n → IsFive (n + 2)"
end expect

expect error {{{ threePlusTwoFive1 }}}
  theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
    intro three
message
"unsolved goals
n : Nat
three : IsThree n
⊢ IsFive (n + 2)"
end expect


expect error {{{ threePlusTwoFive1a }}}
  theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
    intro three
    constructor
message
"tactic 'constructor' failed, no applicable constructor found
n : Nat
three : IsThree n
⊢ IsFive (n + 2)"
end expect

expect error {{{ threePlusTwoFive2 }}}
  theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
    intro three
    cases three with
    | isThree => skip
message
"unsolved goals
case isThree
⊢ IsFive (3 + 2)"
end expect


book declaration {{{ threePlusTwoFive3 }}}
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => constructor
stop book declaration


expect error {{{ fourNotThree0 }}}
  theorem four_is_not_three : ¬ IsThree 4 := by
    skip
message
"unsolved goals
⊢ ¬IsThree 4"
end expect


expect error {{{ fourNotThree1 }}}
  theorem four_is_not_three : ¬ IsThree 4 := by
    simp [Not]
message
"unsolved goals
⊢ IsThree 4 → False"
end expect


expect error {{{ fourNotThree2 }}}
  theorem four_is_not_three : ¬ IsThree 4 := by
    intro h
message
"unsolved goals
h : IsThree 4
⊢ False"
end expect


book declaration {{{ fourNotThreeDone }}}
theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
  cases h
stop book declaration
