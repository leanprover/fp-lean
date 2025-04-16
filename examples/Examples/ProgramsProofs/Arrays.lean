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


book declaration {{{ NatLt }}}
  def Nat.lt (n m : Nat) : Prop :=
    Nat.le (n + 1) m

  instance : LT Nat where
    lt := Nat.lt
stop book declaration

end Orders
example := Nat.le

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
  -- TODO was simp, check text
  theorem four_is_not_three : ¬ IsThree 4 := by
    unfold Not
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



book declaration {{{ four_le_seven }}}
  theorem four_le_seven : 4 ≤ 7 :=
    open Nat.le in
    step (step (step refl))
stop book declaration

book declaration {{{ four_lt_seven }}}
  theorem four_lt_seven : 4 < 7 :=
    open Nat.le in
    step (step refl)
stop book declaration


namespace WithFor

  def Array.map (f : α → β) (arr : Array α) : Array β := Id.run do
    let mut out : Array β := Array.empty
    for x in arr do
      out := out.push (f x)
    pure out

end WithFor




expect error {{{ mapHelperIndexIssue }}}
  def arrayMapHelper (f : α → β) (arr : Array α) (soFar : Array β) (i : Nat) : Array β :=
    if i < arr.size then
      arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
    else soFar
message
"failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.1290
β : Type ?u.1293
f : α → β
arr : Array α
soFar : Array β
i : Nat
⊢ i < arr.size"
end expect


expect error {{{ arrayMapHelperTermIssue }}}
  -- TODO this was a termination issue before, now it Just Works - fix text because this error is bogus
  def arrayMapHelper (f : α → β) (arr : Array α) (soFar : Array β) (i : Nat) : Array β :=
    if inBounds : i < arr.size then
      let x : String := 55
      arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
    else soFar
message
"failed to synthesize
  OfNat String 55
numerals are polymorphic in Lean, but the numeral `55` cannot be used in a context where the expected type is
  String
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command."
end expect

book declaration {{{ ArrayMapHelperOk }}}
  -- TODO this was a termination issue before, now it Just Works - no help needed
  def arrayMapHelper (f : α → β) (arr : Array α) (soFar : Array β) (i : Nat) : Array β :=
    if inBounds : i < arr.size then
      arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
    else soFar
  -- TODO termination_by arrayMapHelper _ arr _ i _ => arr.size - i
stop book declaration

namespace TailRec

book declaration {{{ ArrayMap }}}
  def Array.map (f : α → β) (arr : Array α) : Array β :=
    arrayMapHelper f arr Array.empty 0
stop book declaration

end TailRec


book declaration {{{ ArrayFindHelper }}}
  def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Nat × α) :=
    if h : i < arr.size then
      let x := arr[i]
      if p x then
        some (i, x)
      else findHelper arr p (i + 1)
    else none
  -- TODO check termination_by findHelper arr p i => arr.size - i
stop book declaration

book declaration {{{ ArrayFind }}}
  def Array.find (arr : Array α) (p : α → Bool) : Option (Nat × α) :=
    findHelper arr p 0
stop book declaration
