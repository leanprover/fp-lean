import ExampleSupport

namespace Orders
-- ANCHOR: less
class LE (α : Type u) where
  le : α → α → Prop

class LT (α : Type u) where
  lt : α → α → Prop
-- ANCHOR_END: less

attribute [inherit_doc _root_.LE] LE
attribute [inherit_doc _root_.LE.le] LE.le

attribute [inherit_doc _root_.LT] LT
attribute [inherit_doc _root_.LT.lt] LT.lt

-- ANCHOR: NatLe
inductive Nat.le (n : Nat) : Nat → Prop
  | refl : Nat.le n n
  | step : Nat.le n m → Nat.le n (m + 1)
-- ANCHOR_END: NatLe

attribute [inherit_doc _root_.Nat.le] Nat.le
attribute [inherit_doc _root_.Nat.le.refl] Nat.le.refl
attribute [inherit_doc _root_.Nat.le.step] Nat.le.step


-- ANCHOR: leNames
example := @Nat.le.refl
example := @Nat.le.step
-- ANCHOR_END: leNames

--ANCHOR: ForMArr
example {α m} := ForM m (Array α)
--ANCHOR_END: ForMArr

-- ANCHOR: LENat
instance : LE Nat where
  le := Nat.le
-- ANCHOR_END: LENat


-- ANCHOR: NatLt
def Nat.lt (n m : Nat) : Prop :=
  Nat.le (n + 1) m

instance : LT Nat where
  lt := Nat.lt
-- ANCHOR_END: NatLt

end Orders
example := Nat.le

-- ANCHOR: EasyToProve
inductive EasyToProve : Prop where
  | heresTheProof : EasyToProve
-- ANCHOR_END: EasyToProve


-- ANCHOR: fairlyEasy
theorem fairlyEasy : EasyToProve := by
  constructor
-- ANCHOR_END: fairlyEasy

namespace Argh
-- ANCHOR: True
inductive True : Prop where
  | intro : True
-- ANCHOR_END: True
end Argh


-- ANCHOR: IsThree
inductive IsThree : Nat → Prop where
  | isThree : IsThree 3
-- ANCHOR_END: IsThree


-- ANCHOR: IsFive
inductive IsFive : Nat → Prop where
  | isFive : IsFive 5
-- ANCHOR_END: IsFive


-- ANCHOR: threeIsThree
theorem three_is_three : IsThree 3 := by
  constructor
-- ANCHOR_END: threeIsThree

discarding
/-- error:
unsolved goals
n : Nat
⊢ IsThree n → IsFive (n + 2)
-/
#check_msgs in
-- ANCHOR: threePlusTwoFive0
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  skip
-- ANCHOR_END: threePlusTwoFive0
stop discarding

-- ANCHOR: various
example := 3 + 2
example := False
example {A} := [(Not A), (A → False), ¬ A]
-- ANCHOR_END: various

discarding
/-- error:
unsolved goals
n : Nat
three : IsThree n
⊢ IsFive (n + 2)
-/
#check_msgs in
-- ANCHOR: threePlusTwoFive1
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
-- ANCHOR_END: threePlusTwoFive1
stop discarding

discarding
/--
error: Tactic `constructor` failed: no applicable constructor found

n : Nat
three : IsThree n
⊢ IsFive (n + 2)
-/
#check_msgs in
-- ANCHOR: threePlusTwoFive1a
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  constructor
-- ANCHOR_END: threePlusTwoFive1a
stop discarding

discarding
/-- error:
unsolved goals
case isThree
⊢ IsFive (3 + 2)
-/
#check_msgs in
-- ANCHOR: threePlusTwoFive2
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => skip
-- ANCHOR_END: threePlusTwoFive2
stop discarding

discarding
-- ANCHOR: threePlusTwoFive3
theorem three_plus_two_five : IsThree n → IsFive (n + 2) := by
  intro three
  cases three with
  | isThree => constructor
-- ANCHOR_END: threePlusTwoFive3
stop discarding

discarding
/-- error:
unsolved goals
⊢ ¬IsThree 4
-/
#check_msgs in
-- ANCHOR: fourNotThree0
theorem four_is_not_three : ¬ IsThree 4 := by
  skip
-- ANCHOR_END: fourNotThree0
stop discarding

discarding
/-- error:
unsolved goals
⊢ IsThree 4 → False
-/
#check_msgs in
-- ANCHOR: fourNotThree1
theorem four_is_not_three : ¬ IsThree 4 := by
  unfold Not
-- ANCHOR_END: fourNotThree1
stop discarding

discarding
/-- error:
unsolved goals
h : IsThree 4
⊢ False
-/
#check_msgs in
-- ANCHOR: fourNotThree2
theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
-- ANCHOR_END: fourNotThree2
stop discarding

discarding
-- ANCHOR: fourNotThreeDone
theorem four_is_not_three : ¬ IsThree 4 := by
  intro h
  cases h
-- ANCHOR_END: fourNotThreeDone
stop discarding


-- ANCHOR: four_le_seven
theorem four_le_seven : 4 ≤ 7 :=
  open Nat.le in
  step (step (step refl))
-- ANCHOR_END: four_le_seven

-- ANCHOR: four_lt_seven
theorem four_lt_seven : 4 < 7 :=
  open Nat.le in
  step (step refl)
-- ANCHOR_END: four_lt_seven

-- ANCHOR: four_lt_seven_alt
example : (4 < 7) = (5 ≤ 7) := rfl
-- ANCHOR_END: four_lt_seven_alt

namespace WithFor

  def Array.map (f : α → β) (arr : Array α) : Array β := Id.run do
    let mut out : Array β := Array.empty
    for x in arr do
      out := out.push (f x)
    pure out

end WithFor



discarding
/-- error:
failed to prove index is valid, possible solutions:
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
⊢ i < arr.size
-/
#check_msgs in
-- ANCHOR: mapHelperIndexIssue
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
-- ANCHOR_END: mapHelperIndexIssue
stop discarding

discarding
-- ANCHOR: arrayMapHelperTermIssue
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
-- ANCHOR_END: arrayMapHelperTermIssue
stop discarding

-- ANCHOR: ArrayMapHelperOk
def arrayMapHelper (f : α → β) (arr : Array α)
    (soFar : Array β) (i : Nat) : Array β :=
  if inBounds : i < arr.size then
    arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
  else soFar
termination_by arr.size - i
-- ANCHOR_END: ArrayMapHelperOk

namespace TailRec

-- ANCHOR: ArrayMap
def Array.map (f : α → β) (arr : Array α) : Array β :=
  arrayMapHelper f arr Array.empty 0
-- ANCHOR_END: ArrayMap

end TailRec


-- ANCHOR: ArrayFindHelper
def findHelper (arr : Array α) (p : α → Bool)
    (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
-- ANCHOR_END: ArrayFindHelper

-- ANCHOR: ArrayFind
def Array.find (arr : Array α) (p : α → Bool) :
    Option (Nat × α) :=
  findHelper arr p 0
-- ANCHOR_END: ArrayFind

namespace Huh
/-- info:
Try this: termination_by arr.size - i
-/
#check_msgs in
-- ANCHOR: ArrayFindHelperSugg
def findHelper (arr : Array α) (p : α → Bool)
    (i : Nat) : Option (Nat × α) :=
  if h : i < arr.size then
    let x := arr[i]
    if p x then
      some (i, x)
    else findHelper arr p (i + 1)
  else none
termination_by?
-- ANCHOR_END: ArrayFindHelperSugg
end Huh
