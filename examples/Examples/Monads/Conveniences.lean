import ExampleSupport
import Examples.Classes

set_option linter.unusedVariables false

-- ANCHOR: SumNames
example := Sum
example := @Sum.inl
example := @Sum.inr
section
open Sum
example := @inl
example := @inr
end
-- ANCHOR_END: SumNames

namespace Old
variable {α : Type}
-- ANCHOR: equalHuhOld
def equal? [BEq α] (x : α) (y : α) : Option α :=
  if x == y then
    some x
  else
    none
-- ANCHOR_END: equalHuhOld
end Old


namespace New
variable {α : Type}
-- ANCHOR: equalHuhNew
def equal? [BEq α] (x y : α) : Option α :=
  if x == y then
    some x
  else
    none
-- ANCHOR_END: equalHuhNew
end New

example [BEq α] : Old.equal? (α := α) = New.equal? := by rfl

namespace Old

-- ANCHOR: mirrorOld
def BinTree.mirror : BinTree α → BinTree α
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)
-- ANCHOR_END: mirrorOld
end Old


-- ANCHOR: mirrorNew
def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)
-- ANCHOR_END: mirrorNew

-- ANCHOR: BinTreeEmpty
def BinTree.empty : BinTree α := .leaf
-- ANCHOR_END: BinTreeEmpty

/-- info:
BinTree.empty : BinTree Nat
-/
#check_msgs in
-- ANCHOR: emptyDot
#check (.empty : BinTree Nat)
-- ANCHOR_END: emptyDot

-- ANCHOR: Weekday
inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
deriving Repr
-- ANCHOR_END: Weekday

namespace A

-- ANCHOR: isWeekendA
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | Weekday.saturday => true
  | Weekday.sunday => true
  | _ => false
-- ANCHOR_END: isWeekendA
end A

namespace B
-- ANCHOR: isWeekendB
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday => true
  | .sunday => true
  | _ => false
-- ANCHOR_END: isWeekendB
end B

namespace C
-- ANCHOR: isWeekendC
def Weekday.isWeekend (day : Weekday) : Bool :=
  match day with
  | .saturday | .sunday => true
  | _ => false
-- ANCHOR_END: isWeekendC
end C

namespace D
variable {α : Type}
-- ANCHOR: isWeekendD
def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false
-- ANCHOR_END: isWeekendD
end D

variable {α : Type}

-- ANCHOR: condense
def condense : α ⊕ α → α
  | .inl x | .inr x => x
-- ANCHOR_END: condense


-- ANCHOR: stringy
def stringy : Nat ⊕ Weekday → String
  | .inl x | .inr x => s!"It is {repr x}"
-- ANCHOR_END: stringy

#eval stringy (.inl 5)
#eval stringy (.inr .monday)


-- ANCHOR: getTheNat
def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, x) | .inr (n, y) => n
-- ANCHOR_END: getTheNat



/-- error: Unknown identifier `x` -/
#check_msgs in
-- ANCHOR: getTheAlpha
def getTheAlpha : (Nat × α) ⊕ (Nat × α) → α
  | .inl (n, x) | .inr (n, y) => x
-- ANCHOR_END: getTheAlpha

-- ANCHOR: getTheString
def str := "Some string"

def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (n, str) | .inr (n, y) => str
-- ANCHOR_END: getTheString


/-- info:
"twenty"
-/
#check_msgs in
-- ANCHOR: getOne
#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String))
-- ANCHOR_END: getOne


/-- info:
"Some string"
-/
#check_msgs in
-- ANCHOR: getTwo
#eval getTheString (.inr (20, "twenty"))
-- ANCHOR_END: getTwo
