import Examples.Support
import Examples.Classes

namespace Old
book declaration {{{ equalHuhOld }}}
  def equal? [BEq α] (x : α) (y : α) : Option α :=
    if x == y then
      some x
    else
      none
stop book declaration
end Old


namespace New
book declaration {{{ equalHuhNew }}}
  def equal? [BEq α] (x y : α) : Option α :=
    if x == y then
      some x
    else
      none
stop book declaration
end New

example [BEq α] : Old.equal? (α := α) = New.equal? := by rfl

namespace Old

book declaration {{{ mirrorOld }}}
  def BinTree.mirror : BinTree α → BinTree α
    | BinTree.leaf => BinTree.leaf
    | BinTree.branch l x r => BinTree.branch (mirror r) x (mirror l)
stop book declaration
end Old


book declaration {{{ mirrorNew }}}
  def BinTree.mirror : BinTree α → BinTree α
    | .leaf => .leaf
    | .branch l x r => .branch (mirror r) x (mirror l)
stop book declaration

book declaration {{{ BinTreeEmpty }}}
  def BinTree.empty : BinTree α := .leaf
stop book declaration

expect info {{{ emptyDot }}}
  #check (.empty : BinTree Nat)
message
"BinTree.empty : BinTree Nat"
end expect

book declaration {{{ Weekday }}}
  inductive Weekday where
    | monday
    | tuesday
    | wednesday
    | thursday
    | friday
    | saturday
    | sunday
    deriving Repr
stop book declaration

namespace A

book declaration {{{ isWeekendA }}}
  def Weekday.isWeekend (day : Weekday) : Bool :=
    match day with
    | Weekday.saturday => true
    | Weekday.sunday => true
    | _ => false
stop book declaration
end A

namespace B
book declaration {{{ isWeekendB }}}
  def Weekday.isWeekend (day : Weekday) : Bool :=
    match day with
    | .saturday => true
    | .sunday => true
    | _ => false
stop book declaration
end B

namespace C
book declaration {{{ isWeekendC }}}
  def Weekday.isWeekend (day : Weekday) : Bool :=
    match day with
    | .saturday | .sunday => true
    | _ => false
stop book declaration
end C

namespace D
book declaration {{{ isWeekendD }}}
  def Weekday.isWeekend : Weekday → Bool
    | .saturday | .sunday => true
    | _ => false
stop book declaration
end D



book declaration {{{ condense }}}
  def condense : α ⊕ α → α
    | .inl x | .inr x => x
stop book declaration


book declaration {{{ stringy }}}
  def stringy : Nat ⊕ Weekday → String
    | .inl x | .inr x => s!"It is {repr x}"
stop book declaration

#eval stringy (.inl 5)
#eval stringy (.inr .monday)


book declaration {{{ getTheNat }}}
  def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
    | .inl (n, x) | .inr (n, y) => n
stop book declaration



expect error {{{ getTheAlpha }}}
  def getTheAlpha : (Nat × α) ⊕ (Nat × α) → α
    | .inl (n, x) | .inr (n, y) => x
message
"unknown identifier 'x'"
end expect

book declaration {{{ getTheString }}}
  def str := "Some string"

  def getTheString : (Nat × String) ⊕ (Nat × β) → String
    | .inl (n, str) | .inr (n, y) => str
stop book declaration


expect info {{{ getOne }}}
  #eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String))
message
"\"twenty\""
end expect


expect info {{{ getTwo }}}
  #eval getTheString (.inr (20, "twenty"))
message
"\"Some string\""
end expect
