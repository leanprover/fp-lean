import Examples.Support

book declaration {{{ Plus }}}
  class Plus (α : Type) where
    plus : α → α → α
stop book declaration


bookExample type {{{ PlusType }}}
  Plus
  ===>
  Type → Type
end bookExample


book declaration {{{ PlusNat }}}
  instance : Plus Nat where
    plus := Nat.add
stop book declaration

expect info {{{ plusNatFiveThree }}}
  #eval Plus.plus 5 3
message
"8
"
end expect


book declaration {{{ openPlus }}}
open Plus (plus)
stop book declaration

expect info {{{ plusNatFiveThreeAgain }}}
  #eval plus 5 3
message
"8
"
end expect

#check plus

bookExample type {{{ plusType }}}
  @Plus.plus
  ===>
  {α : Type} → [Plus α] → α → α → α
end bookExample


book declaration {{{ Pos }}}
  inductive Pos : Type where
    | one : Pos
    | succ : Pos → Pos
stop book declaration


expect error {{{ sevenOops }}}
  def seven : Pos := 7
message
"failed to synthesize instance
  OfNat Pos 7"
end expect


book declaration {{{ seven }}}
  def seven : Pos :=
    Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
stop book declaration


expect error {{{ fourteenOops }}}
  def fourteen : Pos := seven + seven
message
"failed to synthesize instance
  HAdd Pos Pos ?m.269"
end expect

expect error {{{ fortyNineOops }}}
  def fortyNine : Pos := seven * seven
message
"failed to synthesize instance
  HMul Pos Pos ?m.269"
end expect



book declaration {{{ PlusPos }}}
  def Pos.plus : Pos → Pos → Pos
    | Pos.one, k => Pos.succ k
    | Pos.succ n, k => Pos.succ (n.plus k)

  instance : Plus Pos where
    plus := Pos.plus

  def fourteen : Pos := plus seven seven
stop book declaration


book declaration {{{ AddPos }}}
  instance : Add Pos where
    add := Pos.plus
stop book declaration

namespace Extra
book declaration {{{ betterFourteen }}}
  def fourteen : Pos := seven + seven
stop book declaration
end Extra

namespace Foo

axiom x : Nat
axiom y : Nat

evaluation steps {{{ plusDesugar }}}
  x + y
  ===>
  Add.add x y
end evaluation steps

end Foo



book declaration {{{ posToNat }}}
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
stop book declaration

namespace Argh

book declaration {{{ posToStringStructure }}}
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
    | Pos.one => "Pos.one"
    | Pos.succ n => paren s!"Pos.succ {posToString false n}"
stop book declaration

book declaration {{{ UglyToStringPos }}}
instance : ToString Pos where
  toString := posToString true
stop book declaration


expect info {{{ sevenLong }}}
  #eval s!"There are {seven}"
message
"\"There are Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))\"
"
end expect

end Argh

section Blah


book declaration {{{ PosToStringNat }}}
instance : ToString Pos where
  toString x := toString (x.toNat)
stop book declaration

expect info {{{ sevenShort }}}
  #eval s!"There are {seven}"
message
"\"There are 7\"
"
end expect
end Blah

expect info {{{ sevenEvalStr }}}
  #eval seven
message
"7
"
end expect


bookExample type {{{ printlnType }}}
  @IO.println
  ===>
  {α : Type} → [ToString α] → α → IO Unit
end bookExample

namespace Foo

evaluation steps {{{ timesDesugar }}}
  x * y
  ===>
  Mul.mul x y
end evaluation steps

end Foo



book declaration {{{ PosMul }}}
  def Pos.mul : Pos → Pos → Pos
    | Pos.one, k => k
    | Pos.succ n, k => n.mul k + k

  instance : Mul Pos where
    mul := Pos.mul
stop book declaration


expect info {{{ muls }}}
  #eval [seven * Pos.one,
         seven * seven,
         Pos.succ Pos.one * seven]
message
"[7, 49, 14]
"
end expect

namespace NatLits


book declaration {{{ OfNat }}}
class OfNat (α : Type) (_ : Nat) where
  ofNat : α
stop book declaration

end NatLits

similar datatypes OfNat NatLits.OfNat


book declaration {{{ LT4 }}}
  inductive LT4 where
    | zero
    | one
    | two
    | three
  deriving Repr
stop book declaration


book declaration {{{ LT4ofNat }}}
  instance : OfNat LT4 Nat.zero where
    ofNat := LT4.zero

  instance : OfNat LT4 (Nat.succ Nat.zero) where
    ofNat := LT4.one

  instance : OfNat LT4 2 where
    ofNat := LT4.two

  instance : OfNat LT4 3 where
    ofNat := LT4.three
stop book declaration
