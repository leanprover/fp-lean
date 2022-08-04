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
  HAdd Pos Pos ?m.292"
end expect

expect error {{{ fortyNineOops }}}
  def fortyNine : Pos := seven * seven
message
"failed to synthesize instance
  HMul Pos Pos ?m.292"
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
"[7, 49, 14]"
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
  instance : OfNat LT4 0 where
    ofNat := LT4.zero

  instance : OfNat LT4 1 where
    ofNat := LT4.one

  instance : OfNat LT4 2 where
    ofNat := LT4.two

  instance : OfNat LT4 3 where
    ofNat := LT4.three
stop book declaration


expect info {{{ LT4three }}}
  #eval (3 : LT4)
message
  "LT4.three"
end expect

expect info {{{ LT4zero }}}
  #eval (0 : LT4)
message
  "LT4.zero"
end expect

expect error {{{ LT4four }}}
  #eval (4 : LT4)
message
  "failed to synthesize instance
  OfNat LT4 4"
end expect



book declaration {{{ OfNatPos }}}
  instance : OfNat Pos (n + 1) where
    ofNat :=
      let rec natPlusOne : Nat → Pos
        | 0 => Pos.one
        | k+1 => Pos.succ (natPlusOne k)
      natPlusOne n
stop book declaration


book declaration {{{ eight }}}
  def eight : Pos := 8
stop book declaration


expect error {{{ zeroBad }}}
  def zero : Pos := 0
message
"failed to synthesize instance
  OfNat Pos 0"
end expect

namespace AltPos


book declaration {{{ AltPos }}}
  structure Pos where
    succ ::
    pred : Nat
stop book declaration

end AltPos

bookExample type {{{ printlnType }}}
  @IO.println
  ===>
  {α : Type} → [ToString α] → α → IO Unit
end bookExample


book declaration {{{ ListSum }}}
  def List.sum [Add α] [OfNat α 0] : List α → α
    | [] => 0
    | x :: xs => x + xs.sum
stop book declaration


book declaration {{{ fourNats }}}
  def fourNats : List Nat := [1, 2, 3, 4]
stop book declaration


book declaration {{{ fourPos }}}
  def fourPos : List Pos := [1, 2, 3, 4]
stop book declaration


expect info {{{ fourNatsSum }}}
  #eval fourNats.sum
message
"10"
end expect


expect error {{{ fourPosSum }}}
  #eval fourPos.sum
message
"failed to synthesize instance
  OfNat Pos 0"
end expect

namespace PointStuff


book declaration {{{ PPoint }}}
  structure PPoint (α : Type) where
    x : α
    y : α
  deriving Repr
stop book declaration


book declaration {{{ AddPPoint }}}
  instance [Add α] : Add (PPoint α) where
    add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }
stop book declaration

end PointStuff



namespace Foo

evaluation steps {{{ minusDesugar }}}
  x - y
  ===>
  Sub.sub x y
end evaluation steps

evaluation steps {{{ divDesugar }}}
  x / y
  ===>
  Div.div x y
end evaluation steps

evaluation steps {{{ modDesugar }}}
  x % y
  ===>
  Mod.mod x y
end evaluation steps

evaluation steps {{{ powDesugar }}}
  x ^ y
  ===>
  Pow.pow x y
end evaluation steps

end Foo

namespace OverloadedInt

axiom x : Int

evaluation steps {{{ negDesugar }}}
  (- x)
  ===>
  Neg.neg x
end evaluation steps

end OverloadedInt

namespace OverloadedBits

axiom x : UInt8
axiom y : UInt8

evaluation steps {{{ bAndDesugar }}}
  x &&& y
  ===>
  AndOp.and x y
end evaluation steps

evaluation steps {{{ bOrDesugar }}}
  x ||| y
  ===>
  OrOp.or x y
end evaluation steps

evaluation steps {{{ bXorDesugar }}}
  x ^^^ y
  ===>
  Xor.xor x y
end evaluation steps

evaluation steps {{{ complementDesugar }}}
  ~~~ x
  ===>
  Complement.complement x
end evaluation steps

evaluation steps {{{ shrDesugar }}}
  x >>> y
  ===>
  ShiftRight.shiftRight x y
end evaluation steps

evaluation steps {{{ shlDesugar }}}
  x <<< y
  ===>
  ShiftLeft.shiftLeft x y
end evaluation steps

evaluation steps {{{ beqDesugar }}}
  x == y
  ===>
  BEq.beq x y
end evaluation steps



end OverloadedBits

