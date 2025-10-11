import ExampleSupport

set_option guard_msgs.diff true

-- Names in the chapter introduction
-- ANCHOR: chapterIntro
example := Add
example := Nat
example := Int
example := [HAnd, HOr, HXor, HShiftRight, HShiftLeft]
example := [Complement]
example := [And, Or]
example := ToString Nat
example := @List.sum
example := @Ord.compare
example := String.intercalate
example := String.trim
example := "Hello!"
example := [HAdd]
example := Unit.unit
example := Float.toString
example := @List.map
example {α β : _} := Coe α β
example := (Prop, Type)
section
open System
example := FilePath
end
-- ANCHOR_END: chapterIntro

-- ANCHOR: types
example : Bool := true

-- ANCHOR_END: types

-- ANCHOR: arrVsList
section
variable {α : Type}
example := Array α → List α
open List
#check cons
example := @Array.size
end
-- ANCHOR_END: arrVsList

-- ANCHOR: posrec
section
variable (n : Nat) (α : Type)
example := [n, n + 1]
example := α
end
-- ANCHOR_END: posrec

-- ANCHOR: Plus
class Plus (α : Type) where
  plus : α → α → α
-- ANCHOR_END: Plus


-- ANCHOR: PlusType
example : Type → Type := Plus
-- ANCHOR_END: PlusType


-- ANCHOR: PlusNat
instance : Plus Nat where
  plus := Nat.add
-- ANCHOR_END: PlusNat


/-- info:
8
-/
#check_msgs in
-- ANCHOR: plusNatFiveThree
#eval Plus.plus 5 3
-- ANCHOR_END: plusNatFiveThree


-- ANCHOR: openPlus
open Plus (plus)
-- ANCHOR_END: openPlus

/-- info:
8
-/
#check_msgs in
-- ANCHOR: plusNatFiveThreeAgain
#eval plus 5 3
-- ANCHOR_END: plusNatFiveThreeAgain

#check plus

-- ANCHOR: plusType
example : {α : Type} → [Plus α] → α → α → α := @Plus.plus
-- ANCHOR_END: plusType

/--
error: failed to synthesize
  Plus Float

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: plusFloatFail
#eval plus 5.2 917.25861
-- ANCHOR_END: plusFloatFail

-- ANCHOR: PlusFloat
example := Plus Float
-- ANCHOR_END: PlusFloat

-- ANCHOR: Nat.zero
section
open Nat
example := zero
end
-- ANCHOR_END: Nat.zero

-- ANCHOR: Pos
inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
-- ANCHOR_END: Pos

-- ANCHOR: PosStuff
example := Option Pos
example := Zero Pos
example := Nat.zero
-- ANCHOR_END: PosStuff

discarding
/--
error: failed to synthesize
  OfNat Pos 7
numerals are polymorphic in Lean, but the numeral `7` cannot be used in a context where the expected type is
  Pos
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: sevenOops
def seven : Pos := 7
-- ANCHOR_END: sevenOops
stop discarding

-- ANCHOR: seven
def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
-- ANCHOR_END: seven

discarding
/--
error: failed to synthesize
  HAdd Pos Pos ?m.3

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: fourteenOops
def fourteen : Pos := seven + seven
-- ANCHOR_END: fourteenOops
stop discarding

/--
error: failed to synthesize
  HMul Pos Pos ?m.3

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: fortyNineOops
def fortyNine : Pos := seven * seven
-- ANCHOR_END: fortyNineOops



-- ANCHOR: PlusPos
def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)

instance : Plus Pos where
  plus := Pos.plus

def fourteen : Pos := plus seven seven
-- ANCHOR_END: PlusPos


-- ANCHOR: AddPos
instance : Add Pos where
  add := Pos.plus
-- ANCHOR_END: AddPos

namespace Extra
-- ANCHOR: betterFourteen
def fourteen : Pos := seven + seven
-- ANCHOR_END: betterFourteen
end Extra

namespace Foo

variable {α β : Type} (x : α) (y : β) [HAdd α β γ]



-- ANCHOR: plusDesugar
example : x + y = HAdd.hAdd x y := rfl
-- ANCHOR_END: plusDesugar


end Foo

-- ANCHOR: readFile
example : System.FilePath → IO String := IO.FS.readFile
-- ANCHOR_END: readFile

-- ANCHOR: fileDumper
def fileDumper : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStr "Which file? "
  stdout.flush
  let f := (← stdin.getLine).trim
  stdout.putStrLn s!"'The file {f}' contains:"
  stdout.putStrLn (← IO.FS.readFile f)
-- ANCHOR_END: fileDumper

-- ANCHOR: posToNat
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
-- ANCHOR_END: posToNat

namespace Argh

-- ANCHOR: posToStringStructure
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
-- ANCHOR_END: posToStringStructure

-- ANCHOR: UglyToStringPos
instance : ToString Pos where
  toString := posToString true
-- ANCHOR_END: UglyToStringPos


/-- info:
"There are Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))"
-/
#check_msgs in
-- ANCHOR: sevenLong
#eval s!"There are {seven}"
-- ANCHOR_END: sevenLong

end Argh

section Blah


-- ANCHOR: PosToStringNat
instance : ToString Pos where
  toString x := toString (x.toNat)
-- ANCHOR_END: PosToStringNat

/-- info:
"There are 7"
-/
#check_msgs in
-- ANCHOR: sevenShort
#eval s!"There are {seven}"
-- ANCHOR_END: sevenShort
end Blah

/-- info:
7
-/
#check_msgs in
-- ANCHOR: sevenEvalStr
#eval seven
-- ANCHOR_END: sevenEvalStr



namespace Foo
variable {α β : Type} (x : α) (y : β) [HMul α β γ]

-- ANCHOR: timesDesugar
example : x * y = HMul.hMul x y := by rfl
-- ANCHOR_END: timesDesugar


end Foo



-- ANCHOR: PosMul
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul
-- ANCHOR_END: PosMul


/-- info:
[7, 49, 14]
-/
#check_msgs in
-- ANCHOR: muls
#eval [seven * Pos.one,
       seven * seven,
       Pos.succ Pos.one * seven]
-- ANCHOR_END: muls

namespace NatLits

-- ANCHOR: Zero
class Zero (α : Type) where
  zero : α
-- ANCHOR_END: Zero

-- ANCHOR: One
class One (α : Type) where
  one : α
-- ANCHOR_END: One

-- ANCHOR: OneExamples
example {α : Type} := [One α, OfNat α 1]
-- ANCHOR_END: OneExamples

-- Test that One works with OfNat _ 1
example [_root_.One α] : α := 1

-- Test the other ways around
example [_root_.OfNat α 1] : _root_.One α := inferInstance

example [_root_.OfNat α 0] : _root_.Zero α := inferInstance


-- ANCHOR: OfNat
class OfNat (α : Type) (_ : Nat) where
  ofNat : α
-- ANCHOR_END: OfNat

end NatLits
similar datatypes Zero NatLits.Zero
similar datatypes One NatLits.One
similar datatypes OfNat NatLits.OfNat


-- ANCHOR: LT4
inductive LT4 where
  | zero
  | one
  | two
  | three
-- ANCHOR_END: LT4


-- ANCHOR: LT4ofNat
instance : OfNat LT4 0 where
  ofNat := LT4.zero

instance : OfNat LT4 1 where
  ofNat := LT4.one

instance : OfNat LT4 2 where
  ofNat := LT4.two

instance : OfNat LT4 3 where
  ofNat := LT4.three
-- ANCHOR_END: LT4ofNat


/-- info:
LT4.three
-/
#check_msgs in
-- ANCHOR: LT4three
#eval (3 : LT4)
-- ANCHOR_END: LT4three

/-- info:
LT4.zero
-/
#check_msgs in
-- ANCHOR: LT4zero
#eval (0 : LT4)
-- ANCHOR_END: LT4zero

/--
error: failed to synthesize
  OfNat LT4 4
numerals are polymorphic in Lean, but the numeral `4` cannot be used in a context where the expected type is
  LT4
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: LT4four
#eval (4 : LT4)
-- ANCHOR_END: LT4four

-- ANCHOR: OnePos
instance : One Pos where
  one := Pos.one
-- ANCHOR_END: OnePos

/-- info: 1 -/
#check_msgs in
-- ANCHOR: onePos
#eval (1 : Pos)
-- ANCHOR_END: onePos


-- ANCHOR: OfNatPos
instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n
-- ANCHOR_END: OfNatPos


-- ANCHOR: eight
def eight : Pos := 8
-- ANCHOR_END: eight


/--
error: failed to synthesize
  OfNat Pos 0
numerals are polymorphic in Lean, but the numeral `0` cannot be used in a context where the expected type is
  Pos
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: zeroBad
def zero : Pos := 0
-- ANCHOR_END: zeroBad

namespace AltPos


-- ANCHOR: AltPos
structure Pos where
  succ ::
  pred : Nat
-- ANCHOR_END: AltPos

end AltPos

-- ANCHOR: printlnType
example : {α : Type} → [ToString α] → α → IO Unit := @IO.println
-- ANCHOR_END: printlnType


/-- info:
IO.println : ?m.2620 → IO Unit
-/
#check_msgs in
-- ANCHOR: printlnMetas
#check (IO.println)
-- ANCHOR_END: printlnMetas

/-- info: @IO.println : {α : Type u_1} → [ToString α] → α → IO Unit -/
#check_msgs in
-- ANCHOR: printlnNoMetas
#check @IO.println
-- ANCHOR_END: printlnNoMetas

discarding
-- ANCHOR: ListSum
def List.sumOfContents [Add α] [OfNat α 0] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
-- ANCHOR_END: ListSum
stop discarding

-- ANCHOR: ListSumZ
def List.sumOfContents [Add α] [Zero α] : List α → α
  | [] => 0
  | x :: xs => x + xs.sumOfContents
-- ANCHOR_END: ListSumZ


-- ANCHOR: fourNats
def fourNats : List Nat := [1, 2, 3, 4]
-- ANCHOR_END: fourNats


-- ANCHOR: fourPos
def fourPos : List Pos := [1, 2, 3, 4]
-- ANCHOR_END: fourPos


/-- info:
10
-/
#check_msgs in
-- ANCHOR: fourNatsSum
#eval fourNats.sumOfContents
-- ANCHOR_END: fourNatsSum


/--
error: failed to synthesize
  Zero Pos

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: fourPosSum
#eval fourPos.sumOfContents
-- ANCHOR_END: fourPosSum

namespace PointStuff


-- ANCHOR: PPoint
structure PPoint (α : Type) where
  x : α
  y : α
-- ANCHOR_END: PPoint


-- ANCHOR: AddPPoint
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y }
-- ANCHOR_END: AddPPoint

-- ANCHOR: AddPPointNat
example := Add (PPoint Nat)
example := Add Nat
-- ANCHOR_END: AddPPointNat

-- ANCHOR: MulPPoint
instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p z := {x := p.x * z, y := p.y * z}
-- ANCHOR_END: MulPPoint

/-- info:
{ x := 5.000000, y := 7.400000 }
-/
#check_msgs in
-- ANCHOR: HMulPPoint
#eval {x := 2.5, y := 3.7 : PPoint Float} * 2.0
-- ANCHOR_END: HMulPPoint

end PointStuff



-- ANCHOR: ofNatType
example : {α : Type} → (n : Nat) → [OfNat α n] → α := @OfNat.ofNat
-- ANCHOR_END: ofNatType

-- ANCHOR: addType
example : {α : Type} → [Add α] → α → α → α := @Add.add
-- ANCHOR_END: addType


namespace Foo

section
variable {α β : Type} (x : α) (y : β)
variable [HSub α β γ] [HDiv α β γ] [HMod α β γ] [HPow α β γ]


-- ANCHOR: minusDesugar
example : x - y = HSub.hSub x y := rfl
-- ANCHOR_END: minusDesugar
end

section
variable {α β : Type} (x : α) (y : β)
variable [HSub α β γ] [HDiv α β γ] [HMod α β γ] [HPow α β γ]

-- ANCHOR: divDesugar
example : x / y = HDiv.hDiv x y := rfl
-- ANCHOR_END: divDesugar
end

section
variable {α β : Type} (x : α) (y : β)
variable [HSub α β γ] [HDiv α β γ] [HMod α β γ] [HPow α β γ]

-- ANCHOR: modDesugar
example : x % y = HMod.hMod x y := rfl
-- ANCHOR_END: modDesugar
end

section
variable {α β : Type} (x : α) (y : β)
variable [HSub α β γ] [HDiv α β γ] [HMod α β γ] [HPow α β γ]

-- ANCHOR: powDesugar
example : x ^ y = HPow.hPow x y := rfl
-- ANCHOR_END: powDesugar
end
section
variable {α β : Type} (x : α) (y : β)
variable [HSub α β γ] [HDiv α β γ] [HMod α β γ] [HPow α β γ]
variable (y : α) [LT α] [LE α]

-- ANCHOR: ltDesugar
example : (x < y) = LT.lt x y := rfl
-- ANCHOR_END: ltDesugar
end
section
variable {α β : Type} (x : α) (y : β)
variable [HSub α β γ] [HDiv α β γ] [HMod α β γ] [HPow α β γ]
variable (y : α) [LT α] [LE α]
-- ANCHOR: leDesugar
example : (x ≤ y) = LE.le x y := rfl
-- ANCHOR_END: leDesugar
end

section
variable {α β : Type} (x : α) (y : β)
variable [HSub α β γ] [HDiv α β γ] [HMod α β γ] [HPow α β γ]
variable (y : α) [LT α] [LE α]

-- ANCHOR: gtDesugar
example : (x > y) = LT.lt y x := by rfl
-- ANCHOR_END: gtDesugar

end

section
variable {α β : Type} (x : α) (y : β)
variable [HSub α β γ] [HDiv α β γ] [HMod α β γ] [HPow α β γ]
variable (y : α) [LT α] [LE α]

-- ANCHOR: geDesugar
example : (x ≥ y) = LE.le y x := by rfl
-- ANCHOR_END: geDesugar
end
section
variable {α β : Type} (x : α) (y : β)
variable [HSub α β γ] [HDiv α β γ] [HMod α β γ] [HPow α β γ]
variable (y : α) [LT α] [LE α]

--ANCHOR: ordSugarClasses
example := [LE, LT]
--ANCHOR_END: ordSugarClasses
end
end Foo

namespace OverloadedInt

variable {α : Type} (x : α) [Neg α]


-- ANCHOR: negDesugar
example : (- x) = Neg.neg x := rfl
-- ANCHOR_END: negDesugar


end OverloadedInt

namespace OverloadedBits



-- ANCHOR: UInt8
example : Type := UInt8
-- ANCHOR_END: UInt8

-- ANCHOR: UInt16
example : Type := UInt16
-- ANCHOR_END: UInt16

-- ANCHOR: UInt32
example : Type := UInt32
-- ANCHOR_END: UInt32

-- ANCHOR: UInt64
example : Type := UInt64
-- ANCHOR_END: UInt64

-- ANCHOR: USize
example : Type := USize
-- ANCHOR_END: USize


section
variable {x: α} {y : β} [HAnd α β γ]
-- ANCHOR: bAndDesugar
example : x &&& y = HAnd.hAnd x y := rfl
-- ANCHOR_END: bAndDesugar
end

section
variable {x: α} {y : β} [HOr α β γ]
-- ANCHOR: bOrDesugar
example : x ||| y = HOr.hOr x y := rfl
-- ANCHOR_END: bOrDesugar
end

section
variable {x: α} {y : β} [HXor α β γ]
-- ANCHOR: bXorDesugar
example : x ^^^ y = HXor.hXor x y := rfl
-- ANCHOR_END: bXorDesugar
end

section
variable {x: α} [Complement α]

-- ANCHOR: complementDesugar
example : ~~~ x = Complement.complement x := rfl
-- ANCHOR_END: complementDesugar
end

section
variable {x: α} {y : β} [HShiftRight α β γ]

-- ANCHOR: shrDesugar
example : x >>> y = HShiftRight.hShiftRight x y := rfl
-- ANCHOR_END: shrDesugar
end

section
variable {x: α} {y : β} [HShiftLeft α β γ]

-- ANCHOR: shlDesugar
example : x <<< y = HShiftLeft.hShiftLeft x y := rfl
-- ANCHOR_END: shlDesugar

end

section
variable {x y : α} [BEq α]

-- ANCHOR: beqDesugar
example : (x == y) = BEq.beq x y := rfl
-- ANCHOR_END: beqDesugar

end

end OverloadedBits


-- ANCHOR: addNatPos
def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)
-- ANCHOR_END: addNatPos



-- ANCHOR: haddInsts
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
-- ANCHOR_END: haddInsts


/-- info:
8
-/
#check_msgs in
-- ANCHOR: posNatEx
#eval (3 : Pos) + (5 : Nat)
-- ANCHOR_END: posNatEx

/-- info:
8
-/
#check_msgs in
-- ANCHOR: natPosEx
#eval (3 : Nat) + (5 : Pos)
-- ANCHOR_END: natPosEx

namespace ProblematicHPlus

-- ANCHOR: HPlus
class HPlus (α : Type) (β : Type) (γ : Type) where
  hPlus : α → β → γ
-- ANCHOR_END: HPlus


-- ANCHOR: HPlusInstances
instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat
-- ANCHOR_END: HPlusInstances

/--
error: typeclass instance problem is stuck, it is often due to metavariables
  ToString ?m.14563
-/
#check_msgs in
-- ANCHOR: hPlusOops
#eval toString (HPlus.hPlus (3 : Pos) (5 : Nat))
-- ANCHOR_END: hPlusOops


/-- info:
8
-/
#check_msgs in
-- ANCHOR: hPlusLotsaTypes
#eval (HPlus.hPlus (3 : Pos) (5 : Nat) : Pos)
-- ANCHOR_END: hPlusLotsaTypes

end ProblematicHPlus

inductive Even where
  | zero
  | plusTwo : Even → Even

instance : OfNat Even 0 where
  ofNat := .zero

instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := .plusTwo (OfNat.ofNat n)

#eval (6 : Even)

namespace BetterHPlus

-- ANCHOR: HPlusOut
class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ
-- ANCHOR_END: HPlusOut

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

/-- info:
8
-/
#check_msgs in
-- ANCHOR: hPlusWorks
#eval HPlus.hPlus (3 : Pos) (5 : Nat)
-- ANCHOR_END: hPlusWorks


-- ANCHOR: notDefaultAdd
instance [Add α] : HPlus α α α where
  hPlus := Add.add
-- ANCHOR_END: notDefaultAdd

/-- info:
8
-/
#check_msgs in
-- ANCHOR: hPlusNatNat
#eval HPlus.hPlus (3 : Nat) (5 : Nat)
-- ANCHOR_END: hPlusNatNat


/-- info:
HPlus.hPlus 5 3 : Nat
-/
#check_msgs in
-- ANCHOR: plusFiveThree
#check HPlus.hPlus (5 : Nat) (3 : Nat)
-- ANCHOR_END: plusFiveThree

/-- info:
HPlus.hPlus 5 : ?m.6076 → ?m.6078
-/
#check_msgs in
-- ANCHOR: plusFiveMeta
#check HPlus.hPlus (5 : Nat)
-- ANCHOR_END: plusFiveMeta


-- ANCHOR: defaultAdd
@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add
-- ANCHOR_END: defaultAdd


/-- info:
HPlus.hPlus 5 : Nat → Nat
-/
#check_msgs in
-- ANCHOR: plusFive
#check HPlus.hPlus (5 : Nat)
-- ANCHOR_END: plusFive

end BetterHPlus

similar datatypes ProblematicHPlus.HPlus BetterHPlus.HPlus

-- ANCHOR: fiveType
example : Nat := 5
-- ANCHOR_END: fiveType


-- ANCHOR: northernTrees
def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]
-- ANCHOR_END: northernTrees

-- ANCHOR: northernTreesSize
example : northernTrees.size = 4 := rfl
-- ANCHOR_END: northernTreesSize

-- ANCHOR: northernTreesTwo
example : northernTrees[2] = "elm" := rfl
-- ANCHOR_END: northernTreesTwo


/-- error:
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ 8 < northernTrees.size
-/
#check_msgs in
-- ANCHOR: northernTreesEight
-- TODO ensure correct quote in book
example := northernTrees[8]
-- ANCHOR_END: northernTreesEight

inductive EvenList (α : Type) : Type where
  | nil : EvenList α
  | cons : α → α → EvenList α → EvenList α


-- ANCHOR: NonEmptyList
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α
-- ANCHOR_END: NonEmptyList

def NonEmptyList.toList (xs : NonEmptyList α) := xs.head :: xs.tail

-- ANCHOR: coeNope
example {α : _} := Coe (List α) (NonEmptyList α)
-- ANCHOR_END: coeNope

-- ANCHOR: idahoSpiders
def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}
-- ANCHOR_END: idahoSpiders

-- ANCHOR: firstSpider
example : -- TODO there was a name overlap - check it
  idahoSpiders.head = "Banded Garden Spider" := rfl
-- ANCHOR_END: firstSpider

-- ANCHOR: moreSpiders
example : idahoSpiders.tail.length = 4 := rfl
-- ANCHOR_END: moreSpiders

-- ANCHOR: NEListGetHuh
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | {head := _, tail := []}, _ + 1 => none
  | {head := _, tail := h :: t}, n + 1 => get? {head := h, tail := t} n
-- ANCHOR_END: NEListGetHuh

namespace UseList
-- ANCHOR: NEListGetHuhList
def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail[n]?
-- ANCHOR_END: NEListGetHuhList
end UseList

-- ANCHOR: inBoundsNEList
abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length
-- ANCHOR_END: inBoundsNEList


-- ANCHOR: NEListGet
def NonEmptyList.get (xs : NonEmptyList α)
    (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]
-- ANCHOR_END: NEListGet



-- ANCHOR: spiderBoundsChecks
theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by decide

theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by decide
-- ANCHOR_END: spiderBoundsChecks

namespace Foo
-- ANCHOR: spiderBoundsChecks'
theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by decide

theorem notSixSpiders : ¬(idahoSpiders.inBounds 5) := by decide
-- ANCHOR_END: spiderBoundsChecks'
end Foo

namespace Demo
-- ANCHOR: GetElem
class GetElem
    (coll : Type)
    (idx : Type)
    (item : outParam Type)
    (inBounds : outParam (coll → idx → Prop)) where
  getElem : (c : coll) → (i : idx) → inBounds c i → item
-- ANCHOR_END: GetElem
end Demo

similar datatypes GetElem Demo.GetElem

-- ANCHOR: GetElemNEList
instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get
-- ANCHOR_END: GetElemNEList


-- ANCHOR: firstSpiderZero
example : idahoSpiders[0] = "Banded Garden Spider" := rfl
-- ANCHOR_END: firstSpiderZero


/-- error:
failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ idahoSpiders.inBounds 9
-/
#check_msgs in
-- ANCHOR: tenthSpider
-- TODO ensure correct quote
example := idahoSpiders[9]
-- ANCHOR_END: tenthSpider




-- ANCHOR: ListPosElem
instance : GetElem (List α) Pos α
    (fun list n => list.length > n.toNat) where
  getElem (xs : List α) (i : Pos) ok := xs[i.toNat]
-- ANCHOR_END: ListPosElem

namespace PointStuff


-- ANCHOR: PPointBoolGetElem
instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p : PPoint α) (i : Bool) _ :=
    if not i then p.x else p.y
-- ANCHOR_END: PPointBoolGetElem


instance : GetElem (PPoint α) Nat α (fun _ n => n < 2) where
  getElem (p : PPoint α) (i : Nat) _ :=
    match i with
    | 0 => p.x
    | 1 => p.y
end PointStuff

-- ANCHOR: boolEqTrue
example : ("Octopus" ==  "Cuttlefish") = false := rfl
-- ANCHOR_END: boolEqTrue

-- ANCHOR: boolEqFalse
example : ("Octopodes" ==  "Octo".append "podes") = true := rfl
-- ANCHOR_END: boolEqFalse

/--
error: failed to synthesize
  BEq (Nat → Nat)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: functionEq
-- TODO quote check
example := (fun (x : Nat) => 1 + x) == (Nat.succ ·)
-- ANCHOR_END: functionEq

-- ANCHOR: functionEqProp
example : Prop := (fun (x : Nat) => 1 + x) = (Nat.succ ·)
-- ANCHOR_END: functionEqProp

-- ANCHOR: LTPos
instance : LT Pos where
  lt x y := LT.lt x.toNat y.toNat
-- ANCHOR_END: LTPos

-- ANCHOR: LEPos
instance : LE Pos where
  le x y := LE.le x.toNat y.toNat
-- ANCHOR_END: LEPos

-- ANCHOR: DecLTLEPos
instance {x : Pos} {y : Pos} : Decidable (x < y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))

instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat ≤ y.toNat))
-- ANCHOR_END: DecLTLEPos

/--
error: Type mismatch
  inferInstanceAs (Decidable (x.toNat < y.toNat))
has type
  Decidable (x.toNat < y.toNat)
but is expected to have type
  Decidable (x ≤ y)
-/
#check_msgs in
-- ANCHOR: LTLEMismatch
instance {x : Pos} {y : Pos} : Decidable (x ≤ y) :=
  inferInstanceAs (Decidable (x.toNat < y.toNat))
-- ANCHOR_END: LTLEMismatch

#eval (5 : Pos) < (3 : Pos)

example : (fun (x : Nat) => 1 + x) = (Nat.succ ·) := by ext; simp +arith

-- Example for exercise
inductive Method where
  | GET
  | POST
  | PUT
  | DELETE

structure Response where

class HTTP (m : Method) where
  doTheWork : (uri : String) → IO Response

/-- info:
2 < 4 : Prop
-/
#check_msgs in
-- ANCHOR: twoLessFour
#check 2 < 4
-- ANCHOR_END: twoLessFour

/--
error: failed to synthesize
  Decidable ((fun x => 1 + x) = fun x => x.succ)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: funEqDec
-- TODO quote check
example := if (fun (x : Nat) => 1 + x) = (Nat.succ ·) then "yes" else "no"
-- ANCHOR_END: funEqDec

--- ANCHOR: ifProp
example : (
if 2 < 4 then 1 else 2
) = (
1
) := rfl
--- ANCHOR_END: ifProp

namespace Cmp
-- ANCHOR: Ordering
inductive Ordering where
  | lt
  | eq
  | gt
-- ANCHOR_END: Ordering
end Cmp

similar datatypes Ordering Cmp.Ordering


-- ANCHOR: OrdPos
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ k => comp n k

instance : Ord Pos where
  compare := Pos.comp
-- ANCHOR_END: OrdPos

namespace H

-- ANCHOR: Hashable
class Hashable (α : Type) where
  hash : α → UInt64
-- ANCHOR_END: Hashable
end H

-- ANCHOR: HashableSpec
section
variable {α : Type} (x y : α) [BEq α] [Hashable α]
example := x == y
example := hash x == hash y
example := x ≠ y
end
-- ANCHOR_END: HashableSpec

similar datatypes Hashable H.Hashable

-- ANCHOR: mixHash
example : UInt64 → UInt64 → UInt64 := mixHash
-- ANCHOR_END: mixHash


-- ANCHOR: HashablePos
def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)

instance : Hashable Pos where
  hash := hashPos
-- ANCHOR_END: HashablePos


-- ANCHOR: TreeHash
inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α

def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf =>
    true
  | BinTree.branch l x r, BinTree.branch l2 x2 r2 =>
    x == x2 && eqBinTree l l2 && eqBinTree r r2
  | _, _ =>
    false

instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf =>
    0
  | BinTree.branch left x right =>
    mixHash 1
      (mixHash (hashBinTree left)
        (mixHash (hash x)
          (hashBinTree right)))

instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree
-- ANCHOR_END: TreeHash

-- ANCHOR: HashableNonEmptyList
instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)
-- ANCHOR_END: HashableNonEmptyList



-- ANCHOR: BEqHashableDerive
deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable for NonEmptyList
-- ANCHOR_END: BEqHashableDerive


/-- error: No deriving handlers have been implemented for class `ToString` -/
#check_msgs in
-- ANCHOR: derivingNotFound
deriving instance ToString for NonEmptyList
-- ANCHOR_END: derivingNotFound

namespace A
-- ANCHOR: HAppend
class HAppend (α : Type) (β : Type) (γ : outParam Type) where
  hAppend : α → β → γ
-- ANCHOR_END: HAppend
end A

similar datatypes HAppend A.HAppend

namespace AppendOverloads
section
variable {α β γ : Type} (xs : α) (ys : β) [HAppend α β γ]
-- ANCHOR: desugarHAppend
example : xs ++ ys = HAppend.hAppend xs ys := rfl
-- ANCHOR_END: desugarHAppend
end
end AppendOverloads


-- ANCHOR: AppendNEList
instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail }
-- ANCHOR_END: AppendNEList

/-- info:
{ head := "Banded Garden Spider",
  tail := ["Long-legged Sac Spider",
           "Wolf Spider",
           "Hobo Spider",
           "Cat-faced Spider",
           "Banded Garden Spider",
           "Long-legged Sac Spider",
           "Wolf Spider",
           "Hobo Spider",
           "Cat-faced Spider"] }
-/
#check_msgs in
-- ANCHOR: appendSpiders
#eval idahoSpiders ++ idahoSpiders
  -- ANCHOR_END: appendSpiders

-- ANCHOR: AppendNEListList
instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys }
-- ANCHOR_END: AppendNEListList

/-- info:
{ head := "Banded Garden Spider",
  tail := ["Long-legged Sac Spider", "Wolf Spider", "Hobo Spider", "Cat-faced Spider", "Trapdoor Spider"] }
-/
#check_msgs in
-- ANCHOR: appendSpidersList
#eval idahoSpiders ++ ["Trapdoor Spider"]
  -- ANCHOR_END: appendSpidersList


section
-- ANCHOR: optionFMeta
variable {α β : Type} (f : α → β)
example := Option
example : Functor.map f none = none := rfl
example : Functor.map f (some x) = some (f x) := rfl
-- ANCHOR_END: optionFMeta
end

section
-- ANCHOR: FunctorLaws
variable {α β γ : Type} (g : α → β) (f : β → γ) {F : Type → Type} [Functor F] (x : F α)
example := id <$> x
open Functor
example := map (fun y => f (g y)) x
example := map f (map g x)
-- ANCHOR_END: FunctorLaws
end

-- ANCHOR: mapList
example : Functor.map (· + 5) [1, 2, 3] = [6, 7, 8] := rfl
-- ANCHOR_END: mapList

-- ANCHOR: mapOption
example : Functor.map toString (some (List.cons 5 List.nil)) = some "[5]" := rfl
-- ANCHOR_END: mapOption

-- ANCHOR: mapListList
example : Functor.map List.reverse [[1, 2, 3], [4, 5, 6]] = [[3, 2, 1], [6, 5, 4]] := rfl
-- ANCHOR_END: mapListList

-- ANCHOR: mapInfixList
example : (· + 5) <$> [1, 2, 3] = [6, 7, 8] := rfl
-- ANCHOR_END: mapInfixList

-- ANCHOR: mapInfixOption
example : toString <$> (some (List.cons 5 List.nil)) = some "[5]" := rfl
-- ANCHOR_END: mapInfixOption

-- ANCHOR: mapInfixListList
example : List.reverse <$> [[1, 2, 3], [4, 5, 6]] = [[3, 2, 1], [6, 5, 4]] := rfl
-- ANCHOR_END: mapInfixListList


-- ANCHOR: FunctorNonEmptyList
instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }
-- ANCHOR_END: FunctorNonEmptyList

section
variable {α : Type}
-- ANCHOR: FunctorNonEmptyListA
example := NonEmptyList α
example := NonEmptyList Nat
-- ANCHOR_END: FunctorNonEmptyListA
end

namespace PointStuff

-- ANCHOR: FunctorPPointBad
instance : Functor PPoint where
  map f p := let x := p.x; have := f x; { x := f p.x, y := f p.x }

-- ANCHOR_END: FunctorPPointBad

-- ANCHOR: FunctorPPoint
instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }
-- ANCHOR_END: FunctorPPoint



-- ANCHOR: NEPP
example := NonEmptyList (PPoint Nat)
-- ANCHOR_END: NEPP

end PointStuff




-- ANCHOR: concat
def concat [Append α] (xs : NonEmptyList α) : α :=
  let rec catList (start : α) : List α → α
    | [] => start
    | (z :: zs) => catList (start ++ z) zs
  catList xs.head xs.tail
-- ANCHOR_END: concat

-- Just a quick test, not used in the book
-- ANCHOR: concatText
example : concat idahoSpiders = "Banded Garden SpiderLong-legged Sac SpiderWolf SpiderHobo SpiderCat-faced Spider" := rfl
-- ANCHOR_END: concatText

namespace FakeFunctor
-- ANCHOR: FunctorDef
class Functor (f : Type → Type) where
  map : {α β : Type} → (α → β) → f α → f β

  mapConst {α β : Type} (x : α) (coll : f β) : f α :=
    map (fun _ => x) coll
-- ANCHOR_END: FunctorDef
end FakeFunctor
similar datatypes FakeFunctor.Functor Functor


namespace Whatevs
axiom α : Type
axiom β : Type
axiom γ : Type
axiom f : β → γ
axiom g : α → β

-- ANCHOR: compDef
example : f ∘ g = fun y => f (g y) := rfl
-- ANCHOR_END: compDef

end Whatevs
-- Coercions


-- ANCHOR: drop
example : {α : Type} → Nat → List α → List α := @List.drop
-- ANCHOR_END: drop

/--
error: Application type mismatch: The argument
  2
has type
  Pos
but is expected to have type
  Nat
in the application
  List.drop 2
-/
#check_msgs in
-- ANCHOR: dropPos
-- TODO quote check
example := [1, 2, 3, 4].drop (2 : Pos)
-- ANCHOR_END: dropPos

namespace FakeCoe
-- ANCHOR: Coe
class Coe (α : Type) (β : Type) where
  coe : α → β
-- ANCHOR_END: Coe

-- ANCHOR: CoeTail
class CoeTail (α : Type) (β : Type) where
  coe : α → β
-- ANCHOR_END: CoeTail

-- ANCHOR: CoeHead
class CoeHead (α : Type) (β : Type) where
  coe : α → β
-- ANCHOR_END: CoeHead

end FakeCoe

similar datatypes Coe FakeCoe.Coe
similar datatypes CoeTail FakeCoe.CoeTail
similar datatypes CoeHead FakeCoe.CoeHead



-- ANCHOR: CoeOption
instance : Coe α (Option α) where
  coe x := some x
-- ANCHOR_END: CoeOption

namespace L


-- ANCHOR: lastHuh
def List.last? : List α → Option α
  | [] => none
  | [x] => x
  | _ :: x :: xs => last? (x :: xs)
-- ANCHOR_END: lastHuh

end L


-- ANCHOR: perhapsPerhapsPerhaps
def perhapsPerhapsPerhaps : Option (Option (Option String)) :=
  "Please don't tell me"
-- ANCHOR_END: perhapsPerhapsPerhaps


discarding
/--
error: failed to synthesize
  OfNat (Option (Option (Option Nat))) 392
numerals are polymorphic in Lean, but the numeral `392` cannot be used in a context where the expected type is
  Option (Option (Option Nat))
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: ofNatBeforeCoe
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  392
-- ANCHOR_END: ofNatBeforeCoe
stop discarding

-- ANCHOR: perhapsPerhapsPerhapsNat
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  (392 : Nat)
-- ANCHOR_END: perhapsPerhapsPerhapsNat

namespace Up
-- ANCHOR: perhapsPerhapsPerhapsNatUp
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) :=
  ↑(392 : Nat)
-- ANCHOR_END: perhapsPerhapsPerhapsNatUp
end Up

-- ANCHOR: CoeNEList
instance : Coe (NonEmptyList α) (List α) where
  coe
    | { head := x, tail := xs } => x :: xs
-- ANCHOR_END: CoeNEList


namespace Foo
-- ANCHOR: CoeDep
class CoeDep (α : Type) (x : α) (β : Type) where
  coe : β
-- ANCHOR_END: CoeDep
end Foo
similar datatypes CoeDep Foo.CoeDep

-- ANCHOR: CoeDepListNEList
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }
-- ANCHOR_END: CoeDepListNEList

/--
error: Type mismatch
  []
has type
  List ?m.2
but is expected to have type
  NonEmptyList Nat
-/
#check_msgs in
#eval ([] : NonEmptyList Nat)

/-- info: { head := 1, tail := [2, 3] } -/
#guard_msgs in
#eval ([1, 2, 3] : NonEmptyList Nat)

-- ANCHOR: JSON
inductive JSON where
  | true : JSON
  | false : JSON
  | null : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array : List JSON → JSON
-- ANCHOR_END: JSON



/-- info:
"5.000000"
-/
#check_msgs in
-- ANCHOR: fiveZeros
#eval (5 : Float).toString
-- ANCHOR_END: fiveZeros


-- ANCHOR: Stringseparate
def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | [] => ""
  | x :: xs => String.join (x :: xs.map (sep ++ ·))
-- ANCHOR_END: Stringseparate



/-- info:
"1, 2"
-/
#check_msgs in
-- ANCHOR: sep2ex
#eval ", ".separate ["1", "2"]
-- ANCHOR_END: sep2ex


/-- info:
"1"
-/
#check_msgs in
-- ANCHOR: sep1ex
#eval ", ".separate ["1"]
-- ANCHOR_END: sep1ex


/-- info:
""
-/
#check_msgs in
-- ANCHOR: sep0ex
#eval ", ".separate []
-- ANCHOR_END: sep0ex

-- ANCHOR: dropDecimals
def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropRightWhile (· == '0')
    noTrailingZeros.dropRightWhile (· == '.')
  else numString
-- ANCHOR_END: dropDecimals


/-- info:
"5"
-/
#check_msgs in
-- ANCHOR: dropDecimalExample
#eval dropDecimals (5 : Float).toString
-- ANCHOR_END: dropDecimalExample

/-- info:
"5.2"
-/
#check_msgs in
-- ANCHOR: dropDecimalExample2
#eval dropDecimals (5.2 : Float).toString
-- ANCHOR_END: dropDecimalExample2



/-- info:
"\\\"Hello!\\\""
-/
#check_msgs in
-- ANCHOR: escapeQuotes
#eval Lean.Json.escape "\"Hello!\""
-- ANCHOR_END: escapeQuotes


-- ANCHOR: JSONasString
partial def JSON.asString (val : JSON) : String :=
  match val with
  | true => "true"
  | false => "false"
  | null => "null"
  | string s => "\"" ++ Lean.Json.escape s ++ "\""
  | number n => dropDecimals n.toString
  | object members =>
    let memberToString mem :=
      "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
    "{" ++ ", ".separate (members.map memberToString) ++ "}"
  | array elements =>
    "[" ++ ", ".separate (elements.map asString) ++ "]"
-- ANCHOR_END: JSONasString

-- ANCHOR: Monoid
structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }
-- ANCHOR_END: Monoid

namespace MMM
-- ANCHOR: firstFoldMap
def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs
-- ANCHOR_END: firstFoldMap
end MMM


-- ANCHOR: CoeMonoid
instance : CoeSort Monoid Type where
  coe m := m.Carrier
-- ANCHOR_END: CoeMonoid


-- ANCHOR: foldMap
def foldMap (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs
-- ANCHOR_END: foldMap

-- ANCHOR: CoeBoolProp
instance : CoeSort Bool Prop where
  coe b := b = true
-- ANCHOR_END: CoeBoolProp


namespace U

-- ANCHOR: CoeFun
class CoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
  coe : (x : α) → makeFunctionType x
-- ANCHOR_END: CoeFun

end U
similar datatypes CoeFun U.CoeFun


-- ANCHOR: Adder
structure Adder where
  howMuch : Nat
-- ANCHOR_END: Adder

-- ANCHOR: add5
def add5 : Adder := ⟨5⟩
-- ANCHOR_END: add5

/--
error: Function expected at
  add5
but this term has type
  Adder

Note: Expected a function because this term is being applied to the argument
  3
-/
#check_msgs in
-- ANCHOR: add5notfun
#eval add5 3
-- ANCHOR_END: add5notfun


-- ANCHOR: CoeFunAdder
instance : CoeFun Adder (fun _ => Nat → Nat) where
  coe a := (· + a.howMuch)
-- ANCHOR_END: CoeFunAdder


/-- info:
8
-/
#check_msgs in
-- ANCHOR: add53
#eval add5 3
-- ANCHOR_END: add53

namespace Ser

-- ANCHOR: Serializer
structure Serializer where
  Contents : Type
  serialize : Contents → JSON
-- ANCHOR_END: Serializer


-- ANCHOR: StrSer
def Str : Serializer :=
  { Contents := String,
    serialize := JSON.string
  }
-- ANCHOR_END: StrSer


-- ANCHOR: CoeFunSer
instance : CoeFun Serializer (fun s => s.Contents → JSON) where
  coe s := s.serialize
-- ANCHOR_END: CoeFunSer


-- ANCHOR: buildResponse
def buildResponse (title : String) (R : Serializer)
    (record : R.Contents) : JSON :=
  JSON.object [
    ("title", JSON.string title),
    ("status", JSON.number 200),
    ("record", R record)
  ]
-- ANCHOR_END: buildResponse



/-- info:
JSON.object
  [("title", JSON.string "Functional Programming in Lean"),
   ("status", JSON.number 200.000000),
   ("record", JSON.string "Programming is fun!")]
-/
#check_msgs in
-- ANCHOR: buildResponseOut
#eval buildResponse "Functional Programming in Lean" Str "Programming is fun!"
-- ANCHOR_END: buildResponseOut



/-- info:
"{\"title\": \"Functional Programming in Lean\", \"status\": 200, \"record\": \"Programming is fun!\"}"
-/
#check_msgs in
-- ANCHOR: buildResponseStr
#eval (buildResponse "Functional Programming in Lean" Str "Programming is fun!").asString
-- ANCHOR_END: buildResponseStr
end Ser

namespace A
/--
error: Application type mismatch: The argument
  idahoSpiders
has type
  NonEmptyList String
but is expected to have type
  List ?m.3
in the application
  List.getLast? idahoSpiders
-/
#check_msgs in
-- ANCHOR: lastSpiderB
def lastSpider :=
  List.getLast? idahoSpiders
-- ANCHOR_END: lastSpiderB

discarding
/--
error: Invalid field `getLast?`: The environment does not contain `NonEmptyList.getLast?`
  idahoSpiders
has type
  NonEmptyList String
-/
#check_msgs in
-- ANCHOR: lastSpiderC
def lastSpider : Option String :=
  idahoSpiders.getLast?
-- ANCHOR_END: lastSpiderC
stop discarding

-- ANCHOR: lastSpiderA
def lastSpider : Option String :=
  List.getLast? idahoSpiders
-- ANCHOR_END: lastSpiderA
end A

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := ⟨x, xs⟩


-- ANCHOR: CoercionCycle
inductive A where
  | a

inductive B where
  | b

instance : Coe A B where
  coe _ := B.b

instance : Coe B A where
  coe _ := A.a

instance : Coe Unit A where
  coe _ := A.a

def coercedToB : B := ()
-- ANCHOR_END: CoercionCycle

-- ANCHOR: ReprB
deriving instance Repr for B
-- ANCHOR_END: ReprB
-- ANCHOR: ReprBTm
example := Repr B
-- ANCHOR_END: ReprBTm


/-- info:
B.b
-/
#check_msgs in
-- ANCHOR: coercedToBEval
#eval coercedToB
-- ANCHOR_END: coercedToBEval

-- ANCHOR: CoePosNat
instance : Coe Pos Nat where
  coe x := x.toNat
-- ANCHOR_END: CoePosNat

-- ANCHOR: posInt
def oneInt : Int := Pos.one
-- ANCHOR_END: posInt

/-- info:
[3, 4]
-/
#check_msgs in
-- ANCHOR: dropPosCoe
#eval [1, 2, 3, 4].drop (2 : Pos)
-- ANCHOR_END: dropPosCoe

/-- info:
List.drop (Pos.toNat 2) [1, 2, 3, 4] : List Nat
-/
#check_msgs in
-- ANCHOR: checkDropPosCoe
#check [1, 2, 3, 4].drop (2 : Pos)
-- ANCHOR_END: checkDropPosCoe


-- ANCHOR: trees
structure Tree : Type where
  latinName : String
  commonNames : List String

def oak : Tree :=
  ⟨"Quercus robur", ["common oak", "European oak"]⟩

def birch : Tree :=
  { latinName := "Betula pendula",
    commonNames := ["silver birch", "warty birch"]
  }

def sloe : Tree where
  latinName := "Prunus spinosa"
  commonNames := ["sloe", "blackthorn"]
-- ANCHOR_END: trees



-- ANCHOR: Display
class Display (α : Type) where
  displayName : α → String

instance : Display Tree :=
  ⟨Tree.latinName⟩

instance : Display Tree :=
  { displayName := Tree.latinName }

instance : Display Tree where
  displayName t := t.latinName
-- ANCHOR_END: Display

-- ANCHOR: birdExample
example : NonEmptyList String :=
  { head := "Sparrow",
    tail := ["Duck", "Swan", "Magpie", "Eurasian coot", "Crow"]
  }
-- ANCHOR_END: birdExample

-- ANCHOR: commAdd
example (n : Nat) (k : Nat) : Bool :=
  n + k == k + n
-- ANCHOR_END: commAdd

-- ANCHOR: nats
example := [0,1,2,3,4,5,6,7,8,9,10]
-- ANCHOR_END: nats

-- ANCHOR: moreOps
section
example := [AndOp, OrOp, Inhabited]
example := Nat → List Int
example {α} := HAppend (List α) (NonEmptyList α) (NonEmptyList α)
end
-- ANCHOR_END: moreOps
