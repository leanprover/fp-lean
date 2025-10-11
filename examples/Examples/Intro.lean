import ExampleSupport
import SubVerso.Examples

set_option linter.unusedVariables false

-- ANCHOR: three
example : (
1 + 2
) = (
3
) := rfl
-- ANCHOR_END: three

/-- info: 3 -/
#check_msgs in
-- ANCHOR: threeEval
#eval 1 + 2
-- ANCHOR_END: threeEval

/-- info: 11 -/
#check_msgs in
-- ANCHOR: orderOfOperations
#eval 1 + 2 * 5
-- ANCHOR_END: orderOfOperations


/-- info: 15 -/
#check_msgs in
-- ANCHOR: orderOfOperationsWrong
#eval (1 + 2) * 5
-- ANCHOR_END: orderOfOperationsWrong

/-- info: "Hello, Lean!" -/
#check_msgs in
--- ANCHOR: stringAppendHello
#eval String.append "Hello, " "Lean!"
--- ANCHOR_END: stringAppendHello

/-- info: "great oak tree" -/
#check_msgs in
--- ANCHOR: stringAppendNested
#eval String.append "great " (String.append "oak " "tree")
--- ANCHOR_END: stringAppendNested


evaluation steps  {{{ stringAppend }}}
-- ANCHOR: stringAppend
String.append "it is " (if 1 > 2 then "yes" else "no")
===>
String.append "it is " (if false then "yes" else "no")
===>
String.append "it is " "no"
===>
"it is no"
-- ANCHOR_END: stringAppend
end evaluation steps

/--
error: could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  String → String
-/
#check_msgs in
-- ANCHOR: stringAppendReprFunction
#eval String.append "it is "
-- ANCHOR_END: stringAppendReprFunction


/-- info:
false
-/
#check_msgs in
-- ANCHOR: stringAppendCond
#eval 1 > 2
-- ANCHOR_END: stringAppendCond

/-- info:
3
-/
#check_msgs in
-- ANCHOR: onePlusTwoEval
#eval (1 + 2 : Nat)
-- ANCHOR_END: onePlusTwoEval


-- ANCHOR: onePlusTwoType
example : (
(1 + 2 : Nat)
) = (
3
) := rfl
-- ANCHOR_END: onePlusTwoType

-- ANCHOR: oneMinusTwo
example : (
1 - 2
) = (
0
) := rfl
-- ANCHOR_END: oneMinusTwo

/-- info:
0
-/
#check_msgs in
-- ANCHOR: oneMinusTwoEval
#eval (1 - 2 : Nat)
-- ANCHOR_END: oneMinusTwoEval


-- ANCHOR: oneMinusTwoInt
example : (
(1 - 2 : Int)
) = (
-1
) := rfl
-- ANCHOR_END: oneMinusTwoInt

/-- info:
-1
-/
#check_msgs in
-- ANCHOR: oneMinusTwoIntEval
#eval (1 - 2 : Int)
-- ANCHOR_END: oneMinusTwoIntEval


/-- info:
1 - 2 : Int
-/
#check_msgs in
-- ANCHOR: oneMinusTwoIntType
#check (1 - 2 : Int)
-- ANCHOR_END: oneMinusTwoIntType


/--
error: Application type mismatch: The argument
  ["hello", " "]
has type
  List String
but is expected to have type
  String
in the application
  String.append ["hello", " "]
---
info: sorry.append "world" : String
-/
#check_msgs in
-- ANCHOR: stringAppendList
#check String.append ["hello", " "] "world"
-- ANCHOR_END: stringAppendList


-- ANCHOR: hello
def hello := "Hello"
-- ANCHOR_END: hello

-- ANCHOR: helloNameVal
example : (
hello
) = (
"Hello"
) := rfl
-- ANCHOR_END: helloNameVal

-- ANCHOR: lean
def lean : String := "Lean"
-- ANCHOR_END: lean

/-- info:
"Hello Lean"
-/
#check_msgs in
-- ANCHOR: helloLean
#eval String.append hello (String.append " " lean)
-- ANCHOR_END: helloLean

-- ANCHOR: add1
def add1 (n : Nat) : Nat := n + 1
-- ANCHOR_END: add1

/-- info:
add1 (n : Nat) : Nat
-/
#check_msgs in
-- ANCHOR: add1sig
#check add1
-- ANCHOR_END: add1sig


/-- info:
add1 : Nat → Nat
-/
#check_msgs in
-- ANCHOR: add1type
#check (add1)
-- ANCHOR_END: add1type

-- ANCHOR: add1typeASCII
example : Nat -> Nat := add1
-- ANCHOR_END: add1typeASCII

/-- info:
8
-/
#check_msgs in
-- ANCHOR: add1_7
#eval add1 7
-- ANCHOR_END: add1_7

/--
error: Application type mismatch: The argument
  "seven"
has type
  String
but is expected to have type
  Nat
in the application
  add1 "seven"
---
info: add1 sorry : Nat
-/
#check_msgs in
-- ANCHOR: add1_string
#check add1 "seven"
-- ANCHOR_END: add1_string

/-- warning: declaration uses 'sorry' -/
#check_msgs in
-- ANCHOR: add1_warn
def foo := add1 sorry
-- ANCHOR_END: add1_warn


section
open SubVerso.Examples

-- ANCHOR: maximum
def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n
-- ANCHOR_END: maximum
end



-- ANCHOR: spaceBetween
def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)
-- ANCHOR_END: spaceBetween

/-- info:
maximum : Nat → Nat → Nat
-/
#check_msgs in
-- ANCHOR: maximumType
#check (maximum)
-- ANCHOR_END: maximumType

-- ANCHOR: maximumTypeASCII
example : Nat -> Nat -> Nat := maximum
-- ANCHOR_END: maximumTypeASCII


/-- info:
maximum 3 : Nat → Nat
-/
#check_msgs in
-- ANCHOR: maximum3Type
#check maximum 3
-- ANCHOR_END: maximum3Type

/-- info:
spaceBetween "Hello " : String → String
-/
#check_msgs in
-- ANCHOR: stringAppendHelloType
#check spaceBetween "Hello "
-- ANCHOR_END: stringAppendHelloType

-- ANCHOR: currying
example : (
Nat → Nat → Nat
) = (
Nat → (Nat → Nat)
) := rfl

-- ANCHOR_END: currying

evaluation steps  {{{ maximum_eval }}}
-- ANCHOR: maximum_eval
maximum (5 + 8) (2 * 7)
===>
maximum 13 14
===>
if 13 < 14 then 14 else 13
===>
14
-- ANCHOR_END: maximum_eval
end evaluation steps

---ANCHOR: joinStringsWith
def joinStringsWith (sep x y : String) : String := String.append x (String.append sep y)
example : String → String → String → String := joinStringsWith
example : String → String → String := joinStringsWith ": "
---ANCHOR_END: joinStringsWith


section
open SubVerso.Examples
%show_name joinStringsWith as joinStringsWith.name
%show_term joinStringsWith.type := String → String → String → String
end

open SubVerso.Examples in
-- ANCHOR: volume
def volume : Nat → Nat → Nat → Nat :=
  fun x y z => x * y * z
-- ANCHOR_END: volume
open SubVerso.Examples in
%show_name volume as volume.name

evaluation steps  {{{ joinStringsWithEx }}}
-- ANCHOR: joinStringsWithEx
joinStringsWith ", " "one" "and another"
===>
"one, and another"
-- ANCHOR_END: joinStringsWithEx
end evaluation steps


-- ANCHOR: StringTypeDef
def Str : Type := String
-- ANCHOR_END: StringTypeDef

open SubVerso.Examples in
%show_name Str as Str.name

-- ANCHOR: aStr
def aStr : Str := "This is a string."
-- ANCHOR_END: aStr


-- ANCHOR: NaturalNumberTypeDef
def NaturalNumber : Type := Nat
-- ANCHOR_END: NaturalNumberTypeDef

open SubVerso.Examples in
%show_name NaturalNumber

discarding
open SubVerso.Examples in
/--
error: failed to synthesize
  OfNat NaturalNumber 38
numerals are polymorphic in Lean, but the numeral `38` cannot be used in a context where the expected type is
  NaturalNumber
due to the absence of the instance above

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: thirtyEight
def thirtyEight : NaturalNumber := 38
-- ANCHOR_END: thirtyEight
stop discarding

open SubVerso.Examples in
-- ANCHOR: thirtyEightFixed
def thirtyEight : NaturalNumber := (38 : Nat)
-- ANCHOR_END: thirtyEightFixed

-- ANCHOR: NTypeDef
abbrev N : Type := Nat
-- ANCHOR_END: NTypeDef

-- ANCHOR: thirtyNine
def thirtyNine : N := 39
-- ANCHOR_END: thirtyNine




evaluation steps  {{{ NaturalNumberDef }}}
-- ANCHOR: NaturalNumberDef
NaturalNumber
===>
Nat
-- ANCHOR_END: NaturalNumberDef
end evaluation steps

/-- info:
1.2 : Float
-/
#check_msgs in
-- ANCHOR: onePointTwo
#check 1.2
-- ANCHOR_END: onePointTwo

/-- info:
-454.2123215 : Float
-/
#check_msgs in
-- ANCHOR: negativeLots
#check -454.2123215
-- ANCHOR_END: negativeLots

/-- info:
0.0 : Float
-/
#check_msgs in
-- ANCHOR: zeroPointZero
#check 0.0
-- ANCHOR_END: zeroPointZero

/-- info:
0 : Nat
-/
#check_msgs in
-- ANCHOR: zeroNat
#check 0
-- ANCHOR_END: zeroNat

/-- info:
0 : Float
-/
#check_msgs in
-- ANCHOR: zeroFloat
#check (0 : Float)
-- ANCHOR_END: zeroFloat


-- ANCHOR: Point
structure Point where
  x : Float
  y : Float
-- ANCHOR_END: Point


section
open SubVerso.Examples
%show_name Point as Point.name
%show_name Repr as Repr.name
open Point
%show_name x as Point.x
%show_name y as Point.y

end

-- ANCHOR: origin
def origin : Point := { x := 0.0, y := 0.0 }
-- ANCHOR_END: origin

/-- info:
{ x := 0.000000, y := 0.000000 }
-/
#check_msgs in
-- ANCHOR: originEval
#eval origin
-- ANCHOR_END: originEval

namespace Oops
  structure Point where
    x : Float
    y : Float

-- ANCHOR: originNoRepr
def origin : Point := { x := 0.0, y := 0.0 }
-- ANCHOR_END: originNoRepr

open SubVerso.Examples in
%show_name origin as origin.name

end Oops

/-- error:
invalid {...} notation, expected type is not known
-/
#check_msgs in
-- ANCHOR: originNoType
#check { x := 0.0, y := 0.0 }
-- ANCHOR_END: originNoType

/-- info:
{ x := 0.0, y := 0.0 } : Point
-/
#check_msgs in
-- ANCHOR: originWithAnnot
#check ({ x := 0.0, y := 0.0 } : Point)
-- ANCHOR_END: originWithAnnot

/-- info:
{ x := 0.0, y := 0.0 } : Point
-/
#check_msgs in
-- ANCHOR: originWithAnnot2
#check { x := 0.0, y := 0.0 : Point}
-- ANCHOR_END: originWithAnnot2

namespace Oops
-- ANCHOR: zeroXBad
def zeroX (p : Point) : Point :=
  { x := 0, y := p.y }
-- ANCHOR_END: zeroXBad
end Oops

-- ANCHOR: zeroX
def zeroX (p : Point) : Point :=
  { p with x := 0 }
-- ANCHOR_END: zeroX

open SubVerso.Examples in
%show_name zeroX as zeroX.name
open SubVerso.Examples in
%show_term zeroPointZero.term := 0.0

-- ANCHOR: fourAndThree
def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }
-- ANCHOR_END: fourAndThree



/-- info:
{ x := 4.300000, y := 3.400000 }
-/
#check_msgs in
-- ANCHOR: fourAndThreeEval
#eval fourAndThree
-- ANCHOR_END: fourAndThreeEval

/-- info:
{ x := 0.000000, y := 3.400000 }
-/
#check_msgs in
-- ANCHOR: zeroXFourAndThreeEval
#eval zeroX fourAndThree
-- ANCHOR_END: zeroXFourAndThreeEval

/-- info:
Point.mk : Float → Float → Point
-/
#check_msgs in
-- ANCHOR: Pointmk
#check (Point.mk)
-- ANCHOR_END: Pointmk

/-- info:
Point.x : Point → Float
-/
#check_msgs in
-- ANCHOR: Pointx
#check (Point.x)
-- ANCHOR_END: Pointx

/-- info:
Point.y : Point → Float
-/
#check_msgs in
-- ANCHOR: Pointy
#check (Point.y)
-- ANCHOR_END: Pointy

/-- info:
0.000000
-/
#check_msgs in
-- ANCHOR: originx1
#eval Point.x origin
-- ANCHOR_END: originx1

/-- info:
0.000000
-/
#check_msgs in
-- ANCHOR: originx
#eval origin.x
-- ANCHOR_END: originx

/-- info:
0.000000
-/
#check_msgs in
-- ANCHOR: originy
#eval origin.y
-- ANCHOR_END: originy

open SubVerso.Examples in
-- ANCHOR: addPoints
def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }
-- ANCHOR_END: addPoints

/-- info:
{ x := -6.500000, y := 32.200000 }
-/
#check_msgs in
-- ANCHOR: addPointsEx
#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }
-- ANCHOR_END: addPointsEx

-- ANCHOR: Point3D
structure Point3D where
  x : Float
  y : Float
  z : Float
-- ANCHOR_END: Point3D

-- ANCHOR: origin3D
def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }
-- ANCHOR_END: origin3D


namespace Ctor
-- ANCHOR: PointCtorName
structure Point where
  point ::
  x : Float
  y : Float
-- ANCHOR_END: PointCtorName
-- ANCHOR: PointCtorNameName
example := Point.point
-- ANCHOR_END: PointCtorNameName
end Ctor

section
open SubVerso.Examples
open Ctor
%show_name Point.point
end

/-- info:
{ x := 1.5, y := 2.8 } : Point
-/
#check_msgs in
-- ANCHOR: checkPointMk
#check Point.mk 1.5 2.8
-- ANCHOR_END: checkPointMk

/-- info:
"one string and another"
-/
#check_msgs in
-- ANCHOR: stringAppendDot
#eval "one string".append " and another"
-- ANCHOR_END: stringAppendDot


-- ANCHOR: modifyBoth
def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }
-- ANCHOR_END: modifyBoth

section
open SubVerso.Examples

%show_name Point.modifyBoth

open Point

%show_name modifyBoth as modifyBoth.name

end

/-- info:
{ x := 4.000000, y := 3.000000 }
-/
#check_msgs in
-- ANCHOR: modifyBothTest
#eval fourAndThree.modifyBoth Float.floor
-- ANCHOR_END: modifyBothTest

open SubVerso.Examples in
%show_name Float.floor

-- ANCHOR: distance
def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))
-- ANCHOR_END: distance

/-- info:
5.000000
-/
#check_msgs in
-- ANCHOR: evalDistance
#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }
-- ANCHOR_END: evalDistance


-- ANCHOR: Hamster
structure Hamster where
  name : String
  fluffy : Bool
-- ANCHOR_END: Hamster

-- ANCHOR: Book
structure Book where
  makeBook ::
  title : String
  author : String
  price : Float
-- ANCHOR_END: Book

set_option SubVerso.examples.suppressedNamespaces "Inductive Oops Ooops Oooops _root_ BetterPlicity StdLibNoUni BadUnzip NRT WithPattern MatchDef AutoImpl"

namespace Inductive

-- ANCHOR: Bool
inductive Bool where
  | false : Bool
  | true : Bool
-- ANCHOR_END: Bool
attribute [inherit_doc _root_.Bool] Inductive.Bool
attribute [inherit_doc _root_.Bool.true] Inductive.Bool.true
attribute [inherit_doc _root_.Bool.false] Inductive.Bool.false

section
-- ANCHOR: BoolNames
example : List Bool := [Bool.true, Bool.false]
open Bool
example : List Bool := [true, false]
-- ANCHOR_END: BoolNames
end

-- ANCHOR: Nat
inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
-- ANCHOR_END: Nat
attribute [inherit_doc _root_.Nat] Inductive.Nat
attribute [inherit_doc _root_.Nat.zero] Inductive.Nat.zero
attribute [inherit_doc _root_.Nat.succ] Inductive.Nat.succ

section
-- ANCHOR: NatNames
example : Nat := Nat.succ Nat.zero
open Nat
example : Nat := succ zero
-- ANCHOR_END: NatNames
end

open Nat
open SubVerso.Examples
%show_name Nat as fakeNat
%show_name Bool as fakeBool
section
open Inductive.Bool
%show_term fakeTrue : Inductive.Bool := true
%show_term fakeFalse : Inductive.Bool := false
end
%show_name Bool.true as fakeBool.true
%show_name Bool.false as fakeBool.false
%show_name zero as fakeZero
%show_name succ as fakeSucc

%show_name Nat.zero as Nat.fakeZero
%show_name Nat.succ as Nat.fakeSucc


instance : OfNat Inductive.Nat n where
  ofNat := go n
where
  go
    | .zero => .zero
    | .succ k => .succ (go k)


evaluation steps : Nat {{{ four }}}
-- ANCHOR: four
Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
===>
4
-- ANCHOR_END: four
end evaluation steps

end Inductive

open SubVerso.Examples in
-- ANCHOR: isZero
def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false
-- ANCHOR_END: isZero

evaluation steps  {{{ isZeroZeroSteps }}}
-- ANCHOR: isZeroZeroSteps
isZero Nat.zero
===>
match Nat.zero with
| Nat.zero => true
| Nat.succ k => false
===>
true
-- ANCHOR_END: isZeroZeroSteps
end evaluation steps

/-- info:
true
-/
#check_msgs in
-- ANCHOR: isZeroZero
#eval isZero 0
-- ANCHOR_END: isZeroZero

evaluation steps  {{{ isZeroFiveSteps }}}
-- ANCHOR: isZeroFiveSteps
isZero 5
===>
isZero (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
===>
match Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) with
| Nat.zero => true
| Nat.succ k => false
===>
false
-- ANCHOR_END: isZeroFiveSteps
end evaluation steps


/-- info:
false
-/
#check_msgs in
-- ANCHOR: isZeroFive
#eval isZero 5
-- ANCHOR_END: isZeroFive

open SubVerso.Examples in
-- ANCHOR: pred
def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k
-- ANCHOR_END: pred

open SubVerso.Examples in
%show_name pred as pred.name

/-- info:
4
-/
#check_msgs in
-- ANCHOR: predFive
#eval pred 5
-- ANCHOR_END: predFive


evaluation steps  {{{ predFiveSteps }}}
-- ANCHOR: predFiveSteps
pred 5
===>
pred (Nat.succ 4)
===>
match Nat.succ 4 with
| Nat.zero => Nat.zero
| Nat.succ k => k
===>
4
-- ANCHOR_END: predFiveSteps
end evaluation steps

/-- info:
838
-/
#check_msgs in
-- ANCHOR: predBig
#eval pred 839
-- ANCHOR_END: predBig

/-- info:
0
-/
#check_msgs in
-- ANCHOR: predZero
#eval pred 0
-- ANCHOR_END: predZero


-- ANCHOR: depth
def depth (p : Point3D) : Float :=
  match p with
  | { x:= h, y := w, z := d } => d
-- ANCHOR_END: depth

open SubVerso.Examples in
-- ANCHOR: even
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
-- ANCHOR_END: even

/-- info:
true
-/
#check_msgs in
-- ANCHOR: _something
#eval even 2
-- ANCHOR_END: _something

/-- info:
false
-/
#check_msgs in
-- ANCHOR: _something_more
#eval even 5
-- ANCHOR_END: _something_more


/-- error:
fail to show termination for
  evenLoops
with errors
failed to infer structural recursion:
Not considering parameter n of evenLoops:
  it is unchanged in the recursive calls
no parameters suitable for structural recursion

well-founded recursion cannot be used, 'evenLoops' does not take any (non-fixed) arguments
-/
#check_msgs in
-- ANCHOR: evenLoops
def evenLoops (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (evenLoops n)
-- ANCHOR_END: evenLoops

open SubVerso.Examples in
-- ANCHOR: plus
def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')
-- ANCHOR_END: plus

open SubVerso.Examples in
%show_name plus as plus.name

evaluation steps  {{{ plusThreeTwo }}}
-- ANCHOR: plusThreeTwo
plus 3 2
===>
plus 3 (Nat.succ (Nat.succ Nat.zero))
===>
match Nat.succ (Nat.succ Nat.zero) with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k')
===>
Nat.succ (plus 3 (Nat.succ Nat.zero))
===>
Nat.succ (match Nat.succ Nat.zero with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k'))
===>
Nat.succ (Nat.succ (plus 3 Nat.zero))
===>
Nat.succ (Nat.succ (match Nat.zero with
| Nat.zero => 3
| Nat.succ k' => Nat.succ (plus 3 k')))
===>
Nat.succ (Nat.succ 3)
===>
5
-- ANCHOR_END: plusThreeTwo
end evaluation steps

-- ANCHOR: times
def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')
-- ANCHOR_END: times

#eval times 5 3

-- ANCHOR: minus
def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')
-- ANCHOR_END: minus

open SubVerso.Examples in
/--
error: fail to show termination for
  div
with errors
failed to infer structural recursion:
Not considering parameter k of div:
  it is unchanged in the recursive calls
Cannot use parameter k:
  failed to eliminate recursive application
    div (n - k) k


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
k n : Nat
h✝ : ¬n < k
⊢ n - k < n
-/
#check_msgs in
-- ANCHOR: div
def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)
-- ANCHOR_END: div


open SubVerso.Examples in
-- ANCHOR: PPoint
structure PPoint (α : Type) where
  x : α
  y : α
-- ANCHOR_END: PPoint


section
open SubVerso.Examples
%show_name PPoint as PPoint.name
open PPoint
%show_name x as PPoint.x
%show_name y as PPoint.y
end


-- ANCHOR: natPoint
def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }
-- ANCHOR_END: natPoint

section
open SubVerso.Examples
%show_name natOrigin as natOrigin.name
end



-- ANCHOR: toPPoint
def Point.toPPoint (p : Point) : PPoint Float :=
  { x := p.x, y := p.y }
-- ANCHOR_END: toPPoint

open SubVerso.Examples in
-- ANCHOR: replaceX
def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
-- ANCHOR_END: replaceX

/-- info:
replaceX : (α : Type) → PPoint α → α → PPoint α
-/
#check_msgs in
-- ANCHOR: replaceXT
#check (replaceX)
-- ANCHOR_END: replaceXT

open SubVerso.Examples in
/-- info:
replaceX Nat : PPoint Nat → Nat → PPoint Nat
-/
#check_msgs in
-- ANCHOR: replaceXNatT
#check replaceX Nat
-- ANCHOR_END: replaceXNatT

/-- info:
replaceX Nat natOrigin : Nat → PPoint Nat
-/
#check_msgs in
-- ANCHOR: replaceXNatOriginT
#check replaceX Nat natOrigin
-- ANCHOR_END: replaceXNatOriginT

/-- info:
replaceX Nat natOrigin 5 : PPoint Nat
-/
#check_msgs in
-- ANCHOR: replaceXNatOriginFiveT
#check replaceX Nat natOrigin 5
-- ANCHOR_END: replaceXNatOriginFiveT

/-- info:
{ x := 5, y := 0 }
-/
#check_msgs in
-- ANCHOR: replaceXNatOriginFiveV
#eval replaceX Nat natOrigin 5
-- ANCHOR_END: replaceXNatOriginFiveV

-- ANCHOR: primesUnder10
def primesUnder10 : List Nat := [2, 3, 5, 7]
-- ANCHOR_END: primesUnder10

open SubVerso.Examples in
%show_name primesUnder10 as primesUnder10.name

namespace Oops
open SubVerso.Examples

-- ANCHOR: List
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
-- ANCHOR_END: List

%show_term fakeList : Type → Type := List

open List

%show_term fakeNil : {α : Type} → Oops.List α := nil
%show_term fakeCons : {α : Type} → α → Oops.List α → Oops.List α := cons

end Oops
similar datatypes List Oops.List


-- ANCHOR: explicitPrimesUnder10
def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))
-- ANCHOR_END: explicitPrimesUnder10

open SubVerso.Examples in
%show_name explicitPrimesUnder10 as explicitPrimesUnder10.name

namespace Ooops
open SubVerso.Examples

-- ANCHOR: length1
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons y ys => Nat.succ (length α ys)
-- ANCHOR_END: length1


evaluation steps  {{{ length1EvalSummary }}}
-- ANCHOR: length1EvalSummary
length String ["Sourdough", "bread"]
===>
length String (List.cons "Sourdough" (List.cons "bread" List.nil))
===>
Nat.succ (length String (List.cons "bread" List.nil))
===>
Nat.succ (Nat.succ (length String List.nil))
===>
Nat.succ (Nat.succ Nat.zero)
===>
2
-- ANCHOR_END: length1EvalSummary
end evaluation steps

evaluation steps  {{{ length1Eval }}}
-- ANCHOR: length1Eval
length String ["Sourdough", "bread"]
===>
length String (List.cons "Sourdough" (List.cons "bread" List.nil))
===>
match List.cons "Sourdough" (List.cons "bread" List.nil) with
| List.nil => Nat.zero
| List.cons y ys => Nat.succ (length String ys)
===>
Nat.succ (length String (List.cons "bread" List.nil))
===>
Nat.succ (match List.cons "bread" List.nil with
| List.nil => Nat.zero
| List.cons y ys => Nat.succ (length String ys))
===>
Nat.succ (Nat.succ (length String List.nil))
===>
Nat.succ (Nat.succ (match List.nil with
| List.nil => Nat.zero
| List.cons y ys => Nat.succ (length String ys)))
===>
Nat.succ (Nat.succ Nat.zero)
===>
2
-- ANCHOR_END: length1Eval
end evaluation steps
end Ooops



namespace Oooops
-- ANCHOR: length2
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length α ys)
-- ANCHOR_END: length2
end Oooops


namespace BetterPlicity
open SubVerso.Examples
-- ANCHOR: replaceXImp
def replaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
-- ANCHOR_END: replaceXImp

/-- info:
{ x := 5, y := 0 }
-/
#check_msgs in
-- ANCHOR: replaceXImpNat
#eval replaceX natOrigin 5
-- ANCHOR_END: replaceXImpNat


-- ANCHOR: lengthImp
def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
-- ANCHOR_END: lengthImp

/-- info:
4
-/
#check_msgs in
-- ANCHOR: lengthImpPrimes
#eval length primesUnder10
-- ANCHOR_END: lengthImpPrimes
end BetterPlicity

/-- info:
4
-/
#check_msgs in
-- ANCHOR: lengthDotPrimes
#eval primesUnder10.length
-- ANCHOR_END: lengthDotPrimes

/-- info:
List.length : List Int → Nat
-/
#check_msgs in
-- ANCHOR: lengthExpNat
#check List.length (α := Int)
-- ANCHOR_END: lengthExpNat

def x := Unit

structure Iso (α : Type u) (β : Type u) : Type u where
  into : α → β
  outOf : β → α
  comp1 : into ∘ outOf = id
  comp2 : outOf ∘ into = id


-- Standard library copies without universe parameters
namespace StdLibNoUni
open SubVerso.Examples

-- ANCHOR: Option
inductive Option (α : Type) : Type where
  | none : Option α
  | some (val : α) : Option α
-- ANCHOR_END: Option

%show_name Option as fakeOption
%show_name Option.none as fakeOption.none
%show_name Option.some as fakeOption.some
namespace Option
%show_name none as fakeNone
%show_name some as fakeSome
end Option

-- ANCHOR: Prod
structure Prod (α : Type) (β : Type) : Type where
  fst : α
  snd : β
-- ANCHOR_END: Prod

%show_name Prod as fakeProd
%show_name Prod.fst as fakeProd.fst
%show_name Prod.snd as fakeProd.snd
namespace Prod
%show_name fst as fakeFst
%show_name snd as fakeSnd
end Prod

-- Justify the claim in the text that Prod could be used instead of PPoint
def iso_Prod_PPoint {α : Type} : Iso (Prod α α) (PPoint α) := by
  constructor
  case into => apply (fun prod => PPoint.mk prod.fst prod.snd)
  case outOf => apply (fun point => Prod.mk point.x point.y)
  case comp1 => funext _ <;> simp
  case comp2 => funext _ <;> simp



-- ANCHOR: Sum
inductive Sum (α : Type) (β : Type) : Type where
  | inl : α → Sum α β
  | inr : β → Sum α β
-- ANCHOR_END: Sum

-- ANCHOR: Sumαβ
%show_term Sumαβ := {α β : Type} → Sum α β → α ⊕ β
-- ANCHOR_END: Sumαβ

-- ANCHOR: FakeSum
%show_name Sum as fakeSum
%show_name Sum.inl as fakeSum.inl
%show_name Sum.inr as fakeSum.inr
namespace Sum
%show_name inl as fakeInl
%show_name inr as fakeInr
end Sum
-- ANCHOR_END: FakeSum


-- ANCHOR: Unit
inductive Unit : Type where
  | unit : Unit
-- ANCHOR_END: Unit

%show_name Unit as fakeUnit

section
open Unit
%show_name unit as fakeunit
end

inductive Empty : Type where

end StdLibNoUni

similar datatypes Option StdLibNoUni.Option
similar datatypes Prod StdLibNoUni.Prod
similar datatypes Sum StdLibNoUni.Sum
similar datatypes PUnit StdLibNoUni.Unit
similar datatypes Empty StdLibNoUni.Empty

-- ANCHOR: PetName
def PetName : Type := String ⊕ String
-- ANCHOR_END: PetName

open SubVerso.Examples in
%show_name PetName as PetName.name

-- ANCHOR: animals
def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi",
   Sum.inl "Rex", Sum.inr "Floof"]
-- ANCHOR_END: animals

-- ANCHOR: howManyDogs
def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets
-- ANCHOR_END: howManyDogs

section
variable (morePets : List PetName)

-- ANCHOR: howManyDogsAdd
example : (
howManyDogs morePets + 1
) = (
(howManyDogs morePets) + 1
) := rfl
-- ANCHOR_END: howManyDogsAdd
end

/-- info:
3
-/
#check_msgs in
-- ANCHOR: dogCount
#eval howManyDogs animals
-- ANCHOR_END: dogCount

-- ANCHOR: unitParens
example : Unit := (() : Unit)
-- ANCHOR_END: unitParens


open SubVerso.Examples in
-- ANCHOR: ArithExpr
inductive ArithExpr (ann : Type) : Type where
  | int : ann → Int → ArithExpr ann
  | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
  | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
-- ANCHOR_END: ArithExpr

-- ANCHOR: ArithExprEx
section
open SubVerso.Examples
structure SourcePos where
  line : Nat
  column : Nat

%show_term «ArithExpr SourcePos» := ArithExpr SourcePos
%show_term «ArithExpr Unit» := ArithExpr Unit
%show_name SourcePos as SourcePos.name

end
-- ANCHOR_END: ArithExprEx

-- ANCHOR: nullOne
example : Option (Option Int) := none
-- ANCHOR_END: nullOne

-- ANCHOR: nullTwo
example : Option (Option Int) := some none
-- ANCHOR_END: nullTwo

-- ANCHOR: nullThree
example : Option (Option Int) := some (some 360)
-- ANCHOR_END: nullThree


namespace Floop
open SubVerso.Examples

-- ANCHOR: headHuh
def List.head? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | y :: _ => some y
-- ANCHOR_END: headHuh

%show_name List.head? as fakeHead?

/-- info:
some 2
-/
#check_msgs in
-- ANCHOR: headSome
#eval primesUnder10.head?
-- ANCHOR_END: headSome

/--
error: don't know how to synthesize implicit argument 'α'
  @_root_.List.head? ?m.41386 []
context:
⊢ Type ?u.41383
---
error: don't know how to synthesize implicit argument 'α'
  @List.nil ?m.41386
context:
⊢ Type ?u.41383
-/
#check_msgs in
-- ANCHOR: headNoneBad
#eval [].head?
-- ANCHOR_END: headNoneBad

/--
error: don't know how to synthesize implicit argument 'α'
  @_root_.List.head? ?m.41395 []
context:
⊢ Type ?u.41392
---
error: don't know how to synthesize implicit argument 'α'
  @List.nil ?m.41395
context:
⊢ Type ?u.41392
-/
#check_msgs in
-- ANCHOR: headNoneBad2
#eval [].head?
-- ANCHOR_END: headNoneBad2


/-- info:
none
-/
#check_msgs in
-- ANCHOR: headNone
#eval [].head? (α := Int)
-- ANCHOR_END: headNone

/-- info:
none
-/
#check_msgs in
-- ANCHOR: headNoneTwo
#eval ([] : List Int).head?
-- ANCHOR_END: headNoneTwo






def List.final? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [y] => some y
  | y1 :: y2 :: ys => final? (y2::ys)


end Floop

open SubVerso.Examples in
%show_term αxβ := (α β : Type) → Prod α β → α × β


namespace StructNotation
-- ANCHOR: fivesStruct
def fives : String × Int := { fst := "five", snd := 5 }
-- ANCHOR_END: fivesStruct
end StructNotation

-- ANCHOR: fives
def fives : String × Int := ("five", 5)
-- ANCHOR_END: fives

example : StructNotation.fives = fives := by rfl


namespace Nested
-- ANCHOR: sevensNested
def sevens : String × (Int × Nat) := ("VII", (7, 4 + 3))
-- ANCHOR_END: sevensNested
end Nested

-- ANCHOR: sevens
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
-- ANCHOR_END: sevens

-- Backing up that they are equivalent
example : Nested.sevens = sevens := by rfl


example : sevens.swap = ((7, 7), "VII") := by rfl


def findString (haystack : List String) (needle : String) : Option Int :=
  match haystack with
  | [] => none
  | x :: xs =>
    if needle == x then
      some 0
    else match findString xs needle with
         | none => none
         | some i => some (i + 1)

inductive LinkedList : Type -> Type where
  | nil : LinkedList α
  | cons : α → LinkedList α → LinkedList α

def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  match xs with
  | [] => none
  | y :: ys => if predicate y then some y else ys.findFirst? predicate


-- ANCHOR: Sign
inductive Sign where
  | pos
  | neg
-- ANCHOR_END: Sign

open SubVerso.Examples in
-- ANCHOR: posOrNegThree
def posOrNegThree (s : Sign) :
    match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)
-- ANCHOR_END: posOrNegThree


section
open SubVerso.Examples
%show_name posOrNegThree as posOrNegThree.name
%show_name Sign.pos as Sign.pos.name
%show_name Sign.neg as Sign.neg.name
open Sign
%show_name pos as pos.name
%show_name neg as neg.name
end

evaluation steps  {{{ posOrNegThreePos }}}
-- ANCHOR: posOrNegThreePos
(posOrNegThree Sign.pos :
 match Sign.pos with | Sign.pos => Nat | Sign.neg => Int)
===>
((match Sign.pos with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)) :
 match Sign.pos with | Sign.pos => Nat | Sign.neg => Int)
===>
((3 : Nat) : Nat)
===>
3
-- ANCHOR_END: posOrNegThreePos
end evaluation steps



def take (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | _, [] => []
  | Nat.zero, _ => []
  | Nat.succ n', x :: xs => x :: take n' xs



/-- info:
["bolete", "oyster"]
-/
#check_msgs in
-- ANCHOR: takeThree
#eval take 3 ["bolete", "oyster"]
-- ANCHOR_END: takeThree

/-- info:
["bolete"]
-/
#check_msgs in
-- ANCHOR: takeOne
#eval take 1 ["bolete", "oyster"]
-- ANCHOR_END: takeOne


-- sum notation
example : (Sum α β) = (α ⊕ β) := by rfl

def Exhausts (α : Type) (xs : List α) := (x : α) → x ∈ xs

example : Exhausts (Bool × Unit) [(true, Unit.unit), (false, Unit.unit)] := by
  intro ⟨ fst, snd ⟩
  cases fst <;> cases snd <;> simp

example : Exhausts (Bool ⊕ Unit) [Sum.inl true, Sum.inl false, Sum.inr Unit.unit] := by
  intro x
  cases x with
  | inl y => cases y <;> simp
  | inr y => cases y <;> simp

example : Exhausts (Bool ⊕ Empty) [Sum.inl true, Sum.inl false] := by
  intro x
  cases x with
  | inl y => cases y <;> repeat constructor
  | inr y => cases y


discarding
/--
error: Invalid universe level in constructor `MyType.ctor`: Parameter `α` has type
  Type
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1
-/
#check_msgs in
-- ANCHOR: TypeInType
inductive MyType : Type where
  | ctor : (α : Type) → α → MyType
-- ANCHOR_END: TypeInType
stop discarding

discarding
/-- error:
(kernel) arg #1 of 'MyType.ctor' has a non positive occurrence of the datatypes being declared
-/
#check_msgs in
-- ANCHOR: Positivity
inductive MyType : Type where
  | ctor : (MyType → Int) → MyType
-- ANCHOR_END: Positivity
stop discarding

#eval if let Option.some x := Option.some 5 then x else 55

section
open SubVerso.Examples

discarding
/-- error:
type expected, got
  (MyType : Type → Type)
-/
#check_msgs in
-- ANCHOR: MissingTypeArg
inductive MyType (α : Type) : Type where
  | ctor : α → MyType
-- ANCHOR_END: MissingTypeArg
stop discarding


-- ANCHOR: MyTypeDef
inductive MyType (α : Type) : Type where
  | ctor : α → MyType α
-- ANCHOR_END: MyTypeDef

-- ANCHOR: MissingTypeArgT
example : Type → Type := MyType
-- ANCHOR_END: MissingTypeArgT

%show_name MyType as MyType.name
section
open MyType
%show_name ctor as MyType.ctor.name
end

/-- error:
type expected, got
  (MyType : Type → Type)
-/
#check_msgs in
-- ANCHOR: MissingTypeArg2
def ofFive : MyType := ctor 5
-- ANCHOR_END: MissingTypeArg2

-- ANCHOR: WoodSplittingTool
inductive WoodSplittingTool where
  | axe
  | maul
  | froe
-- ANCHOR_END: WoodSplittingTool

/-- info: WoodSplittingTool.axe -/
#check_msgs in
-- ANCHOR: evalAxe
#eval WoodSplittingTool.axe
-- ANCHOR_END: evalAxe

-- ANCHOR: allTools
def allTools : List WoodSplittingTool := [
  WoodSplittingTool.axe,
  WoodSplittingTool.maul,
  WoodSplittingTool.froe
]
-- ANCHOR_END: allTools

/--
error: could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  List WoodSplittingTool
-/
#check_msgs in
-- ANCHOR: evalAllTools
#eval allTools
-- ANCHOR_END: evalAllTools

-- ANCHOR: Firewood
inductive Firewood where
  | birch
  | pine
  | beech
deriving Repr
-- ANCHOR_END: Firewood

-- ANCHOR: allFirewood
def allFirewood : List Firewood := [
  Firewood.birch,
  Firewood.pine,
  Firewood.beech
]
-- ANCHOR_END: allFirewood

/-- info: [Firewood.birch, Firewood.pine, Firewood.beech] -/
#check_msgs in
-- ANCHOR: evalAllFirewood
#eval allFirewood
-- ANCHOR_END: evalAllFirewood

end

-- Example solution
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | [] => []
  | x :: xs' =>
    match ys with
    | [] => []
    | y :: ys' => (x, y) :: zip xs' ys'

variable {α β : Type}

open SubVerso.Examples in
/--
error: fail to show termination for
  sameLength
with errors
failed to infer structural recursion:
Not considering parameter α of sameLength:
  it is unchanged in the recursive calls
Not considering parameter β of sameLength:
  it is unchanged in the recursive calls
Cannot use parameter xs:
  failed to eliminate recursive application
    sameLength xs' ys'
Cannot use parameter ys:
  failed to eliminate recursive application
    sameLength xs' ys'


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
              xs ys
1) 1816:28-46  ?  ?
Please use `termination_by` to specify a decreasing measure.
-/
#check_msgs in
-- ANCHOR: sameLengthPair
def sameLength (xs : List α) (ys : List β) : Bool :=
  match (xs, ys) with
  | ([], []) => true
  | (x :: xs', y :: ys') => sameLength xs' ys'
  | _ => false
-- ANCHOR_END: sameLengthPair

namespace Nested
-- ANCHOR: sameLengthOk1
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs with
  | [] =>
    match ys with
    | [] => true
    | _ => false
  | x :: xs' =>
    match ys with
    | y :: ys' => sameLength xs' ys'
    | _ => false
-- ANCHOR_END: sameLengthOk1
end Nested

namespace Both
-- ANCHOR: sameLengthOk2
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => sameLength xs' ys'
  | _, _ => false
-- ANCHOR_END: sameLengthOk2
end Both

namespace AutoImpl
-- ANCHOR: lengthImpAuto
def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
-- ANCHOR_END: lengthImpAuto

end AutoImpl

namespace MatchDef
variable {α : Type}
open SubVerso.Examples

-- ANCHOR: lengthMatchDef
def length : List α → Nat
  | [] => 0
  | y :: ys => Nat.succ (length ys)
-- ANCHOR_END: lengthMatchDef
end MatchDef

section
variable {α : Type}
open SubVerso.Examples in
-- ANCHOR: drop
def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, x :: xs => drop n xs
-- ANCHOR_END: drop



-- ANCHOR: fromOption
def fromOption (default : α) : Option α → α
  | none => default
  | some x => x
-- ANCHOR_END: fromOption
end

/-- info:
"salmonberry"
-/
#check_msgs in
-- ANCHOR: getD
#eval (some "salmonberry").getD ""
-- ANCHOR_END: getD

/-- info:
""
-/
#check_msgs in
-- ANCHOR: getDNone
#eval none.getD ""
-- ANCHOR_END: getDNone

section
variable {α β : Type}
namespace BadUnzip

open SubVerso.Examples

-- ANCHOR: unzipBad
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    (x :: (unzip xys).fst, y :: (unzip xys).snd)
-- ANCHOR_END: unzipBad

%show_name unzip as unzipBad.name
end BadUnzip

-- ANCHOR: unzip
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
-- ANCHOR_END: unzip

open SubVerso.Examples in
%show_name unzip as unzip.name

open SubVerso.Examples in
-- ANCHOR: reverse
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []
-- ANCHOR_END: reverse
end
namespace WithPattern
variable {α β : Type}
-- ANCHOR: unzipPat
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) : List α × List β := unzip xys
    (x :: xs, y :: ys)
-- ANCHOR_END: unzipPat
end WithPattern

namespace NT
variable {α β : Type}
open SubVerso.Examples
-- ANCHOR: unzipNT
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
-- ANCHOR_END: unzipNT


-- ANCHOR: idA
def id (x : α) : α := x
-- ANCHOR_END: idA

end NT

namespace NRT
variable {α β : Type}
open SubVerso.Examples
-- ANCHOR: unzipNRT
def unzip (pairs : List (α × β)) :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
-- ANCHOR_END: unzipNRT

-- ANCHOR: idB
def id (x : α) := x
-- ANCHOR_END: idB

end NRT




namespace ReallyNoTypes
open SubVerso.Examples

/--
error: Failed to infer type of definition `id`
---
error: Failed to infer type of binder `x`
-/
#check_msgs in
-- ANCHOR: identNoTypes
def id x := x
-- ANCHOR_END: identNoTypes

/--
error: Invalid match expression: This pattern contains metavariables:
  []
-/
#check_msgs in
-- ANCHOR: unzipNoTypesAtAll
def unzip pairs :=
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)
-- ANCHOR_END: unzipNoTypesAtAll
end ReallyNoTypes


/-- info:
14 : Nat
-/
#check_msgs in
-- ANCHOR: fourteenNat
#check 14
-- ANCHOR_END: fourteenNat

/-- info:
14 : Int
-/
#check_msgs in
-- ANCHOR: fourteenInt
#check (14 : Int)
-- ANCHOR_END: fourteenInt

namespace Match
variable {α β : Type}
open SubVerso.Examples
-- ANCHOR: dropMatch
def drop (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | Nat.zero, ys => ys
  | _, [] => []
  | Nat.succ n , y :: ys => drop n ys
-- ANCHOR_END: dropMatch

-- ANCHOR: evenFancy
def even : Nat → Bool
  | 0 => true
  | n + 1 => not (even n)
-- ANCHOR_END: evenFancy

namespace Explicit
-- ANCHOR: explicitHalve
def halve : Nat → Nat
  | Nat.zero => 0
  | Nat.succ Nat.zero => 0
  | Nat.succ (Nat.succ n) => halve n + 1
-- ANCHOR_END: explicitHalve
end Explicit


-- ANCHOR: halve
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1
-- ANCHOR_END: halve

-- ANCHOR: halveParens
%show_term halveParens := fun n => [(halve n) + 1, halve (n + 1)]
-- ANCHOR_END: halveParens

example : Explicit.halve = halve := by
  funext x
  fun_induction halve x <;> simp [halve, Explicit.halve, *]

namespace Oops
/--
error: Invalid pattern(s): `n` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching:
  .(Nat.add 2 n)
-/
#check_msgs in
-- ANCHOR: halveFlippedPat
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | 2 + n => halve n + 1
-- ANCHOR_END: halveFlippedPat
end Oops

end Match


evaluation steps  {{{ incrSteps }}}
-- ANCHOR: incrSteps
fun x => x + 1
===>
(· + 1)
===>
Nat.succ
-- ANCHOR_END: incrSteps
end evaluation steps

/-- info:
fun x => x + 1 : Nat → Nat
-/
#check_msgs in
-- ANCHOR: incr
#check fun x => x + 1
-- ANCHOR_END: incr

/-- info:
fun x => x + 1 : Int → Int
-/
#check_msgs in
-- ANCHOR: incrInt
#check fun (x : Int) => x + 1
-- ANCHOR_END: incrInt

/-- info:
fun {α} x => x : {α : Type} → α → α
-/
#check_msgs in
-- ANCHOR: identLambda
#check fun {α : Type} (x : α) => x
-- ANCHOR_END: identLambda

/-- info:
fun x =>
  match x with
  | 0 => none
  | n.succ => some n : Nat → Option Nat
-/
#check_msgs in
-- ANCHOR: predHuh
#check fun
  | 0 => none
  | n + 1 => some n
-- ANCHOR_END: predHuh

namespace Double
-- ANCHOR: doubleLambda
def double : Nat → Nat := fun
  | 0 => 0
  | k + 1 => double k + 2
-- ANCHOR_END: doubleLambda
end Double

evaluation steps  {{{ funPair }}}
-- ANCHOR: funPair
(· + 5, 3)
-- ANCHOR_END: funPair
end evaluation steps

evaluation steps  {{{ pairFun }}}
-- ANCHOR: pairFun
((· + 5), 3)
-- ANCHOR_END: pairFun
end evaluation steps


evaluation steps  {{{ twoDots }}}
-- ANCHOR: twoDots
(· , ·) 1 2
===>
(1, ·) 2
===>
(1, 2)
-- ANCHOR_END: twoDots
end evaluation steps


/-- info:
10
-/
#check_msgs in
-- ANCHOR: applyLambda
#eval (fun x => x + x) 5
-- ANCHOR_END: applyLambda


/-- info:
10
-/
#check_msgs in
-- ANCHOR: applyCdot
#eval (· * 2) 5
-- ANCHOR_END: applyCdot

-- ANCHOR: NatDouble
def Nat.double (x : Nat) : Nat := x + x
-- ANCHOR_END: NatDouble

open SubVerso.Examples in
%show_name Nat.double as Nat.double.name
section
open SubVerso.Examples
open Nat
%show_name double as double.name

end



/-- info:
8
-/
#check_msgs in
-- ANCHOR: NatDoubleFour
#eval (4 : Nat).double
-- ANCHOR_END: NatDoubleFour

-- ANCHOR: NewNamespace
namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace
-- ANCHOR_END: NewNamespace

section
open SubVerso.Examples
open NewNamespace
%show_name triple
%show_name quadruple
end


/-- info:
NewNamespace.triple (x : Nat) : Nat
-/
#check_msgs in
-- ANCHOR: tripleNamespace
#check NewNamespace.triple
-- ANCHOR_END: tripleNamespace

/-- info:
NewNamespace.quadruple (x : Nat) : Nat
-/
#check_msgs in
-- ANCHOR: quadrupleNamespace
#check NewNamespace.quadruple
-- ANCHOR_END: quadrupleNamespace


-- ANCHOR: quadrupleOpenDef
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)
-- ANCHOR_END: quadrupleOpenDef

open SubVerso.Examples in
%show_name timesTwelve

example : timesTwelve 2 = 24 := by rfl

/-- info:
NewNamespace.quadruple (x : Nat) : Nat
-/
#check_msgs in
-- ANCHOR: quadrupleNamespaceOpen
open NewNamespace in
#check quadruple
-- ANCHOR_END: quadrupleNamespaceOpen



/-- info:
"three fives is 15"
-/
#check_msgs in
-- ANCHOR: interpolation
#eval s!"three fives is {NewNamespace.triple 5}"
-- ANCHOR_END: interpolation

/--
error: failed to synthesize
  ToString (Nat → Nat)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
---
info: toString "three fives is " ++ sorry ++ toString "" : String
-/
#check_msgs in
-- ANCHOR: interpolationOops
#check s!"three fives is {NewNamespace.triple}"
-- ANCHOR_END: interpolationOops


-- ANCHOR: Inline
inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline
-- ANCHOR_END: Inline

namespace WithMatch
-- ANCHOR: inlineStringHuhMatch
def Inline.string? (inline : Inline) : Option String :=
  match inline with
  | Inline.string s => some s
  | _ => none
-- ANCHOR_END: inlineStringHuhMatch
end WithMatch



-- ANCHOR: inlineStringHuh
def Inline.string? (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else none
-- ANCHOR_END: inlineStringHuh

example : WithMatch.Inline.string? = Inline.string? := by rfl

-- ANCHOR: pointCtor
example : (Point.mk 1 2 : (Point)) = ({ x := 1, y := 2 } : (Point)) := rfl
-- ANCHOR_END: pointCtor

-- ANCHOR: pointBraces
example : ({ x := 1, y := 2 } : (Point)) = (Point.mk 1 2 : (Point)) := rfl
-- ANCHOR_END: pointBraces

-- ANCHOR: pointPos
example : (⟨1, 2⟩ : (Point)) = (Point.mk 1 2 : (Point)) := rfl
-- ANCHOR_END: pointPos


/-- error: Invalid `⟨...⟩` notation: The expected type of this term could not be determined -/
#check_msgs in
-- ANCHOR: pointPosEvalNoType
#eval ⟨1, 2⟩
-- ANCHOR_END: pointPosEvalNoType

/-- info:
{ x := 1.000000, y := 2.000000 }
-/
#check_msgs in
-- ANCHOR: pointPosWithType
#eval (⟨1, 2⟩ : Point)
-- ANCHOR_END: pointPosWithType


-- ANCHOR: swapLambda
example : (Point → Point) := fun (point : Point) => { x := point.y, y := point.x : Point }
-- ANCHOR_END: swapLambda

-- ANCHOR: subOneDots
example : ((· - 1) : (Int → Int)) = (fun x => x - 1 : (Int → Int)) := rfl
-- ANCHOR_END: subOneDots

open SubVerso.Examples

section
%show_term sizes := (α β : Type) → α → β → α ⊕ β → α × β
%show_term «Bool × Unit» := Bool × Unit
-- ANCHOR: BoolxUnit
%show_term BoolxUnit.vals : List (Bool × Unit) := [(true, Unit.unit), (false, Unit.unit)]
-- ANCHOR_END: BoolxUnit
%show_term «Bool ⊕ Unit» := Bool ⊕ Unit
-- ANCHOR: BooloUnit
%show_term BooloUnit.vals : List (Bool ⊕ Unit) := [Sum.inl true, Sum.inl false, Sum.inr Unit.unit]
-- ANCHOR_END: BooloUnit
end

section
open Point3D
%show_name z as Point3D.z.name
end
%show_name Point3D as Point3D.name

%show_term oak := "oak "
%show_term great := "great "
%show_term tree := "tree"
%show_name String.append
%show_name Nat as Nat.name
%show_name Nat.zero as Nat.zero.name
%show_name Nat.succ as Nat.succ.name

section
open Nat
%show_name succ as succ.name
%show_name zero as zero.name
end
section
open List
%show_name cons as cons.name
%show_name nil as nil.name
end
%show_name List.cons as List.cons.name
%show_name List.nil as List.nil.name

%show_name Prod as Prod.name
%show_name Prod.mk as Prod.mk.name
%show_name Prod.fst as Prod.fst.name
%show_name Prod.snd as Prod.snd.name

%show_name Sum as Sum.name
%show_name Sum.inl as Sum.inl.name
%show_name Sum.inr as Sum.inr.name


%show_name addPoints as addPoints.name
%show_name replaceX as replaceX.name
%show_name isZero as isZero.name
%show_name Float as Float.name
%show_name Int as Int.name
%show_name Bool as Bool.name
%show_name true
%show_name false
%show_name Bool.true
%show_name Bool.false
%show_name String as String.name
%show_name Hamster as Hamster.name
%show_name Book as Book.name
%show_name aStr as aStr.name
%show_name List as List.name
%show_name List.head as List.head.name
%show_name List.head? as List.head?.name

section
open List
%show_name head? as head?.name
end

%show_name List.head! as List.head!.name
%show_name List.headD as List.headD.name

%show_name Option.getD as Option.getD.name

%show_name Empty as Empty.name
%show_name Unit as Unit.name
%show_name Unit.unit as Unit.unit.name
%show_name Option as Option.name
%show_name some as some.name
%show_name none as none.name
%show_name Option.some as Option.some.name
%show_name Option.none as Option.none.name
%show_name Point.mk as Point.mk
%show_name Point.x as Point.x.name
%show_name Point.y as Point.y.name
%show_name fourAndThree as fourAndThree.name
%show_term «Option Int» := Option Int
%show_term «Option (List String)» := Option (List String)
%show_term «Nat→Bool» := Nat → Bool
%show_term «Nat→Nat→Nat» := Nat → Nat → Nat
%show_term «Nat→(Nat→Nat)» := Nat → (Nat → Nat)
%show_name maximum as maximum.name
%show_name spaceBetween as spaceBetween.name
-- ANCHOR: evalEx
%show_term ex1 := 42 + 19
%show_term ex2 := String.append "A" (String.append "B" "C")
%show_term ex3 := String.append (String.append "A" "B") "C"
%show_term ex4 := if 3 == 3 then 5 else 7
%show_term ex5 := if 3 == 4 then "equal" else "not equal"
-- ANCHOR_END: evalEx
%show_term zero := 0
%show_term «0» := 0
%show_term «5» := 5
%show_term «Type» := Type
%show_term «Type→Type» := Type → Type
%show_term «List Nat» := List Nat
%show_term «List String» := List String
%show_term «List (List Point)» := List (List Point)
%show_term «Prod Nat String» := Prod Nat String
%show_term «Prod Nat Nat» := Prod Nat Nat
%show_term «PPoint Nat» := PPoint Nat
%show_term «Sum String Int» := Sum String Int
%show_name List.length as List.length.name
%show_name List.map as List.map.name
%show_name Array.map as Array.map.name
section

-- ANCHOR: distr
%show_term distr := (α β γ : Type) → α × (β ⊕ γ) → (α × β) ⊕ (α × γ) → Bool × α → α ⊕ α
-- ANCHOR_END: distr

end

-- ANCHOR: α
example : Type 1 := ({α : Type} → α → Nat : Type 1)
-- ANCHOR_END: α

namespace Oops
axiom mySorry : α
scoped macro "…" : term => `(mySorry)

noncomputable section

-- ANCHOR: List.findFirst?Ex
def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := …
-- ANCHOR_END: List.findFirst?Ex
%show_name List.findFirst?

-- ANCHOR: Prod.switchEx
def Prod.switch {α β : Type} (pair : α × β) : β × α := …
-- ANCHOR_END: Prod.switchEx
%show_name Prod.switch

-- ANCHOR: zipEx
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := …
-- ANCHOR_END: zipEx
%show_name zip

end
end Oops


-- ANCHOR: fragments
example := [List Nat, List String, List (List Point), PPoint Int, Nat, Bool × Unit, Bool ⊕ Unit, Empty, Option (List String)]
example := [Prod Nat String, Prod Nat Nat, Sum String Int]
example := Point3D.z
example := {α : Type} → Nat → α → List α
example := Option (String ⊕ (Nat × String))
example := @Option.getD
example := Nat.double
section
open Nat
example := double
end
example := @List.nil
example := @List.cons
example := @List.head!
example := @List.head?
example := @List.headD
example := @List.head
example := @List.map
example := @Array.map
section
open List
example := @map
example := @head?
end
-- ANCHOR_END: fragments

-- ANCHOR: ProdSugar
example {α β : Type} : (
Prod α β
) = (
α × β
) := rfl
-- ANCHOR_END: ProdSugar

-- ANCHOR: SumSugar
example {α β : Type} : (
Sum α β
) = (
α ⊕ β
) := rfl
-- ANCHOR_END: SumSugar

-- ANCHOR: SumProd
section
variable (α β : Type)
example := α ⊕ β
example := α × β
end

-- ANCHOR_END: SumProd

namespace Ex
-- ANCHOR: RectangularPrism
structure RectangularPrism where
  -- Exercise

def volume : RectangularPrism → Float := fun _ => 0.0 -- Exercise

structure Segment where
  -- Exercise

def length : Segment → Float := fun _ => 0.0 -- Exercise

-- ANCHOR_END: RectangularPrism
