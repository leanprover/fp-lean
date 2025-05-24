import ExampleSupport
import SubVerso.Examples

set_option linter.unusedVariables false

bookExample {{{ three }}}
  1 + 2
  ===>
  3
end bookExample

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


evaluation steps {{{ stringAppend }}}
  String.append "it is " (if 1 > 2 then "yes" else "no")
  ===>
  String.append "it is " (if false then "yes" else "no")
  ===>
  String.append "it is " "no"
  ===>
  "it is no"
end evaluation steps

/--
error: could not synthesize a 'ToExpr', 'Repr', or 'ToString' instance for type
  String → String
-/
#check_msgs in
-- ANCHOR: stringAppendReprFunction
#eval String.append "it is "
-- ANCHOR_END: stringAppendReprFunction

expect info {{{ stringAppendCond }}}
  #eval 1 > 2
message
"false
"
end expect

expect info {{{ onePlusTwoEval }}}
  #eval (1 + 2 : Nat)
message
"3"
end expect


bookExample {{{ onePlusTwoType }}}
  (1 + 2 : Nat)
  ===>
  3
end bookExample

bookExample {{{ oneMinusTwo }}}
  1 - 2
  ===>
  0
end bookExample

expect info {{{ oneMinusTwoEval }}}
  #eval (1 - 2 : Nat)
message
"0"
end expect


bookExample {{{ oneMinusTwoInt }}}
  (1 - 2 : Int)
  ===>
  -1
end bookExample

expect info {{{ oneMinusTwoIntEval }}}
  #eval (1 - 2 : Int)
message
"-1"
end expect


expect info {{{ oneMinusTwoIntType }}}
  #check (1 - 2 : Int)
message
  "1 - 2 : Int"
end expect


expect error {{{ stringAppendList }}}
  #check String.append ["hello", " "] "world"
message
"application type mismatch
  String.append [\"hello\", \" \"]
argument
  [\"hello\", \" \"]
has type
  List String : Type
but is expected to have type
  String : Type"
end expect


book declaration {{{ hello }}}
  def hello := "Hello"
stop book declaration

bookExample {{{ helloNameVal }}}
  hello
  ===>
  "Hello"
end bookExample

book declaration {{{ lean }}}
  def lean : String := "Lean"
stop book declaration

expect info {{{ helloLean }}}
  #eval String.append hello (String.append " " lean)
message
"\"Hello Lean\"
"
end expect

book declaration {{{ add1 }}}
  def add1 (n : Nat) : Nat := n + 1
stop book declaration

expect info {{{ add1sig }}}
  #check add1
message
"add1 (n : Nat) : Nat"
end expect


expect info {{{ add1type }}}
  #check (add1)
message
"add1 : Nat → Nat"
end expect

bookExample type {{{ add1typeASCII }}}
  add1
  ===>
  Nat -> Nat
end bookExample

expect info {{{ add1_7 }}}
  #eval add1 7
message
"8
"
end expect

expect error {{{ add1_string }}}
  #check add1 "seven"
message
"application type mismatch
  add1 \"seven\"
argument
  \"seven\"
has type
  String : Type
but is expected to have type
  Nat : Type"
end expect

expect warning {{{ add1_warn }}}
  def foo := add1 sorry
message
  "declaration uses 'sorry'"
end expect


section
open SubVerso.Examples

book declaration {{{ maximum }}}
def maximum (n : Nat) (k : Nat) : Nat :=
  if %ex{n}{n} < %ex{k}{k} then
    k
  else n
stop book declaration
end



book declaration {{{ spaceBetween }}}
def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)
stop book declaration

expect info {{{ maximumType }}}
  #check (maximum)
message
"maximum : Nat → Nat → Nat"
end expect

bookExample type {{{ maximumTypeASCII }}}
  maximum
  ===>
  Nat -> Nat -> Nat
end bookExample


expect info {{{ maximum3Type }}}
  #check maximum 3
message
"maximum 3 : Nat → Nat"
end expect

expect info {{{ stringAppendHelloType }}}
  #check spaceBetween "Hello "
message
"spaceBetween \"Hello \" : String → String"
end expect


evaluation steps {{{ maximum_eval }}}
  maximum (5 + 8) (2 * 7)
  ===>
  maximum 13 14
  ===>
  if 13 < 14 then 14 else 13
  ===>
  14
end evaluation steps

def joinStringsWith (sep x y : String) : String := String.append x (String.append sep y)

section
open SubVerso.Examples
%show_name joinStringsWith as joinStringsWith.name
%show_term joinStringsWith.type := String → String → String → String
end

open SubVerso.Examples in
book declaration {{{ volume }}}
  def volume : %ex{«type»}{Nat → Nat → Nat → Nat} :=
    fun x y z => x * y * z
stop book declaration
open SubVerso.Examples in
%show_name volume as volume.name

evaluation steps {{{ joinStringsWithEx }}}
  joinStringsWith ", " "one" "and another"
  ===>
  "one, and another"
end evaluation steps


book declaration {{{ StringTypeDef }}}
  def Str : Type := String
stop book declaration

open SubVerso.Examples in
%show_name Str as Str.name

book declaration {{{ aStr }}}
  def aStr : Str := "This is a string."
stop book declaration


book declaration {{{ NaturalNumberTypeDef }}}
  def NaturalNumber : Type := Nat
stop book declaration

open SubVerso.Examples in
%show_name NaturalNumber

open SubVerso.Examples in
expect error {{{ thirtyEight }}}
  def thirtyEight : NaturalNumber := %ex{val}{38}
message
"failed to synthesize
  OfNat NaturalNumber 38
numerals are polymorphic in Lean, but the numeral `38` cannot be used in a context where the expected type is
  NaturalNumber
due to the absence of the instance above

Additional diagnostic information may be available using the `set_option diagnostics true` command."
end expect

open SubVerso.Examples in
book declaration {{{ thirtyEightFixed }}}
  def thirtyEight : NaturalNumber := (%ex{val}{38} : Nat)
stop book declaration

book declaration {{{ NTypeDef }}}
  abbrev N : Type := Nat
stop book declaration

book declaration {{{ thirtyNine }}}
  def thirtyNine : N := 39
stop book declaration




evaluation steps {{{ NaturalNumberDef }}}
  NaturalNumber
  ===>
  Nat
end evaluation steps

expect info {{{ onePointTwo }}}
  #check 1.2
message
  "1.2 : Float"
end expect

expect info {{{ negativeLots }}}
  #check -454.2123215
message
  "-454.2123215 : Float"
end expect

expect info {{{ zeroPointZero }}}
  #check 0.0
message
  "0.0 : Float"
end expect

expect info {{{ zeroNat }}}
  #check 0
message
  "0 : Nat"
end expect

expect info {{{ zeroFloat }}}
  #check (0 : Float)
message
  "0 : Float"
end expect


book declaration {{{ Point }}}
  structure Point where
    x : Float
    y : Float
  deriving Repr
stop book declaration


section
open SubVerso.Examples
%show_name Point as Point.name
%show_name Repr as Repr.name
open Point
%show_name x as Point.x
%show_name y as Point.y

end

book declaration {{{ origin }}}
  def origin : Point := { x := 0.0, y := 0.0 }
stop book declaration

expect info {{{ originEval }}}
  #eval origin
message
"{ x := 0.000000, y := 0.000000 }
"
end expect

namespace Oops
  structure Point where
    x : Float
    y : Float

book declaration {{{ originNoRepr }}}
  def origin : Point := { x := 0.0, y := 0.0 }
stop book declaration

open SubVerso.Examples in
%show_name origin as origin.name

end Oops

expect error {{{ originNoType }}}
  #check { x := 0.0, y := 0.0 }
message
"invalid {...} notation, expected type is not known"
end expect

expect info {{{ originWithAnnot }}}
  #check ({ x := 0.0, y := 0.0 } : Point)
message
"{ x := 0.0, y := 0.0 } : Point"
end expect

expect info {{{ originWithAnnot2 }}}
  #check { x := 0.0, y := 0.0 : Point}
message
"{ x := 0.0, y := 0.0 } : Point"
end expect

namespace Oops
book declaration {{{ zeroXBad }}}
  def zeroX (p : Point) : Point :=
    { x := 0, y := p.y }
stop book declaration
end Oops

book declaration {{{ zeroX }}}
  def zeroX (p : Point) : Point :=
    { p with x := 0 }
stop book declaration

open SubVerso.Examples in
%show_name zeroX as zeroX.name
open SubVerso.Examples in
%show_term zeroPointZero.term := 0.0

book declaration {{{ fourAndThree }}}
  def fourAndThree : Point :=
    { x := 4.3, y := 3.4 }
stop book declaration



expect info {{{ fourAndThreeEval }}}
  #eval fourAndThree
message
"{ x := 4.300000, y := 3.400000 }
"
end expect

expect info {{{ zeroXFourAndThreeEval }}}
  #eval zeroX fourAndThree
message
"{ x := 0.000000, y := 3.400000 }
"
end expect

expect info {{{ Pointmk }}}
  #check (Point.mk)
message
"Point.mk : Float → Float → Point"
end expect

expect info {{{ Pointx }}}
  #check (Point.x)
message
"Point.x : Point → Float"
end expect

expect info {{{ Pointy }}}
  #check (Point.y)
message
"Point.y : Point → Float"
end expect

expect info {{{ originx1 }}}
  #eval Point.x origin
message
"0.000000
"
end expect

expect info {{{ originx }}}
  #eval origin.x
message
"0.000000
"
end expect

expect info {{{ originy }}}
  #eval origin.y
message
"0.000000
"
end expect

open SubVerso.Examples in
book declaration {{{ addPoints }}}
  def addPoints (p1 : Point) (p2 : Point) : Point :=
    { x := %ex{p1.x}{%ex{p1}{p1}.x} + %ex{p2}{p2}.x, y := p1.y + p2.y }
stop book declaration

expect info {{{ addPointsEx }}}
  #eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }
message
"{ x := -6.500000, y := 32.200000 }
"
end expect

book declaration {{{ Point3D }}}
  structure Point3D where
    x : Float
    y : Float
    z : Float
  deriving Repr
stop book declaration

book declaration {{{ origin3D }}}
  def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }
stop book declaration


namespace Ctor
book declaration {{{ PointCtorName }}}
  structure Point where
    point ::
    x : Float
    y : Float
  deriving Repr
stop book declaration
end Ctor

section
open SubVerso.Examples
open Ctor
%show_name Point.point
end

expect info {{{ checkPointMk }}}
  #check Point.mk 1.5 2.8
message
  "{ x := 1.5, y := 2.8 } : Point"
end expect

expect info {{{ stringAppendDot }}}
  #eval "one string".append " and another"
message
"\"one string and another\"
"
end expect


book declaration {{{ modifyBoth }}}
  def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
    { x := f p.x, y := f p.y }
stop book declaration

section
open SubVerso.Examples

%show_name Point.modifyBoth

open Point

%show_name modifyBoth as modifyBoth.name

end

expect info {{{ modifyBothTest }}}
  #eval fourAndThree.modifyBoth Float.floor
message
  "{ x := 4.000000, y := 3.000000 }"
end expect

open SubVerso.Examples in
%show_name Float.floor

book declaration {{{ distance }}}
  def distance (p1 : Point) (p2 : Point) : Float :=
    Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))
stop book declaration

expect info {{{ evalDistance }}}
  #eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }
message
"5.000000"
end expect


book declaration {{{ Hamster }}}
  structure Hamster where
    name : String
    fluffy : Bool
stop book declaration

book declaration {{{ Book }}}
  structure Book where
    makeBook ::
    title : String
    author : String
    price : Float
stop book declaration

set_option SubVerso.examples.suppressedNamespaces "Inductive Oops Ooops Oooops _root_ BetterPlicity StdLibNoUni BadUnzip NRT WithPattern MatchDef AutoImpl"

namespace Inductive

book declaration {{{ Bool }}}
  inductive Bool where
    | false : Bool
    | true : Bool
stop book declaration
attribute [inherit_doc _root_.Bool] Inductive.Bool
attribute [inherit_doc _root_.Bool.true] Inductive.Bool.true
attribute [inherit_doc _root_.Bool.false] Inductive.Bool.false

book declaration {{{ Nat }}}
  inductive Nat where
    | zero : Nat
    | succ (n : Nat) : Nat
stop book declaration
attribute [inherit_doc _root_.Nat] Inductive.Nat
attribute [inherit_doc _root_.Nat.zero] Inductive.Nat.zero
attribute [inherit_doc _root_.Nat.succ] Inductive.Nat.succ


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
  Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
  ===>
  4
end evaluation steps

end Inductive

open SubVerso.Examples in
book declaration {{{ isZero }}}
  def isZero (n : Nat) : Bool :=
    match %ex{n}{n} with
    | Nat.zero => true
    | Nat.succ %ex{k}{k} => false
stop book declaration

evaluation steps {{{ isZeroZeroSteps }}}
  isZero Nat.zero
  ===>
  match Nat.zero with
  | Nat.zero => true
  | Nat.succ k => false
  ===>
  true
end evaluation steps

expect info {{{ isZeroZero }}}
  #eval isZero 0
message
  "true
"
end expect

evaluation steps {{{ isZeroFiveSteps }}}
  isZero 5
  ===>
  isZero (Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))))
  ===>
  match Nat.succ (Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))) with
  | Nat.zero => true
  | Nat.succ k => false
  ===>
  false
end evaluation steps


expect info {{{ isZeroFive }}}
  #eval isZero 5
message
  "false"
end expect

open SubVerso.Examples in
book declaration {{{ pred }}}
  def pred (n : Nat) : Nat :=
    match n with
    | Nat.zero => Nat.zero
    | Nat.succ k => %ex{k}{k}
stop book declaration

open SubVerso.Examples in
%show_name pred as pred.name

expect info {{{ predFive }}}
  #eval pred 5
message
"4
"
end expect


evaluation steps {{{ predFiveSteps }}}
  pred 5
  ===>
  pred (Nat.succ 4)
  ===>
  match Nat.succ 4 with
  | Nat.zero => Nat.zero
  | Nat.succ k => k
  ===>
  4
end evaluation steps

expect info {{{ predBig }}}
  #eval pred 839
message
"838
"
end expect

expect info {{{ predZero }}}
  #eval pred 0
message
"0
"
end expect


book declaration {{{ depth }}}
  def depth (p : Point3D) : Float :=
    match p with
    | { x:= h, y := w, z := d } => d
stop book declaration

open SubVerso.Examples in
book declaration {{{ even }}}
  def even (n : Nat) : Bool :=
    match n with
    | Nat.zero => true
    | Nat.succ k => not (%ex{name}{even} k)
stop book declaration

expect info {{{ _something }}}
  #eval even 2
message
"true
"
end expect

expect info {{{ _something }}}
  #eval even 5
message
"false
"
end expect


expect error {{{ evenLoops }}}
  def evenLoops (n : Nat) : Bool :=
    match n with
    | Nat.zero => true
    | Nat.succ k => not (evenLoops n)
message
"fail to show termination for
  evenLoops
with errors
failed to infer structural recursion:
Not considering parameter n of evenLoops:
  it is unchanged in the recursive calls
no parameters suitable for structural recursion

well-founded recursion cannot be used, 'evenLoops' does not take any (non-fixed) arguments"
end expect

open SubVerso.Examples in
book declaration {{{ plus }}}
  def plus (n : Nat) (k : Nat) : Nat :=
    match %ex{k}{k} with
    | Nat.zero => n
    | Nat.succ %ex{k'}{k'} => Nat.succ (plus n k')
stop book declaration

open SubVerso.Examples in
%show_name plus as plus.name

evaluation steps {{{ plusThreeTwo }}}
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
end evaluation steps

book declaration {{{ times }}}
  def times (n : Nat) (k : Nat) : Nat :=
    match k with
    | Nat.zero => Nat.zero
    | Nat.succ k' => plus n (times n k')
stop book declaration

#eval times 5 3

book declaration {{{ minus }}}
  def minus (n : Nat) (k : Nat) : Nat :=
    match k with
    | Nat.zero => n
    | Nat.succ k' => pred (minus n k')
stop book declaration

open SubVerso.Examples in
expect error {{{ div }}}
  def div (n : Nat) (k : Nat) : Nat :=
    if n < k then
      0
    else Nat.succ (%ex{name}{div} (n - k) k)
message
"fail to show termination for
  div
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    div (n - k) k
Cannot use parameter k:
  failed to eliminate recursive application
    div (n - k) k


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
             n k
1) 736:29-43 ≤ =
Please use `termination_by` to specify a decreasing measure."
end expect


open SubVerso.Examples in
book declaration {{{ PPoint }}}
  structure PPoint (α : Type) where
    x : %ex{α}{α}
    y : α
  deriving Repr
stop book declaration


section
open SubVerso.Examples
%show_name PPoint as PPoint.name
open PPoint
%show_name x as PPoint.x
%show_name y as PPoint.y
end


book declaration {{{ natPoint }}}
  def natOrigin : PPoint Nat :=
    { x := Nat.zero, y := Nat.zero }
stop book declaration

section
open SubVerso.Examples
%show_name natOrigin as natOrigin.name
end



book declaration {{{ toPPoint }}}
  def Point.toPPoint (p : Point) : PPoint Float :=
    { x := p.x, y := p.y }
stop book declaration

open SubVerso.Examples in
book declaration {{{ replaceX }}}
  def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint %ex{α}{α} :=
    { %ex{point}{point} with x := %ex{newX}{newX} }
stop book declaration

expect info {{{ replaceXT }}}
  #check (replaceX)
message
  "replaceX : (α : Type) → PPoint α → α → PPoint α"
end expect

open SubVerso.Examples in
expect info {{{ replaceXNatT }}}
  #check %ex{term}{replaceX Nat}
message
  "replaceX Nat : PPoint Nat → Nat → PPoint Nat"
end expect

expect info {{{ replaceXNatOriginT }}}
  #check replaceX Nat natOrigin
message
  "replaceX Nat natOrigin : Nat → PPoint Nat"
end expect

expect info {{{ replaceXNatOriginFiveT }}}
  #check replaceX Nat natOrigin 5
message
  "replaceX Nat natOrigin 5 : PPoint Nat"
end expect

expect info {{{ replaceXNatOriginFiveV }}}
  #eval replaceX Nat natOrigin 5
message
"{ x := 5, y := 0 }
"
end expect

book declaration {{{ primesUnder10 }}}
  def primesUnder10 : List Nat := [2, 3, 5, 7]
stop book declaration

open SubVerso.Examples in
%show_name primesUnder10 as primesUnder10.name

namespace Oops
open SubVerso.Examples

book declaration {{{ List }}}
  inductive List (α : Type) where
    | nil : List α
    | cons : α → %ex{rec}{List α} → List α
stop book declaration

%show_term fakeList : Type → Type := List

open List

%show_term fakeNil : {α : Type} → Oops.List α := nil
%show_term fakeCons : {α : Type} → α → Oops.List α → Oops.List α := cons

end Oops
similar datatypes List Oops.List


book declaration {{{ explicitPrimesUnder10 }}}
  def explicitPrimesUnder10 : List Nat :=
    List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))
stop book declaration

open SubVerso.Examples in
%show_name explicitPrimesUnder10 as explicitPrimesUnder10.name

namespace Ooops
open SubVerso.Examples

book declaration {{{ length1 }}}
  def length (α : Type) (xs : List α) : Nat :=
    match xs with
    | List.nil => Nat.zero
    | List.cons y ys => Nat.succ (%ex{name}{length} α ys)
stop book declaration


evaluation steps {{{ length1EvalSummary }}}
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
end evaluation steps

evaluation steps {{{ length1Eval }}}
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
end evaluation steps
end Ooops



namespace Oooops
book declaration {{{ length2 }}}
  def length (α : Type) (xs : List α) : Nat :=
    match xs with
    | [] => 0
    | y :: ys => Nat.succ (length α ys)
stop book declaration
end Oooops


namespace BetterPlicity
open SubVerso.Examples
book declaration {{{ replaceXImp }}}
  def replaceX {α : Type} (point : PPoint %ex{α}{α}) (newX : α) : PPoint α :=
    { point with x := newX }
stop book declaration

expect info {{{ replaceXImpNat }}}
  #eval replaceX natOrigin 5
message
"{ x := 5, y := 0 }
"
end expect


book declaration {{{ lengthImp }}}
  def length {α : Type} (xs : List α) : Nat :=
    match %ex{xs}{xs} with
    | [] => 0
    | y :: ys => Nat.succ (%ex{name}{length} ys)
stop book declaration

expect info {{{ lengthImpPrimes }}}
  #eval length primesUnder10
message
"4
"
end expect
end BetterPlicity

expect info {{{ lengthDotPrimes }}}
  #eval primesUnder10.length
message
"4
"
end expect

expect info {{{ lengthExpNat }}}
  #check List.length (α := Int)
message
  "List.length : List Int → Nat"
end expect

def x := Unit

structure Iso (α : Type u) (β : Type u) : Type u where
  into : α → β
  outOf : β → α
  comp1 : into ∘ outOf = id
  comp2 : outOf ∘ into = id


-- Standard library copies without universe parameters
namespace StdLibNoUni
open SubVerso.Examples

book declaration {{{ Option }}}
  inductive Option (α : Type) : Type where
    | none : Option α
    | some (val : α) : Option α
stop book declaration

%show_name Option as fakeOption
%show_name Option.none as fakeOption.none
%show_name Option.some as fakeOption.some
namespace Option
%show_name none as fakeNone
%show_name some as fakeSome
end Option

book declaration {{{ Prod }}}
  structure Prod (α : Type) (β : Type) : Type where
    fst : α
    snd : β
stop book declaration

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



book declaration {{{ Sum }}}
  inductive Sum (α : Type) (β : Type) : Type where
    | inl : α → Sum α β
    | inr : β → Sum α β
stop book declaration

%show_term Sumαβ := {α β : Type} → %ex{ex}{Sum %ex{α}{α} %ex{β}{β}} → %ex{sugar}{α ⊕ β}

%show_name Sum as fakeSum
%show_name Sum.inl as fakeSum.inl
%show_name Sum.inr as fakeSum.inr
namespace Sum
%show_name inl as fakeInl
%show_name inr as fakeInr
end Sum


book declaration {{{ Unit }}}
  inductive Unit : Type where
    | unit : Unit
stop book declaration

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

book declaration {{{ PetName }}}
  def PetName : Type := String ⊕ String
stop book declaration

open SubVerso.Examples in
%show_name PetName as PetName.name

book declaration {{{ animals }}}
  def animals : List PetName :=
    [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi",
     Sum.inl "Rex", Sum.inr "Floof"]
stop book declaration

book declaration {{{ howManyDogs }}}
  def howManyDogs (pets : List PetName) : Nat :=
    match pets with
    | [] => 0
    | Sum.inl _ :: morePets => howManyDogs morePets + 1
    | Sum.inr _ :: morePets => howManyDogs morePets
stop book declaration

section
variable (morePets : List PetName)

bookExample {{{ howManyDogsAdd }}}
  howManyDogs morePets + 1
  ===>
  (howManyDogs morePets) + 1
end bookExample
end

expect info {{{ dogCount }}}
  #eval howManyDogs animals
message
"3
"
end expect

bookExample type {{{ unitParens }}}
  ()
  ===>
  Unit
end bookExample


open SubVerso.Examples in
book declaration {{{ ArithExpr }}}
  inductive ArithExpr (ann : Type) : Type where
    | int : ann → Int → ArithExpr %ex{ann}{ann}
    | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
    | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
    | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
stop book declaration

section
open SubVerso.Examples
structure SourcePos where
  line : Nat
  column : Nat

%show_term «ArithExpr SourcePos» := ArithExpr SourcePos
%show_term «ArithExpr Unit» := ArithExpr Unit
%show_name SourcePos as SourcePos.name

end

bookExample type {{{ nullOne }}}
  none
  ===>
  Option (Option Int)
end bookExample

bookExample type {{{ nullTwo }}}
  some none
  ===>
  Option (Option Int)
end bookExample

bookExample type {{{ nullThree }}}
  some (some 360)
  <===
  Option (Option Int)
end bookExample


namespace Floop
open SubVerso.Examples

book declaration {{{ headHuh }}}
  def List.head? {α : Type} (xs : List α) : Option α :=
    match xs with
    | [] => none
    | y :: _ => some y
stop book declaration

%show_name List.head? as fakeHead?

expect info {{{ headSome }}}
  #eval primesUnder10.head?
message
"some 2
"
end expect

expect error {{{ headNoneBad }}}
  #eval [].head?
message
"don't know how to synthesize implicit argument 'α'
  @List.nil ?m.18195
context:
⊢ Type ?u.18192"
end expect

expect error {{{ headNoneBad2 }}}
  #eval [].head?
message
"don't know how to synthesize implicit argument 'α'
  @_root_.List.head? ?m.18195 []
context:
⊢ Type ?u.18192"
end expect


expect info {{{ headNone }}}
  #eval [].head? (α := Int)
message
"none
"
end expect

expect info {{{ headNoneTwo }}}
  #eval ([] : List Int).head?
message
"none"
end expect






def List.final? {α : Type} (xs : List α) : Option α :=
  match xs with
  | [] => none
  | [y] => some y
  | y1 :: y2 :: ys => final? (y2::ys)


end Floop

open SubVerso.Examples in
%show_term αxβ := (α β : Type) → %ex{desugar}{Prod α β} → %ex{sugar}{α × β}


namespace StructNotation
book declaration {{{ fivesStruct }}}
  def fives : String × Int := { fst := "five", snd := 5 }
stop book declaration
end StructNotation

book declaration {{{ fives }}}
  def fives : String × Int := ("five", 5)
stop book declaration

example : StructNotation.fives = fives := by rfl


namespace Nested
book declaration {{{ sevensNested }}}
  def sevens : String × (Int × Nat) := ("VII", (7, 4 + 3))
stop book declaration
end Nested

book declaration {{{ sevens }}}
  def sevens : String × Int × Nat := ("VII", 7, 4 + 3)
stop book declaration

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


book declaration {{{ Sign }}}
  inductive Sign where
    | pos
    | neg
stop book declaration

open SubVerso.Examples in
book declaration {{{ posOrNegThree }}}
  def posOrNegThree (s : Sign) :
      match %ex{s}{s} with | Sign.pos => Nat | Sign.neg => Int :=
    match s with
    | Sign.pos => (3 : Nat)
    | Sign.neg => (-3 : Int)
stop book declaration


section
open SubVerso.Examples
%show_name posOrNegThree as posOrNegThree.name
%show_name Sign.pos as Sign.pos.name
%show_name Sign.neg as Sign.neg.name
open Sign
%show_name pos as pos.name
%show_name neg as neg.name
end

evaluation steps {{{ posOrNegThreePos }}}
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
end evaluation steps



def take (n : Nat) (xs : List α) : List α :=
  match n, xs with
  | _, [] => []
  | Nat.zero, _ => []
  | Nat.succ n', x :: xs => x :: take n' xs



expect info {{{ takeThree }}}
  #eval take 3 ["bolete", "oyster"]
message
"[\"bolete\", \"oyster\"]
"
end expect

expect info {{{ takeOne }}}
  #eval take 1 ["bolete", "oyster"]
message
"[\"bolete\"]
"
end expect


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


expect error {{{ TypeInType }}}
  inductive MyType : Type where
    | ctor : (α : Type) → α → MyType
message
"invalid universe level in constructor 'MyType.ctor', parameter 'α' has type
  Type
at universe level
  2
which is not less than or equal to the inductive type's resulting universe level
  1"
end expect


expect error {{{ Positivity }}}
  inductive MyType : Type where
    | ctor : (MyType → Int) → MyType
message
  "(kernel) arg #1 of 'MyType.ctor' has a non positive occurrence of the datatypes being declared"
end expect

#eval if let Option.some x := Option.some 5 then x else 55

section
open SubVerso.Examples

expect error {{{ MissingTypeArg }}}
  inductive MyType (α : Type) : Type where
    | ctor : %ex{α}{α} → MyType
message
"type expected, got
  (MyType : Type → Type)"
end expect

book declaration {{{ MyTypeDef }}}
  inductive MyType (α : Type) : Type where
    | ctor : α → MyType %ex{α}{α}
stop book declaration

%show_name MyType as MyType.name
section
open MyType
%show_name ctor as MyType.ctor.name
end

expect error {{{ MissingTypeArg2 }}}
  def ofFive : MyType := ctor 5
message
"type expected, got
  (MyType : Type → Type)"
end expect

end

-- Example solution
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | [] => []
  | x :: xs' =>
    match ys with
    | [] => []
    | y :: ys' => (x, y) :: zip xs' ys'

open SubVerso.Examples in
expect error {{{ sameLengthPair }}}
  def sameLength (xs : List α) (ys : List β) : Bool :=
    match (%ex{xs}{xs}, ys) with
    | ([], []) => true
    | (%ex{x_xs}{x :: xs'}, y :: ys') => %ex{name}{sameLength} xs' ys'
    | _ => false
message
"fail to show termination for
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
1) 1298:51-70  ?  ?
Please use `termination_by` to specify a decreasing measure."
end expect

namespace Nested
book declaration {{{ sameLengthOk1 }}}
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
stop book declaration
end Nested

namespace Both
book declaration {{{ sameLengthOk2 }}}
  def sameLength (xs : List α) (ys : List β) : Bool :=
    match xs, ys with
    | [], [] => true
    | x :: xs', y :: ys' => sameLength xs' ys'
    | _, _ => false
stop book declaration
end Both

namespace AutoImpl
book declaration {{{ lengthImpAuto }}}
  def length (xs : List α) : Nat :=
    match xs with
    | [] => 0
    | y :: ys => Nat.succ (length ys)
stop book declaration

end AutoImpl

namespace MatchDef
open SubVerso.Examples

book declaration {{{ lengthMatchDef }}}
  def length : %ex{rtype}{List α → Nat}
    | [] => 0
    | y :: ys => Nat.succ (%ex{name}{length} ys)
stop book declaration
end MatchDef

open SubVerso.Examples in
book declaration {{{ drop }}}
  def drop : Nat → List α → List α
    | Nat.zero, xs => xs
    | _, [] => []
    | Nat.succ n, x :: xs => %ex{name}{drop} n xs
stop book declaration



book declaration {{{ fromOption }}}
  def fromOption (default : α) : Option α → α
    | none => default
    | some x => x
stop book declaration


expect info {{{ getD }}}
  #eval (some "salmonberry").getD ""
message
"\"salmonberry\"
"
end expect

expect info {{{ getDNone }}}
  #eval none.getD ""
message
"\"\"
"
end expect


namespace BadUnzip
open SubVerso.Examples

book declaration {{{ unzipBad }}}
  def unzip : List (α × β) → List α × List β
    | [] => ([], [])
    | (x, y) :: xys =>
      (x :: (unzip xys).fst, y :: (unzip xys).snd)
stop book declaration

%show_name unzip as unzipBad.name
end BadUnzip

book declaration {{{ unzip }}}
  def unzip : List (α × β) → List α × List β
    | [] => ([], [])
    | (x, y) :: xys =>
      let unzipped : List α × List β := unzip xys
      (x :: unzipped.fst, y :: unzipped.snd)
stop book declaration

open SubVerso.Examples in
%show_name unzip as unzip.name

open SubVerso.Examples in
book declaration {{{ reverse }}}
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => %ex{soFar}{soFar}
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []
stop book declaration

namespace WithPattern
book declaration {{{ unzipPat }}}
  def unzip : List (α × β) → List α × List β
    | [] => ([], [])
    | (x, y) :: xys =>
      let (xs, ys) : List α × List β := unzip xys
      (x :: xs, y :: ys)
stop book declaration
end WithPattern

namespace NT
open SubVerso.Examples
book declaration {{{ unzipNT }}}
  def unzip : List (α × β) → List α × List β
    | [] => ([], [])
    | (x, y) :: xys =>
      let unzipped := %ex{name}{unzip} xys
      (x :: %ex{unzipped}{unzipped}.fst, y :: unzipped.snd)
stop book declaration


book declaration {{{ idA }}}
  def id (x : α) : α := x
stop book declaration

end NT

namespace NRT
open SubVerso.Examples
book declaration {{{ unzipNRT }}}
  def unzip (pairs : List (α × β)) :=
    match pairs with
    | [] => ([], [])
    | (x, y) :: xys =>
      let unzipped := %ex{name}{unzip} xys
      (x :: unzipped.fst, y :: unzipped.snd)
stop book declaration

book declaration {{{ idB }}}
  def id (x : α) := x
stop book declaration

end NRT




namespace ReallyNoTypes
open SubVerso.Examples

expect error {{{ identNoTypes }}}
  def id x := x
message
"failed to infer binder type"
end expect

expect error {{{ unzipNoTypesAtAll }}}
  def unzip pairs :=
    match pairs with
    | [] => ([], [])
    | (x, y) :: xys =>
      let unzipped := %ex{name}{unzip} xys
      (x :: unzipped.fst, y :: unzipped.snd)
message
"invalid match-expression, pattern contains metavariables
  []"
end expect
end ReallyNoTypes


expect info {{{ fourteenNat }}}
  #check 14
message
"14 : Nat"
end expect

expect info {{{ fourteenInt }}}
  #check (14 : Int)
message
"14 : Int"
end expect

namespace Match
open SubVerso.Examples
book declaration {{{ dropMatch }}}
  def drop (n : Nat) (xs : List α) : List α :=
    match n, xs with
    | Nat.zero, ys => ys
    | _, [] => []
    | Nat.succ n , y :: ys => %ex{name}{drop} n ys
stop book declaration

book declaration {{{ evenFancy }}}
  def even : Nat → Bool
    | 0 => true
    | n + %ex{one}{1} => not (%ex{name}{even} %ex{n}{n})
stop book declaration

namespace Explicit
book declaration {{{ explicitHalve }}}
  def halve : Nat → Nat
    | Nat.zero => 0
    | Nat.succ Nat.zero => 0
    | Nat.succ (Nat.succ n) => %ex{name}{halve} n + 1
stop book declaration
end Explicit


book declaration {{{ halve }}}
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => %ex{recur}{halve n + 1}
stop book declaration

%show_term halveParens := fun n => [%ex{one}{(halve n) + 1}, %ex{two}{halve (n + 1)}]

example : Explicit.halve = halve := by
  funext x
  fun_induction halve x <;> simp [halve, Explicit.halve, *]

namespace Oops
expect error {{{ halveFlippedPat }}}
  def halve : Nat → Nat
    | 0 => 0
    | 1 => 0
    | 2 + n => halve n + 1
message
"invalid patterns, `n` is an explicit pattern variable, but it only occurs in positions that are inaccessible to pattern matching
  .(Nat.add 2 n)"
end expect
end Oops

end Match


evaluation steps {{{ incrSteps }}}
  fun x => x + 1
  ===>
  (· + 1)
  ===>
  Nat.succ
end evaluation steps

expect info {{{ incr }}}
  #check fun x => x + 1
message
  "fun x => x + 1 : Nat → Nat"
end expect

expect info {{{ incrInt }}}
  #check fun (x : Int) => x + 1
message
  "fun x => x + 1 : Int → Int"
end expect

expect info {{{ identLambda }}}
  #check fun {α : Type} (x : α) => x
message
  "fun {α} x => x : {α : Type} → α → α"
end expect

expect info {{{ predHuh }}}
  #check fun
    | 0 => none
    | n + 1 => some n
message
"fun x =>
  match x with
  | 0 => none
  | n.succ => some n : Nat → Option Nat"
end expect

namespace Double
book declaration {{{ doubleLambda }}}
  def double : Nat → Nat := fun
    | 0 => 0
    | k + 1 => double k + 2
stop book declaration
end Double

evaluation steps {{{ funPair }}}
  (· + 5, 3)
end evaluation steps

evaluation steps {{{ pairFun }}}
  ((· + 5), 3)
end evaluation steps


evaluation steps {{{ twoDots }}}
  (· , ·) 1 2
  ===>
  (1, ·) 2
  ===>
  (1, 2)
end evaluation steps


expect info {{{ applyLambda }}}
  #eval (fun x => x + x) 5
message
"10
"
end expect


expect info {{{ applyCdot }}}
  #eval (· * 2) 5
message
"10
"
end expect

book declaration {{{ NatDouble }}}
  def Nat.double (x : Nat) : Nat := x + x
stop book declaration

open SubVerso.Examples in
%show_name Nat.double as Nat.double.name
section
open SubVerso.Examples
open Nat
%show_name double as double.name

end



expect info {{{ NatDoubleFour }}}
  #eval (4 : Nat).double
message
"8
"
end expect

book declaration {{{ NewNamespace }}}
  namespace NewNamespace
  def triple (x : Nat) : Nat := 3 * x
  def quadruple (x : Nat) : Nat := 2 * x + 2 * x
  end NewNamespace
stop book declaration

section
open SubVerso.Examples
open NewNamespace
%show_name triple
%show_name quadruple
end


expect info {{{ tripleNamespace }}}
  #check NewNamespace.triple
message
  "NewNamespace.triple (x : Nat) : Nat"
end expect

expect info {{{ quadrupleNamespace }}}
  #check NewNamespace.quadruple
message
  "NewNamespace.quadruple (x : Nat) : Nat"
end expect


book declaration {{{ quadrupleOpenDef }}}
  def timesTwelve (x : Nat) :=
    open NewNamespace in
    quadruple (triple x)
stop book declaration

open SubVerso.Examples in
%show_name timesTwelve

example : timesTwelve 2 = 24 := by rfl

expect info {{{ quadrupleNamespaceOpen }}}
  open NewNamespace in
  #check quadruple
message
  "NewNamespace.quadruple (x : Nat) : Nat"
end expect



expect info {{{ interpolation }}}
  #eval s!"three fives is {NewNamespace.triple 5}"
message
"\"three fives is 15\"
"
end expect

expect error {{{ interpolationOops }}}
  #check s!"three fives is {NewNamespace.triple}"
message
"failed to synthesize
  ToString (Nat → Nat)

Additional diagnostic information may be available using the `set_option diagnostics true` command."
end expect


book declaration {{{ Inline }}}
  inductive Inline : Type where
    | lineBreak
    | string : String → Inline
    | emph : Inline → Inline
    | strong : Inline → Inline
stop book declaration

namespace WithMatch
book declaration {{{ inlineStringHuhMatch }}}
  def Inline.string? (inline : Inline) : Option String :=
    match inline with
    | Inline.string s => some s
    | _ => none
stop book declaration
end WithMatch



book declaration {{{ inlineStringHuh }}}
  def Inline.string? (inline : Inline) : Option String :=
    if let Inline.string s := inline then
      some s
    else none
stop book declaration

example : WithMatch.Inline.string? = Inline.string? := by rfl

bookExample : Point {{{ pointCtor }}}
  Point.mk 1 2
  ===>
  { x := 1, y := 2 }
end bookExample

bookExample : Point {{{ pointBraces }}}
  { x := 1, y := 2 }
  ===>
  Point.mk 1 2
end bookExample

bookExample : Point {{{ pointPos }}}
  ⟨1, 2⟩
  ===>
  Point.mk 1 2
end bookExample


expect error {{{ pointPosEvalNoType }}}
  #eval ⟨1, 2⟩
message
"invalid constructor ⟨...⟩, expected type must be an inductive type
  ?m.29916"
end expect

expect info {{{ pointPosWithType }}}
  #eval (⟨1, 2⟩ : Point)
message
"{ x := 1.000000, y := 2.000000 }
"
end expect


bookExample type {{{ swapLambda }}}
  fun (point : Point) => { x := point.y, y := point.x : Point }
  ===>
  (Point → Point)
end bookExample

bookExample : Int → Int {{{ subOneDots }}}
  (· - 1)
  ===>
  fun x => x - 1
end bookExample

open SubVerso.Examples

section
%show_term sizes := (α β : Type) → %ex{α}{α} → %ex{β}{β} → %ex{sum}{α ⊕ β} → %ex{prod}{α × β}
%show_term «Bool × Unit» := Bool × Unit
%show_term BoolxUnit.vals : List (Bool × Unit) := [%ex{one}{(true, Unit.unit)}, %ex{two}{(false, Unit.unit)}]
%show_term «Bool ⊕ Unit» := Bool ⊕ Unit
%show_term BooloUnit.vals : List (Bool ⊕ Unit) := [%ex{one}{Sum.inl true}, %ex{two}{Sum.inl false}, %ex{three}{Sum.inr Unit.unit}]
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

%show_term distr := (α β γ : Type) → %ex{one}{α × (β ⊕ γ) → (α × β) ⊕ (α × γ)} → %ex{two}{Bool × α → α ⊕ α}

end

bookExample type {{{ α }}}
  ({α : Type} → %ex{name}{α} → Nat : Type 1)
  ===>
  Type 1
end bookExample

namespace Oops
axiom mySorry : α
scoped macro "…" : term => `(mySorry)

noncomputable section

book declaration {{{ List.findFirst?Ex }}}
def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α := …
stop book declaration
%show_name List.findFirst?

book declaration {{{ Prod.switchEx }}}
def Prod.switch {α β : Type} (pair : α × β) : β × α := …
stop book declaration
%show_name Prod.switch

book declaration {{{ zipEx }}}
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) := …
stop book declaration
%show_name zip

end
end Oops
