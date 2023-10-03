import Examples.Support

set_option linter.unusedVariables false

bookExample {{{ three }}}
  1 + 2
  ===>
  3
end bookExample

expect info {{{ orderOfOperations }}}
  #eval 1 + 2 * 5
message
"11
"
end expect

expect info {{{ orderOfOperationsWrong }}}
  #eval (1 + 2) * 5
message
"15
"
end expect

expect info {{{ stringAppendHello }}}
  #eval String.append "Hello, " "Lean!"
message
"\"Hello, Lean!\"
"
end expect

expect info {{{ stringAppendNested }}}
  #eval String.append "great " (String.append "oak " "tree")
message
"\"great oak tree\"
"
end expect

evaluation steps {{{ stringAppend }}}
  String.append "it is " (if 1 > 2 then "yes" else "no")
  ===>
  String.append "it is " (if false then "yes" else "no")
  ===>
  String.append "it is " "no"
  ===>
  "it is no"
end evaluation steps

expect error {{{ stringAppendReprFunction }}}
  #eval String.append "it is "
message
"expression
  String.append \"it is \"
has type
  String → String
but instance
  Lean.MetaEval (String → String)
failed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `Lean.MetaEval` class"
end expect

expect info {{{ stringAppendCond }}}
  #eval 1 > 2
message
"false
"
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

bookExample {{{ oneMinusTwoInt }}}
  (1 - 2 : Int)
  ===>
  -1
end bookExample

expect info {{{ oneMinusTwoIntType }}}
  #check (1 - 2 : Int)
message
  "1 - 2 : Int"
end expect


expect error {{{ stringAppendList }}}
  #check String.append "hello" [" ", "world"]
message
"application type mismatch
  String.append \"hello\" [\" \", \"world\"]
argument
  [\" \", \"world\"]
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

book declaration {{{ maximum }}}
  def maximum (n : Nat) (k : Nat) : Nat :=
    if n < k then
      k
    else n
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
  #check String.append "Hello "
message
"String.append \"Hello \" : String → String"
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

evaluation steps {{{ joinStringsWithEx }}}
  joinStringsWith ", " "one" "and another"
  ===>
  "one, and another"
end evaluation steps


book declaration {{{ StringTypeDef }}}
  def Str : Type := String
stop book declaration

book declaration {{{ aStr }}}
  def aStr : Str := "This is a string."
stop book declaration


book declaration {{{ NaturalNumberTypeDef }}}
  def NaturalNumber : Type := Nat
stop book declaration

expect error {{{ thirtyEight }}}
  def thirtyEight : NaturalNumber := 38
message
"failed to synthesize instance
  OfNat NaturalNumber 38"
end expect

book declaration {{{ thirtyEightFixed }}}
  def thirtyEight : NaturalNumber := (38 : Nat)
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

expect error {{{ PointNoRepr }}}
  #eval origin
message
"expression
  origin
has type
  Point
but instance
  Lean.MetaEval Point
failed to be synthesized, this instance instructs Lean on how to display the resulting value, recall that any type implementing the `Repr` class also implements the `Lean.MetaEval` class"
end expect
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

book declaration {{{ addPoints }}}
  def addPoints (p1 : Point) (p2 : Point) : Point :=
    { x := p1.x + p2.x, y := p1.y + p2.y }
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

expect info {{{ modifyBothTest }}}
  #eval fourAndThree.modifyBoth Float.floor
message
  "{ x := 4.000000, y := 3.000000 }"
end expect

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


namespace Inductive

book declaration {{{ Bool }}}
  inductive Bool where
    | false : Bool
    | true : Bool
stop book declaration

book declaration {{{ Nat }}}
  inductive Nat where
    | zero : Nat
    | succ (n : Nat) : Nat
stop book declaration
end Inductive

evaluation steps {{{ four }}}
  Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
  ===>
  4
end evaluation steps

book declaration {{{ isZero }}}
  def isZero (n : Nat) : Bool :=
    match n with
    | Nat.zero => true
    | Nat.succ k => false
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
  "false
"
end expect

book declaration {{{ pred }}}
  def pred (n : Nat) : Nat :=
    match n with
    | Nat.zero => Nat.zero
    | Nat.succ k => k
stop book declaration

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

book declaration {{{ even }}}
  def even (n : Nat) : Bool :=
    match n with
    | Nat.zero => true
    | Nat.succ k => not (even k)
stop book declaration

expect info
  #eval even 2
message
"true
"
end expect

expect info
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
structural recursion cannot be used

well-founded recursion cannot be used, 'evenLoops' does not take any (non-fixed) arguments"
end expect

book declaration {{{ plus }}}
  def plus (n : Nat) (k : Nat) : Nat :=
    match k with
    | Nat.zero => n
    | Nat.succ k' => Nat.succ (plus n k')
stop book declaration

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

expect error {{{ div }}}
  def div (n : Nat) (k : Nat) : Nat :=
    if n < k then
      0
    else Nat.succ (div (n - k) k)
message
"fail to show termination for
  div
with errors
argument #1 was not used for structural recursion
  failed to eliminate recursive application
    div (n - k) k

argument #2 was not used for structural recursion
  failed to eliminate recursive application
    div (n - k) k

structural recursion cannot be used

failed to prove termination, use `termination_by` to specify a well-founded relation"
end expect


book declaration {{{ PPoint }}}
  structure PPoint (α : Type) where
    x : α
    y : α
  deriving Repr
stop book declaration

#check (Nat : Type)
#check (List String : Type)
#check (PPoint Int : Type)


book declaration {{{ natPoint }}}
  def natOrigin : PPoint Nat :=
    { x := Nat.zero, y := Nat.zero }
stop book declaration

book declaration {{{ toPPoint }}}
  def Point.toPPoint (p : Point) : PPoint Float :=
    { x := p.x, y := p.y }
stop book declaration

book declaration {{{ replaceX }}}
  def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
    { point with x := newX }
stop book declaration

expect info {{{ replaceXT }}}
  #check (replaceX)
message
  "replaceX : (α : Type) → PPoint α → α → PPoint α"
end expect

expect info {{{ replaceXNatT }}}
  #check replaceX Nat
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

namespace Oops
book declaration {{{ List }}}
  inductive List (α : Type) where
    | nil : List α
    | cons : α → List α → List α
stop book declaration

end Oops
similar datatypes List Oops.List


book declaration {{{ explicitPrimesUnder10 }}}
  def explicitPrimesUnder10 : List Nat :=
    List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))
stop book declaration

namespace Ooops
book declaration {{{ length1 }}}
  def length (α : Type) (xs : List α) : Nat :=
    match xs with
    | List.nil => Nat.zero
    | List.cons y ys => Nat.succ (length α ys)
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
book declaration {{{ replaceXImp }}}
  def replaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
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
    match xs with
    | [] => 0
    | y :: ys => Nat.succ (length ys)
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


book declaration {{{ Option }}}
  inductive Option (α : Type) : Type where
    | none : Option α
    | some (val : α) : Option α
stop book declaration



book declaration {{{ Prod }}}
  structure Prod (α : Type) (β : Type) : Type where
    fst : α
    snd : β
stop book declaration

-- Justify the claim in the text that Prod could be used instead of PPoint
theorem iso_Prod_PPoint {α : Type} : Iso (Prod α α) (PPoint α) := by
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

book declaration {{{ Unit }}}
  inductive Unit : Type where
    | unit : Unit
stop book declaration

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

book declaration {{{ animals }}}
  def animals : List PetName :=
    [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]
stop book declaration

book declaration {{{ howManyDogs }}}
  def howManyDogs (pets : List PetName) : Nat :=
    match pets with
    | [] => 0
    | Sum.inl _ :: morePets => howManyDogs morePets + 1
    | Sum.inr _ :: morePets => howManyDogs morePets
stop book declaration

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


book declaration {{{ ArithExpr }}}
  inductive ArithExpr (ann : Type) : Type where
    | int : ann → Int → ArithExpr ann
    | plus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
    | minus : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
    | times : ann → ArithExpr ann → ArithExpr ann → ArithExpr ann
stop book declaration

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


book declaration {{{ headHuh }}}
  def List.head? {α : Type} (xs : List α) : Option α :=
    match xs with
    | [] => none
    | y :: _ => some y
stop book declaration

expect info {{{ headSome }}}
  #eval primesUnder10.head?
message
"some 2
"
end expect

expect error {{{ headNoneBad }}}
  #eval [].head?
message
"don't know how to synthesize implicit argument
  @List.nil ?m.20264
context:
⊢ Type ?u.20261"
end expect

expect error {{{ headNoneBad2 }}}
  #eval [].head?
message
"don't know how to synthesize implicit argument
  @_root_.List.head? ?m.20264 []
context:
⊢ Type ?u.20261"
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


def Prod.swap {α β : Type} (pair : α × β) : β × α := (pair.snd, pair.fst)

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


book declaration {{{ posOrNegThree }}}
  def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
    match s with
    | Sign.pos => (3 : Nat)
    | Sign.neg => (-3 : Int)
stop book declaration

evaluation steps {{{ posOrNegThreePos }}}
  (posOrNegThree Sign.pos : match Sign.pos with | Sign.pos => Nat | Sign.neg => Int)
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
it must be smaller than or equal to the inductive datatype universe level
  1"
end expect


expect error {{{ Positivity }}}
  inductive MyType : Type where
    | ctor : (MyType → Int) → MyType
message
  "(kernel) arg #1 of 'MyType.ctor' has a non positive occurrence of the datatypes being declared"
end expect

#eval if let Option.some x := Option.some 5 then x else 55

expect error {{{ MissingTypeArg }}}
  inductive MyType (α : Type) : Type where
    | ctor : α → MyType
message
"type expected, got
  (MyType : Type → Type)"
end expect

book declaration {{{ MyTypeDef }}}
  inductive MyType (α : Type) : Type where
    | ctor : α → MyType α
stop book declaration

expect error {{{ MissingTypeArg2 }}}
  def ofFive : MyType := ctor 5
message
"type expected, got
  (MyType : Type → Type)"
end expect

-- Example solution
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  match xs with
  | [] => []
  | x :: xs' =>
    match ys with
    | [] => []
    | y :: ys' => (x, y) :: zip xs' ys'

namespace AutoImpl
book declaration {{{ lengthImpAuto }}}
  def length (xs : List α) : Nat :=
    match xs with
    | [] => 0
    | y :: ys => Nat.succ (length ys)
stop book declaration

end AutoImpl

namespace MatchDef
book declaration {{{ lengthMatchDef }}}
  def length : List α → Nat
    | [] => 0
    | y :: ys => Nat.succ (length ys)
stop book declaration
end MatchDef


book declaration {{{ drop }}}
  def drop : Nat → List α → List α
    | Nat.zero, xs => xs
    | _, [] => []
    | Nat.succ n, x :: xs => drop n xs
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
book declaration {{{ unzipBad }}}
  def unzip : List (α × β) → List α × List β
    | [] => ([], [])
    | (x, y) :: xys =>
      (x :: (unzip xys).fst, y :: (unzip xys).snd)
stop book declaration
end BadUnzip

book declaration {{{ unzip }}}
  def unzip : List (α × β) → List α × List β
    | [] => ([], [])
    | (x, y) :: xys =>
      let unzipped : List α × List β := unzip xys
      (x :: unzipped.fst, y :: unzipped.snd)
stop book declaration

book declaration {{{ reverse }}}
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
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
book declaration {{{ unzipNT }}}
  def unzip : List (α × β) → List α × List β
    | [] => ([], [])
    | (x, y) :: xys =>
      let unzipped := unzip xys
      (x :: unzipped.fst, y :: unzipped.snd)
stop book declaration


book declaration {{{ idA }}}
  def id (x : α) : α := x
stop book declaration

end NT

namespace NRT
book declaration {{{ unzipNRT }}}
  def unzip (pairs : List (α × β)) :=
    match pairs with
    | [] => ([], [])
    | (x, y) :: xys =>
      let unzipped := unzip xys
      (x :: unzipped.fst, y :: unzipped.snd)
stop book declaration

book declaration {{{ idB }}}
  def id (x : α) := x
stop book declaration

end NRT




namespace ReallyNoTypes

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
      let unzipped := unzip xys
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
book declaration {{{ dropMatch }}}
  def drop (n : Nat) (xs : List α) : List α :=
    match n, xs with
    | Nat.zero, ys => ys
    | _, [] => []
    | Nat.succ n , y :: ys => drop n ys
stop book declaration

book declaration {{{ evenFancy }}}
  def even : Nat → Bool
    | 0 => true
    | n + 1 => not (even n)
stop book declaration

namespace Explicit
book declaration {{{ explicitHalve }}}
  def halve : Nat → Nat
    | Nat.zero => 0
    | Nat.succ Nat.zero => 0
    | Nat.succ (Nat.succ n) => halve n + 1
stop book declaration
end Explicit


book declaration {{{ halve }}}
def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1
stop book declaration

example : Explicit.halve = halve := by rfl

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
  | Nat.succ n => some n : Nat → Option Nat"
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
"failed to synthesize instance
  ToString (Nat → Nat)"
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
"invalid constructor ⟨...⟩, expected type must be an inductive type \n  ?m.34991"
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
