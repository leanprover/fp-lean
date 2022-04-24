import Examples.Support

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
end book declaration

bookExample {{{ helloNameVal }}}
  hello
  ===>
  "Hello"
end bookExample

book declaration {{{ lean }}}
  def lean : String := "Lean"
end book declaration

expect info {{{ helloLean }}}
  #eval String.append hello (String.append " " lean)
message
"\"Hello Lean\"
"
end expect

book declaration {{{ add1 }}}
  def add1 (n : Nat) : Nat := n + 1
end book declaration

expect info {{{ add1type }}}
  #check add1
message
"add1 : Nat → Nat"
end expect

expect info {{{ add1_7 }}}
  #eval add1 7
message
"8
"
end expect


book declaration {{{ maximum }}}
  def maximum (n : Nat) (k : Nat) : Nat :=
    if n < k then k else n
end book declaration

expect info {{{ maximumType }}}
  #check maximum
message
"maximum : Nat → Nat → Nat"
end expect

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
end book declaration

book declaration {{{ aStr }}}
  def aStr : Str := "This is a string."
end book declaration


book declaration {{{ NaturalNumberTypeDef }}}
  def NaturalNumber : Type := Nat
end book declaration

expect error {{{ thirtyEight }}}
  def thirtyEight : NaturalNumber := 38
message
"failed to synthesize instance
  OfNat NaturalNumber 38"
end expect

book declaration {{{ thirtyEightFixed }}}
  def thirtyEight : NaturalNumber := (38 : Nat)
end book declaration

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
end book declaration

book declaration {{{ origin }}}
  def origin : Point := { x := 0.0, y := 0.0 }
end book declaration

expect info {{{ originEval }}}
  #eval origin
message
"{ x := 0.000000, y := 0.000000 }
"
end expect

namespace Oops
book declaration {{{ Point }}}
  structure Point where
    x : Float
    y : Float
end book declaration

book declaration {{{ origin }}}
  def origin : Point := { x := 0.0, y := 0.0 }
end book declaration

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

expect info {{{ Pointmk }}}
  #check Point.mk
message
"Point.mk : Float → Float → Point"
end expect

expect info {{{ Pointx }}}
  #check Point.x
message
"Point.x : Point → Float"
end expect

expect info {{{ Pointy }}}
  #check Point.y
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
end book declaration

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
end book declaration

book declaration {{{ origin3D }}}
  def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }
end book declaration


namespace Ctor
book declaration {{{ PointCtorName }}}
  structure Point where
    point ::
    x : Float
    y : Float
  deriving Repr
end book declaration
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

book declaration {{{ distance }}}
  def distance (p1 : Point) (p2 : Point) : Float :=
    Float.sqrt ((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0)
end book declaration

book declaration {{{ Hamster }}}
  structure Hamster where
    name : String
    fluffy : Bool
end book declaration

book declaration {{{ Book }}}
  structure Book where
    title : String
    author : String
    price : Float
end book declaration

#check Prod
