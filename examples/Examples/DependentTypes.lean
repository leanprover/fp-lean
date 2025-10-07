import ExampleSupport

set_option linter.unusedVariables false

-- ANCHOR: natOrStringThree
def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"
-- ANCHOR_END: natOrStringThree


-- ANCHOR: Vect
inductive Vect (α : Type u) : Nat → Type u where
   | nil : Vect α 0
   | cons : α → Vect α n → Vect α (n + 1)
-- ANCHOR_END: Vect

deriving instance Repr for Vect

-- ANCHOR: vect3
example : Vect String 3 :=
  .cons "one" (.cons "two" (.cons "three" .nil))
-- ANCHOR_END: vect3

/--
error: Type mismatch
  Vect.nil
has type
  Vect ?m.3 0
but is expected to have type
  Vect String 3
-/
#check_msgs in
-- ANCHOR: nilNotLengthThree
example : Vect String 3 := Vect.nil
-- ANCHOR_END: nilNotLengthThree


/--
error: Type mismatch
  Vect.nil
has type
  Vect ?m.2 0
but is expected to have type
  Vect String n
-/
#check_msgs in
-- ANCHOR: nilNotLengthN
example : Vect String n := Vect.nil
-- ANCHOR_END: nilNotLengthN


/--
error: Type mismatch
  Vect.cons "Hello" (Vect.cons "world" Vect.nil)
has type
  Vect String (0 + 1 + 1)
but is expected to have type
  Vect String n
-/
#check_msgs in
-- ANCHOR: consNotLengthN
example : Vect String n := Vect.cons "Hello" (Vect.cons "world" Vect.nil)
-- ANCHOR_END: consNotLengthN

discarding
/-- error:
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
⊢ Vect α n
-/
#check_msgs in
-- ANCHOR: replicateStart
def Vect.replicate (n : Nat) (x : α) : Vect α n := _
-- ANCHOR_END: replicateStart
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α (k + 1)
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
⊢ Vect α 0
-/
#check_msgs in
-- ANCHOR: replicateMatchOne
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => _
  | k + 1 => _
-- ANCHOR_END: replicateMatchOne
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α (k + 1)
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
⊢ Vect α 0
-/
#check_msgs in
-- ANCHOR: replicateMatchTwo
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => _
  | k + 1 => _
-- ANCHOR_END: replicateMatchTwo
stop discarding

discarding
/-- error:
don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α (k + 1)
-/
#check_msgs in
-- ANCHOR: replicateMatchThree
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => _
-- ANCHOR_END: replicateMatchThree
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α k
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ α
-/
#check_msgs in
-- ANCHOR: replicateMatchFour
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons _ _
-- ANCHOR_END: replicateMatchFour
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α k
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ α
-/
#check_msgs in
-- ANCHOR: replicateMatchFive
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons _ _
-- ANCHOR_END: replicateMatchFive
stop discarding

discarding
/--
error: Application type mismatch: The argument
  cons x (replicate k x)
has type
  Vect α (k + 1)
but is expected to have type
  Vect α k
in the application
  cons x (cons x (replicate k x))
-/
#check_msgs in
-- ANCHOR: replicateOops
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (.cons x (replicate k x))
-- ANCHOR_END: replicateOops
stop discarding

-- ANCHOR: replicate
def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)
-- ANCHOR_END: replicate


namespace Extras
-- ANCHOR: listReplicate
def List.replicate (n : Nat) (x : α) : List α :=
  match n with
  | 0 => []
  | k + 1 => x :: x :: replicate k x
-- ANCHOR_END: listReplicate
end Extras

/-- info:
Vect.cons "hi" (Vect.cons "hi" (Vect.cons "hi" (Vect.nil)))
-/
#check_msgs in
-- ANCHOR: replicateHi
#eval Vect.replicate 3 "hi"
-- ANCHOR_END: replicateHi

-- ANCHOR: zip1
example : (
["Mount Hood",
 "Mount Jefferson",
 "South Sister"].zip ["Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"]
) = (
[("Mount Hood", "Møllehøj"),
 ("Mount Jefferson", "Yding Skovhøj"),
 ("South Sister", "Ejer Bavnehøj")]
) := rfl
-- ANCHOR_END: zip1

-- ANCHOR: zip2
example :
[3428.8, 3201, 3158.5, 3075, 3064].zip [170.86, 170.77, 170.35]
=
[(3428.8, 170.86), (3201, 170.77), (3158.5, 170.35)]
:= rfl
-- ANCHOR_END: zip2


-- ANCHOR: VectZip
def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
-- ANCHOR_END: VectZip

--ANCHOR: otherEx
example := Vect String 2
example := @Vect.nil
example := Except
example := Option
example := IO
example := Prop
example := Type 3
example := @List.zip
example := [1, 2, 3]
example := List String
example := 5
example := Nat.succ Nat.zero
--ANCHOR_END: otherEx

namespace Other


/--
error: Missing cases:
(List.cons _ _), []
[], (List.cons _ _)
-/
#check_msgs in
-- ANCHOR: zipMissing
def List.zip : List α → List β → List (α × β)
  | [], [] => []
  | x :: xs, y :: ys => (x, y) :: zip xs ys
-- ANCHOR_END: zipMissing

/--
error: Type mismatch
  Vect.cons y ys
has type
  Vect ?m.10 (?m.16 + 1)
but is expected to have type
  Vect β 0
-/
#check_msgs in
-- ANCHOR: zipExtraCons
def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
  | .nil, .nil => .nil
  | .nil, .cons y ys => .nil
  | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
-- ANCHOR_END: zipExtraCons
end Other

namespace Details

-- ANCHOR: VectZipLen
def Vect.zip : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n
  | 0, .nil, .nil => .nil
  | k + 1, .cons x xs, .cons y ys => .cons (x, y) (zip k xs ys)
-- ANCHOR_END: VectZipLen

end Details

-- ANCHOR: exerciseDefs
def oregonianPeaks : Vect String 3 :=
  .cons "Mount Hood" <|
  .cons "Mount Jefferson" <|
  .cons "South Sister" <| .nil

def danishPeaks : Vect String 3 :=
  .cons "Møllehøj" <|
  .cons "Yding Skovhøj" <|
  .cons "Ejer Bavnehøj" <| .nil

def Vect.map : (α → β) → Vect α n → Vect β n
  | f, .nil => .nil
  | f, .cons x xs => .cons (f x) (xs.map f)

def Vect.zipWith : (α → β → γ) → Vect α n → Vect β n → Vect γ n
  | f, .nil, .nil => .nil
  | f, .cons x xs, .cons y ys => .cons (f x y) (xs.zipWith f ys)

def Vect.unzip : Vect (α × β) n → Vect α n × Vect β n
  | .nil => (.nil, .nil)
  | .cons (x, y) xys =>
    let (xs, ys) := xys.unzip
    (.cons x xs, .cons y ys)


def Vect.push : Vect α n → α → Vect α (n + 1)
  | .nil, x => .cons x .nil
  | .cons y ys, x => .cons y (push ys x)

def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, xs => xs
  | n + 1, .cons x xs => xs.drop n

def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs => xs.reverse.push x

-- ANCHOR: take
def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, xs => .nil
  | n + 1, .cons x xs => .cons x (xs.take n)
-- ANCHOR_END: take

-- ANCHOR_END: exerciseDefs


/-- info:
Vect.cons
  ("Mount Hood", "Møllehøj")
  (Vect.cons ("Mount Jefferson", "Yding Skovhøj") (Vect.cons ("South Sister", "Ejer Bavnehøj") (Vect.nil)))
-/
#check_msgs in
-- ANCHOR: peaksVectZip
#eval oregonianPeaks.zip danishPeaks
-- ANCHOR_END: peaksVectZip




/-- info:
Vect.cons "snowy" (Vect.cons "peaks" (Vect.nil))
-/
#check_msgs in
-- ANCHOR: snocSnowy
#eval Vect.push (.cons "snowy" .nil) "peaks"
-- ANCHOR_END: snocSnowy


/-- info:
Vect.cons "Ejer Bavnehøj" (Vect.nil)
-/
#check_msgs in
-- ANCHOR: ejerBavnehoej
#eval danishPeaks.drop 2
-- ANCHOR_END: ejerBavnehoej
