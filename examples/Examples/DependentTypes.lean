import Examples.Support


book declaration {{{ natOrStringThree }}}
  def natOrStringThree (b : Bool) : if b then Nat else String :=
    match b with
    | true => (3 : Nat)
    | false => "three"
stop book declaration


book declaration {{{ Vect }}}
 inductive Vect (α : Type u) : Nat → Type u where
    | nil : Vect α 0
    | cons : α → Vect α n → Vect α (n + 1)
stop book declaration

deriving instance Repr for Vect

expect error {{{ nilNotLengthThree }}}
  example : Vect String 3 := Vect.nil
message
"type mismatch
  Vect.nil
has type
  Vect String 0 : Type
but is expected to have type
  Vect String 3 : Type"
end expect


expect error {{{ nilNotLengthN }}}
  example : Vect String n := Vect.nil
message
"type mismatch
  Vect.nil
has type
  Vect String 0 : Type
but is expected to have type
  Vect String n : Type"
end expect


expect error {{{ consNotLengthN }}}
  example : Vect String n := Vect.cons "Hello" (Vect.cons "world" Vect.nil)
message
"type mismatch
  Vect.cons \"Hello\" (Vect.cons \"world\" Vect.nil)
has type
  Vect String (0 + 1 + 1) : Type
but is expected to have type
  Vect String n : Type"
end expect

expect error {{{ replicateStart }}}
  def Vect.replicate (n : Nat) (x : α) : Vect α n := _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
⊢ Vect α n"
end expect


expect error {{{ replicateMatchOne }}}
  def Vect.replicate (n : Nat) (x : α) : Vect α n :=
    match n with
    | 0 => _
    | k + 1 => _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
⊢ Vect α 0"
end expect


expect error {{{ replicateMatchTwo }}}
  def Vect.replicate (n : Nat) (x : α) : Vect α n :=
    match n with
    | 0 => _
    | k + 1 => _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α (k + 1)"
end expect

expect error {{{ replicateMatchThree }}}
  def Vect.replicate (n : Nat) (x : α) : Vect α n :=
    match n with
    | 0 => .nil
    | k + 1 => _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α (k + 1)"
end expect

expect error {{{ replicateMatchFour }}}
  def Vect.replicate (n : Nat) (x : α) : Vect α n :=
    match n with
    | 0 => .nil
    | k + 1 => .cons _ _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ α"
end expect

expect error {{{ replicateMatchFive }}}
  def Vect.replicate (n : Nat) (x : α) : Vect α n :=
    match n with
    | 0 => .nil
    | k + 1 => .cons _ _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n : Nat
x : α
k : Nat
⊢ Vect α k "
end expect



expect error {{{ replicateOops }}}
  def Vect.replicate (n : Nat) (x : α) : Vect α n :=
    match n with
    | 0 => .nil
    | k + 1 => .cons x (.cons x (replicate k x))
message
"application type mismatch
  cons x (cons x (replicate k x))
argument
  cons x (replicate k x)
has type
  Vect α (k + 1) : Type ?u.1998
but is expected to have type
  Vect α k : Type ?u.1998"
end expect


book declaration {{{ replicate }}}
  def Vect.replicate (n : Nat) (x : α) : Vect α n :=
    match n with
    | 0 => .nil
    | k + 1 => .cons x (replicate k x)
stop book declaration


namespace Extras
book declaration {{{ listReplicate }}}
  def List.replicate (n : Nat) (x : α) : List α :=
    match n with
    | 0 => []
    | k + 1 => x :: x :: replicate k x
stop book declaration
end Extras

expect info {{{ replicateHi }}}
  #eval Vect.replicate 3 "hi"
message
"Vect.cons \"hi\" (Vect.cons \"hi\" (Vect.cons \"hi\" (Vect.nil)))"
end expect

bookExample {{{ zip1 }}}
  ["Mount Hood",
   "Mount Jefferson",
   "South Sister"].zip ["Møllehøj", "Yding Skovhøj", "Ejer Bavnehøj"]
  ===>
  [("Mount Hood", "Møllehøj"),
   ("Mount Jefferson", "Yding Skovhøj"),
   ("South Sister", "Ejer Bavnehøj")]
end bookExample

bookExample {{{ zip2 }}}
  [3428.8, 3201, 3158.5, 3075, 3064].zip [170.86, 170.77, 170.35]
  ===>
  [(3428.8, 170.86), (3201, 170.77), (3158.5, 170.35)]
end bookExample


book declaration {{{ VectZip }}}
  def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
    | .nil, .nil => .nil
    | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
stop book declaration

namespace Other


expect error {{{ zipMissing }}}
  def List.zip : List α → List β → List (α × β)
    | [], [] => []
    | x :: xs, y :: ys => (x, y) :: zip xs ys
message
"missing cases:
(List.cons _ _), []
[], (List.cons _ _)"
end expect

expect error {{{ zipExtraCons }}}
  def Vect.zip : Vect α n → Vect β n → Vect (α × β) n
    | .nil, .nil => .nil
    | .nil, .cons y ys => .nil
    | .cons x xs, .cons y ys => .cons (x, y) (zip xs ys)
message
"type mismatch
  Vect.cons y ys
has type
  Vect β (?m.4718 + 1) : Type ?u.4530
but is expected to have type
  Vect β 0 : Type ?u.4530"
end expect
end Other

namespace Details

book declaration {{{ VectZipLen }}}
  def Vect.zip : (n : Nat) → Vect α n → Vect β n → Vect (α × β) n
    | 0, .nil, .nil => .nil
    | k + 1, .cons x xs, .cons y ys => .cons (x, y) (zip k xs ys)
stop book declaration

end Details


def oregonianPeaks : Vect String 3 :=
  .cons "Mount Hood" <|
  .cons "Mount Jefferson" <|
  .cons "South Sister" <| .nil

def danishPeaks : Vect String 3 :=
  .cons "Møllehøj" <|
  .cons "Yding Skovhøj" <|
  .cons "Ejer Bavnehøj" <| .nil


expect info {{{ peaksVectZip }}}
  #eval oregonianPeaks.zip danishPeaks
message
"Vect.cons
  (\"Mount Hood\", \"Møllehøj\")
  (Vect.cons (\"Mount Jefferson\", \"Yding Skovhøj\") (Vect.cons (\"South Sister\", \"Ejer Bavnehøj\") (Vect.nil)))"
end expect

def Vect.map (f : α → β) : Vect α n → Vect β n
  | .nil => .nil
  | .cons x xs => .cons (f x) (map f xs)

def Vect.zipWith : (α → β → γ) → Vect α n → Vect β n → Vect γ n
  | f, .nil, .nil => .nil
  | f, .cons x xs, .cons y ys => .cons (f x y) (zipWith f xs ys)

def Vect.unzip : Vect (α × β) n → Vect α n × Vect β n
  | .nil => (.nil, .nil)
  | .cons (x, y) xys =>
    let (xs, ys) := unzip xys
    (.cons x xs, .cons y ys)

def Vect.snoc : Vect α n → α → Vect α (n + 1)
  | .nil, x => .cons x .nil
  | .cons y ys, x => .cons y (snoc ys x)


expect info {{{ snocSnowy }}}
  #eval Vect.snoc (.cons "snowy" .nil) "peaks"
message
"Vect.cons \"snowy\" (Vect.cons \"peaks\" (Vect.nil))"
end expect

def Vect.reverse : Vect α n → Vect α n
  | .nil => .nil
  | .cons x xs => Vect.snoc (reverse xs) x

def Vect.drop : (n : Nat) → Vect α (k + n) → Vect α k
  | 0, xs => xs
  | j + 1, .cons _ xs => drop j xs


expect info {{{ ejerBavnehoej }}}
  #eval danishPeaks.drop 2
message
"Vect.cons \"Ejer Bavnehøj\" (Vect.nil)"
end expect

def Vect.take : (n : Nat) → Vect α (k + n) → Vect α n
  | 0, _ => .nil
  | j + 1, .cons x xs => .cons x (take j xs)
