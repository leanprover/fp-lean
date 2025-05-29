import ExampleSupport
import Examples.Classes

example := Monad
example := @HAdd.hAdd
example := @HMul.hMul
example := IO


-- ANCHOR: exceptNames
section
example := Except
example := @Except.ok
example := @Except.error
end
-- ANCHOR_END: exceptNames

namespace Monads.Option

variable {α : Type}

-- ANCHOR: first
def first (xs : List α) : Option α :=
  xs[0]?
-- ANCHOR_END: first


-- ANCHOR: firstThird
def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)
-- ANCHOR_END: firstThird


-- ANCHOR: firstThirdFifth
def firstThirdFifth (xs : List α) : Option (α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        some (first, third, fifth)
-- ANCHOR_END: firstThirdFifth


-- ANCHOR: firstThirdFifthSeventh
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      match xs[4]? with
      | none => none
      | some fifth =>
        match xs[6]? with
        | none => none
        | some seventh =>
          some (first, third, fifth, seventh)
-- ANCHOR_END: firstThirdFifthSeventh

namespace M
-- ANCHOR: andThenOption
def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x
-- ANCHOR_END: andThenOption


-- ANCHOR: firstThirdandThen
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)
-- ANCHOR_END: firstThirdandThen

namespace ExplicitParens
-- ANCHOR: firstThirdandThenExpl
def firstThird (xs : List α) : Option (α × α) :=
  andThen xs[0]? (fun first =>
    andThen xs[2]? (fun third =>
      some (first, third)))
-- ANCHOR_END: firstThirdandThenExpl
end ExplicitParens

namespace Fixity
axiom w : Nat
axiom x : Nat
axiom y : Nat
axiom z : Nat

-- ANCHOR: plusFixity
example : w + x + y + z = (((w + x) + y) + z) := rfl
-- ANCHOR_END: plusFixity

-- ANCHOR: powFixity
example : w ^ x ^ y ^ z = (w ^ (x ^ (y ^ z))) := rfl
-- ANCHOR_END: powFixity

-- ANCHOR: plusTimesPrec
example : x + y * z = x + (y * z) := rfl
-- ANCHOR_END: plusTimesPrec


end Fixity



-- ANCHOR: andThenOptArr
infixl:55 " ~~> " => andThen
-- ANCHOR_END: andThenOptArr



-- ANCHOR: firstThirdInfix
def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)
-- ANCHOR_END: firstThirdInfix


-- ANCHOR: firstThirdFifthSeventInfix
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)
-- ANCHOR_END: firstThirdFifthSeventInfix
end M

end Monads.Option

namespace FakeExcept
-- ANCHOR: Except
inductive Except (ε : Type) (α : Type) where
  | error : ε → Except ε α
  | ok : α → Except ε α
deriving BEq, Hashable, Repr
-- ANCHOR_END: Except
attribute [inherit_doc _root_.Except] Except
attribute [inherit_doc _root_.Except.ok] Except.ok
attribute [inherit_doc _root_.Except.error] Except.error
--ANCHOR: ExceptExtra
example := @Except.error
example := @Except.ok
--ANCHOR_END: ExceptExtra
end FakeExcept
similar datatypes FakeExcept.Except Except

namespace Monads.Err


-- ANCHOR: getExcept
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x
-- ANCHOR_END: getExcept


-- ANCHOR: ediblePlants
def ediblePlants : List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]
-- ANCHOR_END: ediblePlants

/-- info:
Except.ok "sea buckthorn"
-/
#check_msgs in
-- ANCHOR: success
#eval get ediblePlants 2
-- ANCHOR_END: success

/-- info:
Except.error "Index 4 not found (maximum is 3)"
-/
#check_msgs in
-- ANCHOR: failure
#eval get ediblePlants 4
-- ANCHOR_END: failure


-- ANCHOR: firstExcept
def first (xs : List α) : Except String α :=
  get xs 0
-- ANCHOR_END: firstExcept


-- ANCHOR: firstThirdExcept
def firstThird (xs : List α) : Except String (α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      Except.ok (first, third)
-- ANCHOR_END: firstThirdExcept


-- ANCHOR: firstThirdFifthExcept
def firstThirdFifth (xs : List α) : Except String (α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        Except.ok (first, third, fifth)
-- ANCHOR_END: firstThirdFifthExcept


-- ANCHOR: firstThirdFifthSeventhExcept
def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  match get xs 0 with
  | Except.error msg => Except.error msg
  | Except.ok first =>
    match get xs 2 with
    | Except.error msg => Except.error msg
    | Except.ok third =>
      match get xs 4 with
      | Except.error msg => Except.error msg
      | Except.ok fifth =>
        match get xs 6 with
        | Except.error msg => Except.error msg
        | Except.ok seventh =>
          Except.ok (first, third, fifth, seventh)
-- ANCHOR_END: firstThirdFifthSeventhExcept


-- ANCHOR: andThenExcept
def andThen (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x
-- ANCHOR_END: andThenExcept

namespace AndThen
-- ANCHOR: firstThirdAndThenExcept
def firstThird' (xs : List α) : Except String (α × α) :=
  andThen (get xs 0) fun first  =>
  andThen (get xs 2) fun third =>
  Except.ok (first, third)
-- ANCHOR_END: firstThirdAndThenExcept
end AndThen



-- ANCHOR: andThenExceptInfix
infixl:55 " ~~> " => andThen
-- ANCHOR_END: andThenExceptInfix

-- ANCHOR: okExcept
def ok (x : α) : Except ε α := Except.ok x
-- ANCHOR_END: okExcept

-- ANCHOR: failExcept
def fail (err : ε) : Except ε α := Except.error err
-- ANCHOR_END: failExcept

namespace Eff
-- ANCHOR: getExceptEffects
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x
-- ANCHOR_END: getExceptEffects
end Eff

namespace WithInfix
-- ANCHOR: firstThirdInfixExcept
def firstThird (xs : List α) : Except String (α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  ok (first, third)
-- ANCHOR_END: firstThirdInfixExcept

-- ANCHOR: firstThirdFifthSeventInfixExcept
def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)
-- ANCHOR_END: firstThirdFifthSeventInfixExcept

end WithInfix


end Monads.Err





namespace Monads.Writer


-- ANCHOR: isEven
def isEven (i : Int) : Bool :=
  i % 2 == 0
-- ANCHOR_END: isEven

example : isEven 34 := by decide
example : ¬isEven 39 := by decide


-- ANCHOR: sumAndFindEvensDirect
def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    (if isEven i then i :: moreEven else moreEven, sum + i)
-- ANCHOR_END: sumAndFindEvensDirect

namespace MoreMonadic
-- ANCHOR: sumAndFindEvensDirectish
def sumAndFindEvens : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens is
    let (evenHere, ()) := (if isEven i then [i] else [], ())
    (evenHere ++ moreEven, sum + i)
-- ANCHOR_END: sumAndFindEvensDirectish
end MoreMonadic

-- ANCHOR: inorderSum
def inorderSum : BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | BinTree.branch l x r =>
    let (leftVisited, leftSum) := inorderSum l
    let (hereVisited, hereSum) := ([x], x)
    let (rightVisited, rightSum) := inorderSum r
    (leftVisited ++ hereVisited ++ rightVisited,
     leftSum + hereSum + rightSum)
-- ANCHOR_END: inorderSum


-- ANCHOR: WithLog
structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
-- ANCHOR_END: WithLog

section
variable {logged : Type}
example := WithLog logged
end

deriving instance Repr for WithLog

-- ANCHOR: andThenWithLog
def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}
-- ANCHOR_END: andThenWithLog


-- ANCHOR: okWithLog
def ok (x : β) : WithLog α β := {log := [], val := x}
-- ANCHOR_END: okWithLog


-- ANCHOR: save
def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}
-- ANCHOR_END: save

namespace WithAndThen


-- ANCHOR: sumAndFindEvensAndThen
def sumAndFindEvens : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    andThen (if isEven i then save i else ok ()) fun () =>
    andThen (sumAndFindEvens is) fun sum =>
    ok (i + sum)
-- ANCHOR_END: sumAndFindEvensAndThen


-- ANCHOR: inorderSumAndThen
def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    andThen (inorderSum l) fun leftSum =>
    andThen (save x) fun () =>
    andThen (inorderSum r) fun rightSum =>
    ok (leftSum + x + rightSum)
-- ANCHOR_END: inorderSumAndThen

end WithAndThen



-- ANCHOR: infixAndThenLog
infixl:55 " ~~> " => andThen
-- ANCHOR_END: infixAndThenLog

namespace WithInfix


-- ANCHOR: withInfixLogging
def sumAndFindEvens : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    (if isEven i then save i else ok ()) ~~> fun () =>
    sumAndFindEvens is ~~> fun sum =>
    ok (i + sum)

def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    inorderSum l ~~> fun leftSum =>
    save x ~~> fun () =>
    inorderSum r ~~> fun rightSum =>
    ok (leftSum + x + rightSum)
-- ANCHOR_END: withInfixLogging

end WithInfix

end Monads.Writer

namespace Monads.State


-- ANCHOR: aTree
open BinTree in
def aTree :=
  branch
    (branch
       (branch leaf "a" (branch leaf "b" leaf))
       "c"
       leaf)
    "d"
    (branch leaf "e" leaf)
-- ANCHOR_END: aTree

-- TODO include in text
deriving instance Repr for BinTree

-- ANCHOR: numberDirect
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf => (n, BinTree.leaf)
    | BinTree.branch left x right =>
      let (k, numberedLeft) := helper n left
      let (i, numberedRight) := helper (k + 1) right
      (i, BinTree.branch numberedLeft (k, x) numberedRight)
  (helper 0 t).snd
-- ANCHOR_END: numberDirect



/-- info:
BinTree.branch
  (BinTree.branch
    (BinTree.branch (BinTree.leaf) (0, "a") (BinTree.branch (BinTree.leaf) (1, "b") (BinTree.leaf)))
    (2, "c")
    (BinTree.leaf))
  (3, "d")
  (BinTree.branch (BinTree.leaf) (4, "e") (BinTree.leaf))
-/
#check_msgs in
-- ANCHOR: numberATree
#eval number aTree
-- ANCHOR_END: numberATree


-- ANCHOR: State
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)
-- ANCHOR_END: State


-- ANCHOR: get
def get : State σ σ :=
  fun s => (s, s)
-- ANCHOR_END: get


-- ANCHOR: set
def set (s : σ) : State σ Unit :=
  fun _ => (s, ())
-- ANCHOR_END: set


-- ANCHOR: andThenState
def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s
    next x s'

infixl:55 " ~~> " => andThen
-- ANCHOR_END: andThenState


-- ANCHOR: okState
def ok (x : α) : State σ α :=
  fun s => (s, x)
-- ANCHOR_END: okState


namespace Monadicish


-- ANCHOR: numberMonadicish
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => ok BinTree.leaf
    | BinTree.branch left x right =>
      helper left ~~> fun numberedLeft =>
      get ~~> fun n =>
      set (n + 1) ~~> fun () =>
      helper right ~~> fun numberedRight =>
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd
-- ANCHOR_END: numberMonadicish

end Monadicish

example : number aTree = Monadicish.number aTree := by rfl

end Monads.State
