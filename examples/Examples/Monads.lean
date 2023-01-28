import Examples.Support
import Examples.Classes

namespace Monads.Option


book declaration {{{ first }}}
  def first (xs : List α) : Option α :=
    xs[0]?
stop book declaration


book declaration {{{ firstThird }}}
  def firstThird (xs : List α) : Option (α × α) :=
    match xs[0]? with
    | none => none
    | some first =>
      match xs[2]? with
      | none => none
      | some third =>
        some (first, third)
stop book declaration


book declaration {{{ firstThirdFifth }}}
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
stop book declaration


book declaration {{{ firstThirdFifthSeventh }}}
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
stop book declaration

namespace M
book declaration {{{ andThenOption }}}
  def andThen (opt : Option α) (next : α → Option β) : Option β :=
    match opt with
    | none => none
    | some x => next x
stop book declaration


book declaration {{{ firstThirdandThen }}}
  def firstThird (xs : List α) : Option (α × α) :=
    andThen xs[0]? fun first =>
    andThen xs[2]? fun third =>
    some (first, third)
stop book declaration

namespace ExplicitParens
book declaration {{{ firstThirdandThenExpl }}}
  def firstThird (xs : List α) : Option (α × α) :=
    andThen xs[0]? (fun first =>
      andThen xs[2]? (fun third =>
        some (first, third)))
stop book declaration
end ExplicitParens

namespace Fixity
axiom w : Nat
axiom x : Nat
axiom y : Nat
axiom z : Nat

bookExample {{{ plusFixity }}}
  w + x + y + z
  ===>
  (((w + x) + y) + z)
end bookExample

bookExample {{{ powFixity }}}
  w ^ x ^ y ^ z
  ===>
  (w ^ (x ^ (y ^ z)))
end bookExample

bookExample {{{ plusTimesPrec }}}
  x + y * z
  ===>
  x + (y * z)
end bookExample


end Fixity



book declaration {{{ andThenOptArr }}}
  infixl:55 " ~~> " => andThen
stop book declaration



book declaration {{{ firstThirdInfix }}}
  def firstThirdInfix (xs : List α) : Option (α × α) :=
    xs[0]? ~~> fun first =>
    xs[2]? ~~> fun third =>
    some (first, third)
stop book declaration


book declaration {{{ firstThirdFifthSeventInfix }}}
  def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
    xs[0]? ~~> fun first =>
    xs[2]? ~~> fun third =>
    xs[4]? ~~> fun fifth =>
    xs[6]? ~~> fun seventh =>
    some (first, third, fifth, seventh)
stop book declaration
end M

end Monads.Option

namespace FakeExcept
book declaration {{{ Except }}}
  inductive Except (ε : Type) (α : Type) where
    | error : ε → Except ε α
    | ok : α → Except ε α
  deriving BEq, Hashable, Repr
stop book declaration
end FakeExcept
similar datatypes FakeExcept.Except Except

namespace Monads.Err


book declaration {{{ getExcept }}}
  def get (xs : List α) (i : Nat) : Except String α :=
    match xs[i]? with
    | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
    | some x => Except.ok x
stop book declaration


book declaration {{{ ediblePlants }}}
  def ediblePlants : List String :=
    ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]
stop book declaration

expect info {{{ success }}}
  #eval get ediblePlants 2
message
  "Except.ok \"sea buckthorn\""
end expect

expect info {{{ failure }}}
  #eval get ediblePlants 4
message
  "Except.error \"Index 4 not found (maximum is 3)\""
end expect


book declaration {{{ firstExcept }}}
  def first (xs : List α) : Except String α :=
    get xs 0
stop book declaration


book declaration {{{ firstThirdExcept }}}
  def firstThird (xs : List α) : Except String (α × α) :=
    match get xs 0 with
    | Except.error msg => Except.error msg
    | Except.ok first =>
      match get xs 2 with
      | Except.error msg => Except.error msg
      | Except.ok third =>
        Except.ok (first, third)
stop book declaration


book declaration {{{ firstThirdFifthExcept }}}
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
stop book declaration


book declaration {{{ firstThirdFifthSeventhExcept }}}
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
stop book declaration


book declaration {{{ andThenExcept }}}
  def andThen (attempt : Except e α) (next : α → Except e β) : Except e β :=
    match attempt with
    | Except.error msg => Except.error msg
    | Except.ok x => next x
stop book declaration

namespace AndThen
book declaration {{{ firstThirdAndThenExcept }}}
  def firstThird' (xs : List α) : Except String (α × α) :=
    andThen (get xs 0) fun first  =>
    andThen (get xs 2) fun third =>
    Except.ok (first, third)
stop book declaration
end AndThen



book declaration {{{ andThenExceptInfix }}}
  infixl:55 " ~~> " => andThen
stop book declaration

book declaration {{{ okExcept }}}
  def ok (x : α) : Except ε α := Except.ok x
stop book declaration

book declaration {{{ failExcept }}}
  def fail (err : ε) : Except ε α := Except.error err
stop book declaration

namespace Eff
book declaration {{{ getExceptEffects }}}
  def get (xs : List α) (i : Nat) : Except String α :=
    match xs[i]? with
    | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
    | some x => ok x
stop book declaration
end Eff

namespace WithInfix
book declaration {{{ firstThirdInfixExcept }}}
  def firstThird (xs : List α) : Except String (α × α) :=
    get xs 0 ~~> fun first =>
    get xs 2 ~~> fun third =>
    ok (first, third)
stop book declaration

book declaration {{{ firstThirdFifthSeventInfixExcept }}}
  def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
    get xs 0 ~~> fun first =>
    get xs 2 ~~> fun third =>
    get xs 4 ~~> fun fifth =>
    get xs 6 ~~> fun seventh =>
    ok (first, third, fifth, seventh)
stop book declaration

end WithInfix


end Monads.Err





namespace Monads.Writer


book declaration {{{ isEven }}}
  def isEven (i : Int) : Bool :=
    i % 2 == 0
stop book declaration

example : isEven 34 := by simp
example : ¬isEven 39 := by simp


book declaration {{{ sumAndFindEvensDirect }}}
  def sumAndFindEvens : List Int → List Int × Int
    | [] => ([], 0)
    | i :: is =>
      let (moreEven, sum) := sumAndFindEvens is
      (if isEven i then i :: moreEven else moreEven, sum + i)
stop book declaration

namespace MoreMonadic
book declaration {{{ sumAndFindEvensDirectish }}}
  def sumAndFindEvens : List Int → List Int × Int
    | [] => ([], 0)
    | i :: is =>
      let (moreEven, sum) := sumAndFindEvens is
      let (evenHere, ()) := (if isEven i then [i] else [], ())
      (evenHere ++ moreEven, sum + i)
stop book declaration
end MoreMonadic

book declaration {{{ preorderSum }}}
  def preorderSum : BinTree Int → List Int × Int
    | BinTree.leaf => ([], 0)
    | BinTree.branch l x r =>
      let (leftVisited, leftSum) := preorderSum l
      let (hereVisited, hereSum) := ([x], x)
      let (rightVisited, rightSum) := preorderSum r
      (leftVisited ++ hereVisited ++ rightVisited, leftSum + hereSum + rightSum)
stop book declaration


book declaration {{{ WithLog }}}
  structure WithLog (logged : Type) (α : Type) where
    log : List logged
    val : α
stop book declaration

deriving instance Repr for WithLog

book declaration {{{ andThenWithLog }}}
  def andThen (result : WithLog α β) (next : β → WithLog α γ) : WithLog α γ :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
stop book declaration


book declaration {{{ okWithLog }}}
  def ok (x : β) : WithLog α β := {log := [], val := x}
stop book declaration


book declaration {{{ save }}}
  def save (data : α) : WithLog α Unit :=
    {log := [data], val := ()}
stop book declaration

namespace WithAndThen


book declaration {{{ sumAndFindEvensAndThen }}}
  def sumAndFindEvens : List Int → WithLog Int Int
    | [] => ok 0
    | i :: is =>
      andThen (if isEven i then save i else ok ()) fun () =>
      andThen (sumAndFindEvens is) fun sum =>
      ok (i + sum)
stop book declaration


book declaration {{{ preorderSumAndThen }}}
  def preorderSum : BinTree Int → WithLog Int Int
    | BinTree.leaf => ok 0
    | BinTree.branch l x r =>
      andThen (preorderSum l) fun leftSum =>
      andThen (save x) fun () =>
      andThen (preorderSum r) fun rightSum =>
      ok (leftSum + x + rightSum)
stop book declaration

end WithAndThen



book declaration {{{ infixAndThenLog }}}
  infixl:55 " ~~> " => andThen
stop book declaration

namespace WithInfix


book declaration {{{ withInfixLogging }}}
  def sumAndFindEvens : List Int → WithLog Int Int
    | [] => ok 0
    | i :: is =>
      (if isEven i then save i else ok ()) ~~> fun () =>
      sumAndFindEvens is ~~> fun sum =>
      ok (i + sum)

  def preorderSum : BinTree Int → WithLog Int Int
    | BinTree.leaf => ok 0
    | BinTree.branch l x r =>
      preorderSum l ~~> fun leftSum =>
      save x ~~> fun () =>
      preorderSum r ~~> fun rightSum =>
      ok (leftSum + x + rightSum)
stop book declaration

end WithInfix

end Monads.Writer

namespace Monads.State


book declaration {{{ aTree }}}
  open BinTree in
  def aTree :=
    branch
      (branch
         (branch leaf "a" (branch leaf "b" leaf))
         "c"
         leaf)
      "d"
      (branch leaf "e" leaf)
stop book declaration

-- TODO include in text
deriving instance Repr for BinTree

book declaration {{{ numberDirect }}}
  def number (t : BinTree α) : BinTree (Nat × α) :=
    let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
      | BinTree.leaf => (n, BinTree.leaf)
      | BinTree.branch left x right =>
        let (k, numberedLeft) := helper n left
        let (i, numberedRight) := helper (k + 1) right
        (i, BinTree.branch numberedLeft (k, x) numberedRight)
    (helper 0 t).snd
stop book declaration



expect info {{{ numberATree }}}
  #eval number aTree
message
"BinTree.branch
  (BinTree.branch
    (BinTree.branch (BinTree.leaf) (0, \"a\") (BinTree.branch (BinTree.leaf) (1, \"b\") (BinTree.leaf)))
    (2, \"c\")
    (BinTree.leaf))
  (3, \"d\")
  (BinTree.branch (BinTree.leaf) (4, \"e\") (BinTree.leaf))"
end expect


book declaration {{{ State }}}
  def State (σ : Type) (α : Type) : Type :=
    σ → (σ × α)
stop book declaration


book declaration {{{ get }}}
  def get : State σ σ :=
    fun s => (s, s)
stop book declaration


book declaration {{{ set }}}
  def set (s : σ) : State σ Unit :=
    fun _ => (s, ())
stop book declaration


book declaration {{{ andThenState }}}
  def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
    fun s =>
      let (s', x) := first s
      next x s'

  infixl:55 " ~~> " => andThen
stop book declaration


book declaration {{{ okState }}}
  def ok (x : α) : State σ α :=
    fun s => (s, x)
stop book declaration


namespace Monadicish


book declaration {{{ numberMonadicish }}}
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
stop book declaration

end Monadicish

example : number aTree = Monadicish.number aTree := by rfl

end Monads.State



