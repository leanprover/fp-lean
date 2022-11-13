import Examples.Support
import Examples.Monads
import Examples.Monads.Many

namespace Class
book declaration {{{ FakeMonad }}}
  class Monad (m : Type → Type) where
    pure : α → m α
    bind : m α → (α → m β) → m β
stop book declaration
end Class



book declaration {{{ firstThirdFifthSeventhMonad }}}
  def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) :=
    lookup xs 0 >>= fun first =>
    lookup xs 2 >>= fun third =>
    lookup xs 4 >>= fun fifth =>
    lookup xs 6 >>= fun seventh =>
    pure (first, third, fifth, seventh)
stop book declaration


book declaration {{{ animals }}}
  def slowMammals : List String :=
    ["Three-toed sloth", "Slow loris"]

  def fastBirds : List String := [
    "Peregrine falcon",
    "Saker falcon",
    "Golden eagle",
    "Gray-headed albatross",
    "Spur-winged goose",
    "Swift",
    "Anna's hummingbird"
  ]
stop book declaration

expect info {{{ noneSlow }}}
  #eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals
message
  "none"
end expect

expect info {{{ someFast }}}
  #eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds
message
  "some (\"Peregrine falcon\", \"Golden eagle\", \"Spur-winged goose\", \"Anna's hummingbird\")"
end expect

namespace Errs

book declaration {{{ getOrExcept }}}
  def getOrExcept (xs : List α) (i : Nat) : Except String α :=
    match xs[i]? with
    | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
    | some x => Except.ok x
stop book declaration


expect info {{{ errorSlow }}}
  #eval firstThirdFifthSeventh getOrExcept slowMammals
message
  "Except.error \"Index 2 not found (maximum is 1)\""
end expect


expect info {{{ okFast }}}
  #eval firstThirdFifthSeventh getOrExcept fastBirds
message
  "Except.ok (\"Peregrine falcon\", \"Golden eagle\", \"Spur-winged goose\", \"Anna's hummingbird\")"
end expect
end Errs


namespace IdentMonad


book declaration {{{ IdMonad }}}
  def Id (t : Type) : Type := t

  instance : Monad Id where
    pure x := x
    bind x f := f x
stop book declaration

end IdentMonad


namespace MyListStuff



book declaration {{{ mapM }}}
  def mapM [Monad m] (f : α → m β) : List α → m (List β)
    | [] => pure []
    | x :: xs =>
      f x >>= fun hd =>
      mapM f xs >>= fun tl =>
      pure (hd :: tl)
stop book declaration

open Monads.State (State get set)

book declaration {{{ StateMonad }}}
  instance : Monad (State σ) where
    pure x := fun s => (s, x)
    bind first next :=
      fun s =>
        let (s', x) := first s
        next x s'
stop book declaration


book declaration {{{ increment }}}
  def increment (howMuch : Int) : State Int Int :=
    get >>= fun i =>
    set (i + howMuch) >>= fun ⟨⟩ =>
    pure i
stop book declaration

bookExample type {{{ mapMincrement }}}
  mapM increment
  ===>
  List Int → State Int (List Int)
end bookExample

bookExample type {{{ mapMincrement2 }}}
  mapM increment
  ===>
  List Int → Int → (Int × List Int)
end bookExample


expect info {{{ mapMincrementOut }}}
  #eval mapM increment [1, 2, 3, 4, 5] 0
message
  "(15, [0, 1, 3, 6, 10])"
end expect

-- TODO fix error about unknown universe levels here
-- evaluation steps : (State Int (List Int) : Type) {{{ mapMincrOutSteps }}}
--   mapM increment [1, 2]
--   ===>
--   match [1, 2] with
--   | [] => pure []
--   | x :: xs =>
--     increment x >>= fun hd =>
--     mapM increment xs >>= fun tl =>
--     pure (hd :: tl)
--   ===>
--   increment 1 >>= fun hd =>
--   mapM increment [2] >>= fun tl  =>
--   pure (hd :: tl)
--   ===>
--   (get >>= fun i =>
--    set (i + 1) >>= fun ⟨⟩ =>
--    pure i) >>= fun hd =>
--   mapM increment [2] >>= fun tl =>
--   pure (hd :: tl)
-- end evaluation steps

-- TODO same
-- evaluation steps : (State Int (List Int) : Type) {{{ mapMincrOutSteps }}}
--   mapM increment []
--   ===>
--   match [] with
--   | [] => pure []
--   | x :: xs =>
--     increment x >>= fun hd =>
--     mapM increment xs >>= fun tl =>
--     pure (hd :: tl)
--   ===>
--   pure []
--   ===>
--   fun s => ([], s)
-- end evaluation steps

open Monads.Writer (WithLog save isEven)


book declaration {{{ MonadWriter }}}
  instance : Monad (WithLog logged) where
    pure x := {log := [], val := x}
    bind result next :=
      let {log := thisOut, val := thisRes} := result
      let {log := nextOut, val := nextRes} := next thisRes
      {log := thisOut ++ nextOut, val := nextRes}
stop book declaration


book declaration {{{ saveIfEven }}}
  def saveIfEven (i : Int) : WithLog Int Int :=
    (if isEven i then
      save i
     else pure ⟨⟩) >>= fun ⟨⟩ =>
    pure i
stop book declaration


expect info {{{ mapMsaveIfEven }}}
  #eval mapM saveIfEven [1, 2, 3, 4, 5]
message
  "{ log := [2, 4], val := [1, 2, 3, 4, 5] }"
end expect

expect info {{{ mapMId }}}
  #eval mapM (m := Id) (· + 1) [1, 2, 3, 4, 5]
message
  "[2, 3, 4, 5, 6]"
end expect



expect error {{{ mapMIdNoHint }}}
  #eval mapM (· + 1) [1, 2, 3, 4, 5]
message
"failed to synthesize instance
  HAdd Nat Nat (?m.7879 ?m.7881)"
end expect


expect error {{{ mapMIdId }}}
  #eval mapM (fun x => x) [1, 2, 3, 4, 5]
message
"typeclass instance problem is stuck, it is often due to metavariables
  Monad ?m.7879"
end expect

end MyListStuff

inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special
  deriving Repr

def evaluate [Monad m] (evalOp : op → Int → Int → m Int) : Expr op → m Int
  | Expr.const i => pure i
  | Expr.prim op x y =>
    evaluate evalOp x >>= fun xv =>
    evaluate evalOp y >>= fun yv =>
    evalOp op xv yv

inductive CanFail where | div

def evalOpOption : Prim CanFail → Int → Int → Option Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other CanFail.div, x, y =>
    if y == 0 then
      none
    else pure (x / y)

def evalOpExcept : Prim CanFail → Int → Int → Except String Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other CanFail.div, x, y =>
    if y == 0 then
      Except.error "Division by 0"
    else pure (x / y)

open Monads.Writer (WithLog save)

instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}

deriving instance Repr for WithLog

def evalOpWithLog (op : Prim Empty) (x : Int) (y : Int) : WithLog (Prim Empty × Int × Int) Int :=
  save (op, x, y) >>= fun ⟨⟩ =>
  match op with
  | Prim.plus => pure (x + y)
  | Prim.minus => pure (x - y)
  | Prim.times => pure (x * y)

deriving instance Repr for Empty

def evalOpId (op : Prim Empty) (x : Int) (y : Int) : Id Int :=
  match op with
  | Prim.plus => pure (x + y)
  | Prim.minus => pure (x - y)
  | Prim.times => pure (x * y)

open Monads.State (State get set)

def evalOpState (op : Prim Empty) (x : Int) (y : Int) : State Nat Int :=
  get >>= fun i =>
  set (i + 1) >>= fun ⟨⟩ =>
  match op with
  | Prim.plus => pure (x + y)
  | Prim.minus => pure (x - y)
  | Prim.times => pure (x * y)

#eval evaluate evalOpOption (Expr.prim Prim.plus (Expr.const 2) (Expr.prim (Prim.other CanFail.div) (Expr.const 3) (Expr.const 5)))
#eval evaluate evalOpOption (Expr.prim Prim.plus (Expr.const 2) (Expr.prim (Prim.other CanFail.div) (Expr.const 3) (Expr.const 0)))
#eval evaluate evalOpExcept (Expr.prim Prim.plus (Expr.const 2) (Expr.prim (Prim.other CanFail.div) (Expr.const 3) (Expr.const 5)))
#eval evaluate evalOpExcept (Expr.prim Prim.plus (Expr.const 2) (Expr.prim (Prim.other CanFail.div) (Expr.const 3) (Expr.const 0)))
#eval evaluate evalOpWithLog (Expr.prim Prim.plus (Expr.const 2) (Expr.prim Prim.times (Expr.const 3) (Expr.const 5)))
#eval evaluate evalOpId (Expr.prim Prim.plus (Expr.const 2) (Expr.prim Prim.times (Expr.const 3) (Expr.const 5)))


inductive ManyPrim
  | both
  | neither

def evalOpMany (op : Prim ManyPrim) (x : Int) (y : Int) : Many Int :=
  match op with
  | Prim.plus => pure (x + y)
  | Prim.minus => pure (x - y)
  | Prim.times => pure (x * y)
  | Prim.other ManyPrim.both => Many.fromList [x, y]
  | Prim.other ManyPrim.neither => Many.nil

#eval evaluate evalOpMany (Expr.prim Prim.plus (Expr.const 2) (Expr.prim (Prim.other ManyPrim.both) (Expr.const 3) (Expr.const 5))) |> Many.take 5
