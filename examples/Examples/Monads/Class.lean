import Examples.Support
import Examples.Monads

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

namespace MyListStuff


def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)

open Monads.State (State get set)

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

def increment (howMuch : Int) : State Int Int :=
  get >>= fun i =>
  set (i + howMuch) >>= fun ⟨⟩ =>
  pure i

#eval (mapM increment [1, 2, 3, 4]) 0

open Monads.Writer (WithLog save)

instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}

#eval mapM save [1, 2, 3, 4]

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

instance : Repr Empty where
  reprPrec (x : Empty) := x.rec

def evalOpId (op : Prim Empty) (x : Int) (y : Int) : Id Int :=
  match op with
  | Prim.plus => pure (x + y)
  | Prim.minus => pure (x - y)
  | Prim.times => pure (x * y)

open Monads.State (State get set)

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

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

inductive Many (α : Type) where
  | nil : Many α
  | cons : α → (Unit → Many α) → Many α

def Many.append : Many α → Many α → Many α
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (fun ⟨⟩ => append (xs ⟨⟩) ys)

def Many.bind : Many α → (α → Many β) → Many β
  | .nil, _ => .nil
  | .cons x more, f => (f x).append (bind (more ⟨⟩) f)

instance : Monad Many where
  pure x := .cons x (fun ⟨⟩ => .nil)
  bind := Many.bind

def Many.fromList : List α → Many α
  | [] => .nil
  | x :: xs => .cons x (fun ⟨⟩ => fromList xs)

def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, .nil => []
  | n + 1, .cons x xs => x :: (xs ⟨⟩).take n

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
