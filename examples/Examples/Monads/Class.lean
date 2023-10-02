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


book declaration {{{ MonadOptionExcept }}}
  instance : Monad Option where
    pure x := some x
    bind opt next :=
      match opt with
      | none => none
      | some x => next x

  instance : Monad (Except ε) where
    pure x := Except.ok x
    bind attempt next :=
      match attempt with
      | Except.error e => Except.error e
      | Except.ok x => next x
stop book declaration

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
    set (i + howMuch) >>= fun () =>
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
--    set (i + 1) >>= fun () =>
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
     else pure ()) >>= fun () =>
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
  HAdd Nat Nat (?m.9063 ?m.9065)"
end expect


expect error {{{ mapMIdId }}}
  #eval mapM (fun x => x) [1, 2, 3, 4, 5]
message
"typeclass instance problem is stuck, it is often due to metavariables
  Monad ?m.9063"
end expect

end MyListStuff



book declaration {{{ ExprArith }}}
  inductive Expr (op : Type) where
    | const : Int → Expr op
    | prim : op → Expr op → Expr op → Expr op


  inductive Arith where
    | plus
    | minus
    | times
    | div
stop book declaration

book declaration {{{ twoPlusThree }}}
  open Expr in
  open Arith in
  def twoPlusThree : Expr Arith :=
    prim plus (const 2) (const 3)
stop book declaration


book declaration {{{ exampleArithExpr }}}
  open Expr in
  open Arith in
  def fourteenDivided : Expr Arith :=
    prim div (const 14) (prim minus (const 45) (prim times (const 5) (const 9)))
stop book declaration

namespace One
book declaration {{{ evaluateOptionCommingled }}}
  def evaluateOption : Expr Arith → Option Int
    | Expr.const i => pure i
    | Expr.prim p e1 e2 =>
      evaluateOption e1 >>= fun v1 =>
      evaluateOption e2 >>= fun v2 =>
      match p with
      | Arith.plus => pure (v1 + v2)
      | Arith.minus => pure (v1 - v2)
      | Arith.times => pure (v1 * v2)
      | Arith.div => if v2 == 0 then none else pure (v1 / v2)
stop book declaration
end One

namespace Two

book declaration {{{ evaluateOptionSplit }}}
  def applyPrim : Arith → Int → Int → Option Int
    | Arith.plus, x, y => pure (x + y)
    | Arith.minus, x, y => pure (x - y)
    | Arith.times, x, y => pure (x * y)
    | Arith.div, x, y => if y == 0 then none else pure (x / y)

  def evaluateOption : Expr Arith → Option Int
    | Expr.const i => pure i
    | Expr.prim p e1 e2 =>
      evaluateOption e1 >>= fun v1 =>
      evaluateOption e2 >>= fun v2 =>
      applyPrim p v1 v2
stop book declaration


expect info {{{ fourteenDivOption }}}
  #eval evaluateOption fourteenDivided
message
"none"
end expect

end Two


namespace Three

book declaration {{{ evaluateExcept }}}
  def applyPrim : Arith → Int → Int → Except String Int
    | Arith.plus, x, y => pure (x + y)
    | Arith.minus, x, y => pure (x - y)
    | Arith.times, x, y => pure (x * y)
    | Arith.div, x, y =>
      if y == 0 then
        Except.error s!"Tried to divide {x} by zero"
      else pure (x / y)


  def evaluateExcept : Expr Arith → Except String Int
    | Expr.const i => pure i
    | Expr.prim p e1 e2 =>
      evaluateExcept e1 >>= fun v1 =>
      evaluateExcept e2 >>= fun v2 =>
      applyPrim p v1 v2
stop book declaration

end Three

namespace Four


book declaration {{{ evaluateM }}}
  def applyPrimOption : Arith → Int → Int → Option Int
    | Arith.plus, x, y => pure (x + y)
    | Arith.minus, x, y => pure (x - y)
    | Arith.times, x, y => pure (x * y)
    | Arith.div, x, y =>
      if y == 0 then
        none
      else pure (x / y)

  def applyPrimExcept : Arith → Int → Int → Except String Int
    | Arith.plus, x, y => pure (x + y)
    | Arith.minus, x, y => pure (x - y)
    | Arith.times, x, y => pure (x * y)
    | Arith.div, x, y =>
      if y == 0 then
        Except.error s!"Tried to divide {x} by zero"
      else pure (x / y)

  def evaluateM [Monad m] (applyPrim : Arith → Int → Int → m Int): Expr Arith → m Int
    | Expr.const i => pure i
    | Expr.prim p e1 e2 =>
      evaluateM applyPrim e1 >>= fun v1 =>
      evaluateM applyPrim e2 >>= fun v2 =>
      applyPrim p v1 v2
stop book declaration

expect info {{{ evaluateMOption }}}
  #eval evaluateM applyPrimOption fourteenDivided
message
"none"
end expect


expect info {{{ evaluateMExcept }}}
  #eval evaluateM applyPrimExcept fourteenDivided
message
"Except.error \"Tried to divide 14 by zero\""
end expect


end Four

namespace FourPointFive
book declaration {{{ evaluateMRefactored }}}
  def applyDivOption (x : Int) (y : Int) : Option Int :=
      if y == 0 then
        none
      else pure (x / y)

  def applyDivExcept (x : Int) (y : Int) : Except String Int :=
      if y == 0 then
        Except.error s!"Tried to divide {x} by zero"
      else pure (x / y)

  def applyPrim [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
    | Arith.plus, x, y => pure (x + y)
    | Arith.minus, x, y => pure (x - y)
    | Arith.times, x, y => pure (x * y)
    | Arith.div, x, y => applyDiv x y

  def evaluateM [Monad m] (applyDiv : Int → Int → m Int): Expr Arith → m Int
    | Expr.const i => pure i
    | Expr.prim p e1 e2 =>
      evaluateM applyDiv e1 >>= fun v1 =>
      evaluateM applyDiv e2 >>= fun v2 =>
      applyPrim applyDiv p v1 v2
stop book declaration

end FourPointFive

example : Four.evaluateM Four.applyPrimOption = FourPointFive.evaluateM FourPointFive.applyDivOption := by
  funext e
  induction e with
  | const => simp [Four.evaluateM, FourPointFive.evaluateM]
  | prim p e1 e2 ih1 ih2 =>
    simp [Four.evaluateM, FourPointFive.evaluateM, *]
    rfl

example : Four.evaluateM Four.applyPrimExcept = FourPointFive.evaluateM FourPointFive.applyDivExcept := by
  funext e
  induction e with
  | const => simp [Four.evaluateM, FourPointFive.evaluateM]
  | prim p e1 e2 ih1 ih2 =>
    simp [Four.evaluateM, FourPointFive.evaluateM, *]
    rfl


book declaration {{{ PrimCanFail }}}
  inductive Prim (special : Type) where
    | plus
    | minus
    | times
    | other : special → Prim special

  inductive CanFail where
    | div
stop book declaration



book declaration {{{ evaluateMMorePoly }}}
  def divOption : CanFail → Int → Int → Option Int
    | CanFail.div, x, y => if y == 0 then none else pure (x / y)

  def divExcept : CanFail → Int → Int → Except String Int
    | CanFail.div, x, y =>
      if y == 0 then
        Except.error s!"Tried to divide {x} by zero"
      else pure (x / y)

  def applyPrim [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
    | Prim.plus, x, y => pure (x + y)
    | Prim.minus, x, y => pure (x - y)
    | Prim.times, x, y => pure (x * y)
    | Prim.other op, x, y => applySpecial op x y

  def evaluateM [Monad m] (applySpecial : special → Int → Int → m Int): Expr (Prim special) → m Int
    | Expr.const i => pure i
    | Expr.prim p e1 e2 =>
      evaluateM applySpecial e1 >>= fun v1 =>
      evaluateM applySpecial e2 >>= fun v2 =>
      applyPrim applySpecial p v1 v2
stop book declaration


book declaration {{{ applyEmpty }}}
  def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
    nomatch op
stop book declaration


expect info {{{ evalId }}}
  open Expr Prim in
  #eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))
message
"-9"
end expect

book declaration {{{ NeedsSearch }}}
  inductive NeedsSearch
    | div
    | choose

  def applySearch : NeedsSearch → Int → Int → Many Int
    | NeedsSearch.choose, x, y =>
      Many.fromList [x, y]
    | NeedsSearch.div, x, y =>
      if y == 0 then
        Many.none
      else Many.one (x / y)
stop book declaration

section

book declaration {{{ opening }}}
  open Expr Prim NeedsSearch
stop book declaration


expect info {{{ searchA }}}
  #eval (evaluateM applySearch (prim plus (const 1) (prim (other choose) (const 2) (const 5)))).takeAll
message
"[3, 6]"
end expect


expect info {{{ searchB }}}
  #eval (evaluateM applySearch (prim plus (const 1) (prim (other div) (const 2) (const 0)))).takeAll
message
"[]"
end expect


expect info {{{ searchC }}}
  #eval (evaluateM applySearch (prim (other div) (const 90) (prim plus (prim (other choose) (const (-5)) (const 5)) (const 5)))).takeAll
message
  "[9]"
end expect

end



book declaration {{{ Reader }}}
  def Reader (ρ : Type) (α : Type) : Type := ρ → α

  def read : Reader ρ ρ := fun env => env
stop book declaration

namespace Temp


expect error {{{ readerbind0 }}}
  def Reader.bind {ρ : Type} {α : Type} {β : Type}
    (result : ρ → α) (next : α → ρ → β) : ρ → β :=
    _
message
"don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
⊢ ρ → β"
end expect

expect error {{{ readerbind1 }}}
  def Reader.bind {ρ : Type} {α : Type} {β : Type}
    (result : ρ → α) (next : α → ρ → β) : ρ → β :=
    fun env => _
message
"don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ β"
end expect

expect error {{{ readerbind2a }}}
  def Reader.bind {ρ : Type} {α : Type} {β : Type}
    (result : ρ → α) (next : α → ρ → β) : ρ → β :=
    fun env => next _ _
message
"don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ α"
end expect


expect error {{{ readerbind2b }}}
  def Reader.bind {ρ : Type} {α : Type} {β : Type}
    (result : ρ → α) (next : α → ρ → β) : ρ → β :=
    fun env => next _ _
message
"don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ"
end expect


expect error {{{ readerbind3 }}}
  def Reader.bind {ρ : Type} {α : Type} {β : Type}
    (result : ρ → α) (next : α → ρ → β) : ρ → β :=
    fun env => next (result _) _
message
"don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ"
end expect


book declaration {{{ readerbind4 }}}
  def Reader.bind {ρ : Type} {α : Type} {β : Type}
    (result : ρ → α) (next : α → ρ → β) : ρ → β :=
    fun env => next (result env) env
stop book declaration

end Temp


book declaration {{{ Readerbind }}}
  def Reader.bind (result : Reader ρ α) (next : α → Reader ρ β) : Reader ρ β :=
    fun env => next (result env) env
stop book declaration

namespace TTT
axiom α : Type
axiom β : Type
axiom ρ : Type
bookExample type {{{ readerBindType }}}
  Reader.bind
  ===>
  Reader ρ α → (α → Reader ρ β) → Reader ρ β
end bookExample
bookExample {{{ readerBindTypeEval }}}
  Reader ρ α → (α → Reader ρ β) → Reader ρ β
  ===>
  (ρ → α) → (α → ρ → β) → ρ → β
end bookExample


end TTT

book declaration {{{ ReaderPure }}}
  def Reader.pure (x : α) : Reader ρ α := fun _ => x
stop book declaration


namespace MonadLaws
axiom α : Type
axiom ρ : Type
axiom β : Type
axiom γ : Type
axiom v : α
axiom r : Reader ρ α
axiom f : α → Reader ρ β
axiom g : β → Reader ρ γ

evaluation steps {{{ ReaderMonad1 }}}
  Reader.bind (Reader.pure v) f
  ===>
  fun env => f ((Reader.pure v) env) env
  ===>
  fun env => f ((fun _ => v) env) env
  ===>
  fun env => f v env
  ===>
  f v
end evaluation steps

evaluation steps {{{ ReaderMonad2 }}}
  Reader.bind r Reader.pure
  ===>
  fun env => Reader.pure (r env) env
  ===>
  fun env => (fun _ => (r env)) env
  ===>
  fun env => r env
end evaluation steps

evaluation steps {{{ ReaderMonad3a }}}
  Reader.bind (Reader.bind r f) g
  ===>
  fun env => g ((Reader.bind r f) env) env
  ===>
  fun env => g ((fun env' => f (r env') env') env) env
  ===>
  fun env => g (f (r env) env) env
end evaluation steps

evaluation steps {{{ ReaderMonad3b }}}
  Reader.bind r (fun x => Reader.bind (f x) g)
  ===>
  Reader.bind r (fun x => fun env => g (f x env) env)
  ===>
  fun env => (fun x => fun env' => g (f x env') env') (r env) env
  ===>
  fun env => (fun env' => g (f (r env) env') env') env
  ===>
  fun env => g (f (r env) env) env
end evaluation steps


end MonadLaws

book declaration {{{ MonadReaderInst }}}
  instance : Monad (Reader ρ) where
    pure x := fun _ => x
    bind x f := fun env => f (x env) env
stop book declaration

instance : LawfulMonad (Reader ρ) where
  map_const := by
    simp [Functor.mapConst, Function.comp, Functor.map]
  id_map x := by
    simp [Functor.map]
  seqLeft_eq x _ := by
    simp [SeqLeft.seqLeft, Seq.seq, Functor.map]
  seqRight_eq _ y := by
    simp [SeqRight.seqRight, Seq.seq, Functor.map]
  pure_seq g x := by
    simp [Seq.seq, Functor.map, pure]
  bind_pure_comp f x := by
    simp [Functor.map, bind, pure]
  bind_map f x := by
    simp [Seq.seq, bind, Functor.map]
  pure_bind x f := by
    simp [pure, bind]
  bind_assoc x f g := by
    simp [bind]



book declaration {{{ Env }}}
  abbrev Env : Type := List (String × (Int → Int → Int))
stop book declaration


book declaration {{{ applyPrimReader }}}
  def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
    read >>= fun env =>
    match env.lookup op with
    | none => pure 0
    | some f => pure (f x y)
stop book declaration


book declaration {{{ exampleEnv }}}
  def exampleEnv : Env := [("max", max), ("mod", (· % ·))]
stop book declaration

expect info {{{ readerEval }}}
  open Expr Prim in
  #eval evaluateM applyPrimReader (prim (other "max") (prim plus (const 5) (const 4)) (prim times (const 3) (const 2))) exampleEnv
message
"9"
end expect

namespace Exercises

def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | .leaf => pure .leaf
  | .branch l x r =>
    mapM f l >>= fun l' =>
    f x >>= fun x' =>
    mapM f r >>= fun r' =>
    pure (BinTree.branch l' x' r')

namespace Busted


set_option linter.unusedVariables false in
book declaration {{{ badOptionMonad }}}
  instance : Monad Option where
    pure x := some x
    bind opt next := none
stop book declaration

end Busted


open Monads.Writer (WithLog save)

instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}


book declaration {{{ ReprInstances }}}
deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim
stop book declaration

book declaration {{{ ToTrace }}}
  inductive ToTrace (α : Type) : Type where
    | trace : α → ToTrace α
stop book declaration

def applyTraced : ToTrace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int
  | ToTrace.trace op, x, y =>
    save (op, x, y) >>= fun () =>
    applyPrim applyEmpty op x y

bookExample type {{{ applyTracedType }}}
  applyTraced
  ===>
  ToTrace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int
end bookExample



expect info {{{ evalTraced }}}
  open Expr Prim ToTrace in
  #eval evaluateM applyTraced (prim (other (trace times)) (prim (other (trace plus)) (const 1) (const 2)) (prim (other (trace minus)) (const 3) (const 4)))
message
"{ log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4), (Prim.times, 3, -1)], val := -3 }"
end expect

book declaration {{{ ReaderFail }}}
def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α
stop book declaration



end Exercises


-- def evalOpWithLog (op : Prim Empty) (x : Int) (y : Int) : WithLog (Prim Empty × Int × Int) Int :=
--   save (op, x, y) >>= fun () =>
--   match op with
--   | Prim.plus => pure (x + y)
--   | Prim.minus => pure (x - y)
--   | Prim.times => pure (x * y)

--

-- def evalOpId (op : Prim Empty) (x : Int) (y : Int) : Id Int :=
--   match op with
--   | Prim.plus => pure (x + y)
--   | Prim.minus => pure (x - y)
--   | Prim.times => pure (x * y)

-- open Monads.State (State get set)

-- def evalOpState (op : Prim Empty) (x : Int) (y : Int) : State Nat Int :=
--   get >>= fun i =>
--   set (i + 1) >>= fun () =>
--   match op with
--   | Prim.plus => pure (x + y)
--   | Prim.minus => pure (x - y)
--   | Prim.times => pure (x * y)

-- deriving instance Repr for Prim

-- #eval evaluate evalOpOption (Expr.prim Prim.plus (Expr.const 2) (Expr.prim (Prim.other CanFail.div) (Expr.const 3) (Expr.const 5)))
-- #eval evaluate evalOpOption (Expr.prim Prim.plus (Expr.const 2) (Expr.prim (Prim.other CanFail.div) (Expr.const 3) (Expr.const 0)))
-- #eval evaluate evalOpExcept (Expr.prim Prim.plus (Expr.const 2) (Expr.prim (Prim.other CanFail.div) (Expr.const 3) (Expr.const 5)))
-- #eval evaluate evalOpExcept (Expr.prim Prim.plus (Expr.const 2) (Expr.prim (Prim.other CanFail.div) (Expr.const 3) (Expr.const 0)))
-- #eval evaluate evalOpWithLog (Expr.prim Prim.plus (Expr.const 2) (Expr.prim Prim.times (Expr.const 3) (Expr.const 5)))
-- #eval evaluate evalOpId (Expr.prim Prim.plus (Expr.const 2) (Expr.prim Prim.times (Expr.const 3) (Expr.const 5)))
