import ExampleSupport
import Examples.Monads
import Examples.Monads.Many

set_option linter.unusedVariables false

-- ANCHOR: Names
example := Option
example := IO
section
variable (ε : Type)
example := Except ε

variable {α : Type}
example := Option α
example := Except String α
example := @Functor.map
end
-- ANCHOR_END: Names

namespace Class
variable {α β : Type} {m : Type → Type}
-- ANCHOR: FakeMonad
class Monad (m : Type → Type) where
  pure : α → m α
  bind : m α → (α → m β) → m β
-- ANCHOR_END: FakeMonad
end Class


-- ANCHOR: MonadOptionExcept
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
-- ANCHOR_END: MonadOptionExcept
section
variable {α : Type} {m : Type → Type}
-- ANCHOR: firstThirdFifthSeventhMonad
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) :=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)
-- ANCHOR_END: firstThirdFifthSeventhMonad
end

-- ANCHOR: animals
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
-- ANCHOR_END: animals

/-- info:
none
-/
#check_msgs in
-- ANCHOR: noneSlow
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals
-- ANCHOR_END: noneSlow

/-- info:
some ("Peregrine falcon", "Golden eagle", "Spur-winged goose", "Anna's hummingbird")
-/
#check_msgs in
-- ANCHOR: someFast
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds
-- ANCHOR_END: someFast

namespace Errs

-- ANCHOR: getOrExcept
def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none =>
    Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x =>
    Except.ok x
-- ANCHOR_END: getOrExcept


/-- info:
Except.error "Index 2 not found (maximum is 1)"
-/
#check_msgs in
-- ANCHOR: errorSlow
#eval firstThirdFifthSeventh getOrExcept slowMammals
-- ANCHOR_END: errorSlow


/-- info:
Except.ok ("Peregrine falcon", "Golden eagle", "Spur-winged goose", "Anna's hummingbird")
-/
#check_msgs in
-- ANCHOR: okFast
#eval firstThirdFifthSeventh getOrExcept fastBirds
-- ANCHOR_END: okFast
end Errs


namespace IdentMonad


-- ANCHOR: IdMonad
def Id (t : Type) : Type := t

instance : Monad Id where
  pure x := x
  bind x f := f x
-- ANCHOR_END: IdMonad

end IdentMonad

-- ANCHOR: IdMore

example : Id α = α := rfl
example : (α → Id α) = (α → α) := rfl
example : (α → (α → Id β) → Id β) = (α → (α → β) → β) := rfl

-- ANCHOR_END: IdMore


namespace MyListStuff
variable {α β : Type} {m : Type → Type}


-- ANCHOR: mapM
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)
-- ANCHOR_END: mapM

open Monads.State (State get set)

-- ANCHOR: StateEx
section
variable {σ α : Type}
example := State σ α
example := Type → Type

example : State σ σ := get
example : σ → State σ Unit := set

end
-- ANCHOR_END: StateEx

-- ANCHOR: StateMonad
instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'
-- ANCHOR_END: StateMonad


-- ANCHOR: increment
def increment (howMuch : Int) : State Int Int :=
  get >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i
-- ANCHOR_END: increment

-- ANCHOR: mapMincrement
example : List Int → State Int (List Int) := mapM increment
-- ANCHOR_END: mapMincrement

-- ANCHOR: mapMincrement2
example : List Int → Int → (Int × List Int) := mapM increment
-- ANCHOR_END: mapMincrement2


/-- info:
(15, [0, 1, 3, 6, 10])
-/
#check_msgs in
-- ANCHOR: mapMincrementOut
#eval mapM increment [1, 2, 3, 4, 5] 0
-- ANCHOR_END: mapMincrementOut

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


-- ANCHOR: MonadWriter
instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
-- ANCHOR_END: MonadWriter


-- ANCHOR: saveIfEven
def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then
    save i
   else pure ()) >>= fun () =>
  pure i
-- ANCHOR_END: saveIfEven


/-- info:
{ log := [2, 4], val := [1, 2, 3, 4, 5] }
-/
#check_msgs in
-- ANCHOR: mapMsaveIfEven
#eval mapM saveIfEven [1, 2, 3, 4, 5]
-- ANCHOR_END: mapMsaveIfEven

/-- info:
[2, 3, 4, 5, 6]
-/
#check_msgs in
-- ANCHOR: mapMId
#eval mapM (m := Id) (· + 1) [1, 2, 3, 4, 5]
-- ANCHOR_END: mapMId



/--
error: failed to synthesize
  HAdd Nat Nat (?m.4 ?m.3)

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: mapMIdNoHint
#eval mapM (· + 1) [1, 2, 3, 4, 5]
-- ANCHOR_END: mapMIdNoHint


/-- error:
typeclass instance problem is stuck, it is often due to metavariables
  Monad ?m.4319
-/
#check_msgs in
-- ANCHOR: mapMIdId
#eval mapM (fun (x : Nat) => x) [1, 2, 3, 4, 5]
-- ANCHOR_END: mapMIdId

end MyListStuff



-- ANCHOR: ExprArith
inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op


inductive Arith where
  | plus
  | minus
  | times
  | div
-- ANCHOR_END: ExprArith

-- ANCHOR: twoPlusThree
open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)
-- ANCHOR_END: twoPlusThree


-- ANCHOR: exampleArithExpr
open Expr in
open Arith in
def fourteenDivided : Expr Arith :=
  prim div (const 14)
    (prim minus (const 45)
      (prim times (const 5)
        (const 9)))
-- ANCHOR_END: exampleArithExpr

namespace One
-- ANCHOR: evaluateOptionCommingled
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
-- ANCHOR_END: evaluateOptionCommingled
end One

namespace Two

-- ANCHOR: evaluateOptionSplit
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
-- ANCHOR_END: evaluateOptionSplit


/-- info:
none
-/
#check_msgs in
-- ANCHOR: fourteenDivOption
#eval evaluateOption fourteenDivided
-- ANCHOR_END: fourteenDivOption

end Two


namespace Three

-- ANCHOR: evaluateExcept
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
-- ANCHOR_END: evaluateExcept

end Three

namespace Four


-- ANCHOR: evaluateM
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

def evaluateM [Monad m]
    (applyPrim : Arith → Int → Int → m Int) :
    Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyPrim e1 >>= fun v1 =>
    evaluateM applyPrim e2 >>= fun v2 =>
    applyPrim p v1 v2
-- ANCHOR_END: evaluateM

/-- info:
none
-/
#check_msgs in
-- ANCHOR: evaluateMOption
#eval evaluateM applyPrimOption fourteenDivided
-- ANCHOR_END: evaluateMOption


/-- info:
Except.error "Tried to divide 14 by zero"
-/
#check_msgs in
-- ANCHOR: evaluateMExcept
#eval evaluateM applyPrimExcept fourteenDivided
-- ANCHOR_END: evaluateMExcept


end Four

namespace FourPointFive
-- ANCHOR: evaluateMRefactored
def applyDivOption (x : Int) (y : Int) : Option Int :=
    if y == 0 then
      none
    else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m]
    (applyDiv : Int → Int → m Int) :
    Arith → Int → Int → m Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y

def evaluateM [Monad m]
    (applyDiv : Int → Int → m Int) :
    Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyDiv e1 >>= fun v1 =>
    evaluateM applyDiv e2 >>= fun v2 =>
    applyPrim applyDiv p v1 v2
-- ANCHOR_END: evaluateMRefactored

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


-- ANCHOR: PrimCanFail
inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div
-- ANCHOR_END: PrimCanFail



-- ANCHOR: evaluateMMorePoly
def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)

def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m]
    (applySpecial : special → Int → Int → m Int) :
    Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y

def evaluateM [Monad m]
    (applySpecial : special → Int → Int → m Int) :
    Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applySpecial e1 >>= fun v1 =>
    evaluateM applySpecial e2 >>= fun v2 =>
    applyPrim applySpecial p v1 v2
-- ANCHOR_END: evaluateMMorePoly


-- ANCHOR: applyEmpty
def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op
-- ANCHOR_END: applyEmpty


-- ANCHOR: nomatch
section
variable {E : Empty}
example : α := nomatch E
end
-- ANCHOR_END: nomatch

-- ANCHOR: etc
example := @List.cons
example := @List.lookup
-- ANCHOR_END: etc

/-- info:
-9
-/
#check_msgs in
-- ANCHOR: evalId
open Expr Prim in
#eval evaluateM (m := Id) applyEmpty (prim plus (const 5) (const (-14)))
-- ANCHOR_END: evalId

-- ANCHOR: NeedsSearch
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
-- ANCHOR_END: NeedsSearch

section

-- ANCHOR: opening
open Expr Prim NeedsSearch
-- ANCHOR_END: opening


/-- info:
[3, 6]
-/
#check_msgs in
-- ANCHOR: searchA
#eval
  (evaluateM applySearch
    (prim plus (const 1)
      (prim (other choose) (const 2)
        (const 5)))).takeAll
-- ANCHOR_END: searchA


/-- info:
[]
-/
#check_msgs in
-- ANCHOR: searchB
#eval
  (evaluateM applySearch
    (prim plus (const 1)
      (prim (other div) (const 2)
        (const 0)))).takeAll
-- ANCHOR_END: searchB


/-- info:
[9]
-/
#check_msgs in
-- ANCHOR: searchC
#eval
  (evaluateM applySearch
    (prim (other div) (const 90)
      (prim plus (prim (other choose) (const (-5)) (const 5))
        (const 5)))).takeAll
-- ANCHOR_END: searchC

end

-- ANCHOR: MonadContract
section
example := [BEq, Hashable]
variable {m} [Monad m] [LawfulMonad m]
variable {v : α} {f : α → m β}
example : bind (pure v) f = f v := by simp
variable {v : m α}
-- ANCHOR: MonadContract2
example : bind v pure = v := by simp
example : bind (bind v f) g = bind v (fun x => bind (f x) g) := by simp
end
-- ANCHOR_END: MonadContract2
-- ANCHOR_END: MonadContract


-- ANCHOR: Reader
def Reader (ρ : Type) (α : Type) : Type := ρ → α

def read : Reader ρ ρ := fun env => env
-- ANCHOR_END: Reader

namespace Temp

discarding
/-- error:
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
⊢ ρ → β
-/
#check_msgs in
-- ANCHOR: readerbind0
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  _
-- ANCHOR_END: readerbind0
stop discarding

discarding
/-- error:
don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ β
-/
#check_msgs in
-- ANCHOR: readerbind1
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => _
-- ANCHOR_END: readerbind1
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ
---
error: don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ α
-/
#check_msgs in
-- ANCHOR: readerbind2a
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next _ _
-- ANCHOR_END: readerbind2a
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ
---
error: don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ α
-/
#check_msgs in
-- ANCHOR: readerbind2b
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next _ _
-- ANCHOR_END: readerbind2b
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ
---
error: don't know how to synthesize placeholder
context:
ρ α β : Type
result : ρ → α
next : α → ρ → β
env : ρ
⊢ ρ
-/
#check_msgs in
-- ANCHOR: readerbind3
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result _) _
-- ANCHOR_END: readerbind3
stop discarding

-- ANCHOR: readerbind4
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env
-- ANCHOR_END: readerbind4

end Temp


-- ANCHOR: Readerbind
def Reader.bind
    (result : Reader ρ α)
    (next : α → Reader ρ β) : Reader ρ β :=
  fun env => next (result env) env
-- ANCHOR_END: Readerbind

namespace TTT
variable (α : Type)
variable (β : Type)
variable (ρ : Type)
-- ANCHOR: readerBindType
example : Reader ρ α → (α → Reader ρ β) → Reader ρ β := Reader.bind
-- ANCHOR_END: readerBindType
-- ANCHOR: readerBindTypeEval
example : (Reader ρ α → (α → Reader ρ β) → Reader ρ β) = ((ρ → α) → (α → ρ → β) → (ρ → β)) := by rfl
-- ANCHOR_END: readerBindTypeEval


end TTT

-- ANCHOR: ReaderPure
def Reader.pure (x : α) : Reader ρ α := fun _ => x
-- ANCHOR_END: ReaderPure


-- ANCHOR: eta
section
variable (f : α → β)
example : (fun x => f x) = f := rfl
end
-- ANCHOR_END: eta

namespace MonadLaws
variable (α : Type)
variable (ρ : Type)
variable (β : Type)
variable (γ : Type)
variable (v : α)
variable (r : Reader ρ α)
variable (f : α → Reader ρ β)
variable (g : β → Reader ρ γ)

evaluation steps {{{ ReaderMonad1 }}}
-- ANCHOR: ReaderMonad1
Reader.bind (Reader.pure v) f
===>
fun env => f ((Reader.pure v) env) env
===>
fun env => f ((fun _ => v) env) env
===>
fun env => f v env
===>
f v
-- ANCHOR_END: ReaderMonad1
end evaluation steps

evaluation steps {{{ ReaderMonad2 }}}
-- ANCHOR: ReaderMonad2
Reader.bind r Reader.pure
===>
fun env => Reader.pure (r env) env
===>
fun env => (fun _ => (r env)) env
===>
fun env => r env
-- ANCHOR_END: ReaderMonad2
end evaluation steps

evaluation steps {{{ ReaderMonad3a }}}
-- ANCHOR: ReaderMonad3a
Reader.bind (Reader.bind r f) g
===>
fun env => g ((Reader.bind r f) env) env
===>
fun env => g ((fun env' => f (r env') env') env) env
===>
fun env => g (f (r env) env) env
-- ANCHOR_END: ReaderMonad3a
end evaluation steps

evaluation steps {{{ ReaderMonad3b }}}
-- ANCHOR: ReaderMonad3b
Reader.bind r (fun x => Reader.bind (f x) g)
===>
Reader.bind r (fun x => fun env => g (f x env) env)
===>
fun env => (fun x => fun env' => g (f x env') env') (r env) env
===>
fun env => (fun env' => g (f (r env) env') env') env
===>
fun env => g (f (r env) env) env
-- ANCHOR_END: ReaderMonad3b
end evaluation steps


end MonadLaws

-- ANCHOR: MonadReaderInst
instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env
-- ANCHOR_END: MonadReaderInst

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



-- ANCHOR: Env
abbrev Env : Type := List (String × (Int → Int → Int))
-- ANCHOR_END: Env


-- ANCHOR: applyPrimReader
def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)
-- ANCHOR_END: applyPrimReader


-- ANCHOR: exampleEnv
def exampleEnv : Env := [("max", max), ("mod", (· % ·))]
-- ANCHOR_END: exampleEnv

/-- info:
9
-/
#check_msgs in
-- ANCHOR: readerEval
open Expr Prim in
#eval
  evaluateM applyPrimReader
    (prim (other "max") (prim plus (const 5) (const 4))
      (prim times (const 3)
        (const 2)))
    exampleEnv
-- ANCHOR_END: readerEval

namespace Exercises
---ANCHOR: ex1
def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | .leaf => pure .leaf
  | .branch l x r =>
    mapM f l >>= fun l' =>
    f x >>= fun x' =>
    mapM f r >>= fun r' =>
    pure (BinTree.branch l' x' r')
---ANCHOR_END: ex1
namespace Busted


set_option linter.unusedVariables false in
-- ANCHOR: badOptionMonad
instance : Monad Option where
  pure x := some x
  bind opt next := none
-- ANCHOR_END: badOptionMonad

end Busted


open Monads.Writer (WithLog save)

instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}


-- ANCHOR: ReprInstances
deriving instance Repr for WithLog
deriving instance Repr for Empty
deriving instance Repr for Prim
-- ANCHOR_END: ReprInstances

-- ANCHOR: ToTrace
inductive ToTrace (α : Type) : Type where
  | trace : α → ToTrace α
-- ANCHOR_END: ToTrace

def applyTraced : ToTrace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int
  | ToTrace.trace op, x, y =>
    save (op, x, y) >>= fun () =>
    applyPrim applyEmpty op x y

-- ANCHOR: applyTracedType
example : ToTrace (Prim Empty) → Int → Int → WithLog (Prim Empty × Int × Int) Int := applyTraced
-- ANCHOR_END: applyTracedType
--ANCHOR: ToTraceExpr
example := Expr (Prim (ToTrace (Prim Empty)))
--ANCHOR_END: ToTraceExpr


/-- info:
{ log := [(Prim.plus, 1, 2), (Prim.minus, 3, 4), (Prim.times, 3, -1)], val := -3 }
-/
#check_msgs in
-- ANCHOR: evalTraced
open Expr Prim ToTrace in
#eval
  evaluateM applyTraced
    (prim (other (trace times))
      (prim (other (trace plus)) (const 1)
        (const 2))
      (prim (other (trace minus)) (const 3)
        (const 4)))
-- ANCHOR_END: evalTraced

-- ANCHOR: ReaderFail
def ReaderOption (ρ : Type) (α : Type) : Type := ρ → Option α

def ReaderExcept (ε : Type) (ρ : Type) (α : Type) : Type := ρ → Except ε α
-- ANCHOR_END: ReaderFail



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
