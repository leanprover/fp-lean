import ExampleSupport

-- ANCHOR: names
example := IO
section
local instance : Monad IO where
  pure := pure
  bind := bind
universe u
example {ε} {α}:= EIO ε α
-- ANCHOR: EStateMNames
example {ε} {α} {σ} := EStateM ε σ α → EStateM.Result ε σ α
-- ANCHOR_END: EStateMNames
example := @EStateM.Result.ok
example := @EStateM.Result.error
example {α}:= BaseIO α
example {ε} := Except ε
example := Type u
end
-- ANCHOR_END: names

/-- info:
inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat
-/
#check_msgs in
-- ANCHOR: printNat
#print Nat
-- ANCHOR_END: printNat


/-- info:
def Char.isAlpha : Char → Bool :=
fun c => c.isUpper || c.isLower
-/
#check_msgs in
-- ANCHOR: printCharIsAlpha
#print Char.isAlpha
-- ANCHOR_END: printCharIsAlpha


/-- info:
def List.isEmpty.{u} : {α : Type u} → List α → Bool :=
fun {α} x =>
  match x with
  | [] => true
  | head :: tail => false
-/
#check_msgs in
-- ANCHOR: printListIsEmpty
#print List.isEmpty
-- ANCHOR_END: printListIsEmpty



/-- info:
@[reducible] def IO : Type → Type :=
EIO IO.Error
-/
#check_msgs in
-- ANCHOR: printIO
#print IO
-- ANCHOR_END: printIO



/-- info:
inductive IO.Error : Type
number of parameters: 0
constructors:
IO.Error.alreadyExists : Option String → UInt32 → String → IO.Error
IO.Error.otherError : UInt32 → String → IO.Error
IO.Error.resourceBusy : UInt32 → String → IO.Error
IO.Error.resourceVanished : UInt32 → String → IO.Error
IO.Error.unsupportedOperation : UInt32 → String → IO.Error
IO.Error.hardwareFault : UInt32 → String → IO.Error
IO.Error.unsatisfiedConstraints : UInt32 → String → IO.Error
IO.Error.illegalOperation : UInt32 → String → IO.Error
IO.Error.protocolError : UInt32 → String → IO.Error
IO.Error.timeExpired : UInt32 → String → IO.Error
IO.Error.interrupted : String → UInt32 → String → IO.Error
IO.Error.noFileOrDirectory : String → UInt32 → String → IO.Error
IO.Error.invalidArgument : Option String → UInt32 → String → IO.Error
IO.Error.permissionDenied : Option String → UInt32 → String → IO.Error
IO.Error.resourceExhausted : Option String → UInt32 → String → IO.Error
IO.Error.inappropriateType : Option String → UInt32 → String → IO.Error
IO.Error.noSuchThing : Option String → UInt32 → String → IO.Error
IO.Error.unexpectedEof : IO.Error
IO.Error.userError : String → IO.Error
-/
#check_msgs in
-- ANCHOR: printIOError
#print IO.Error
-- ANCHOR_END: printIOError


/-- info:
def EIO : Type → Type → Type :=
fun ε => EStateM ε IO.RealWorld
-/
#check_msgs in
-- ANCHOR: printEIO
#print EIO
-- ANCHOR_END: printEIO



/-- info:
def EStateM.{u} : Type u → Type u → Type u → Type u :=
fun ε σ α => σ → EStateM.Result ε σ α
-/
#check_msgs in
-- ANCHOR: printEStateM
#print EStateM
-- ANCHOR_END: printEStateM


/-- info:
inductive EStateM.Result.{u} : Type u → Type u → Type u → Type u
number of parameters: 3
constructors:
EStateM.Result.ok : {ε σ α : Type u} → α → σ → EStateM.Result ε σ α
EStateM.Result.error : {ε σ α : Type u} → ε → σ → EStateM.Result ε σ α
-/
#check_msgs in
-- ANCHOR: printEStateMResult
#print EStateM.Result
-- ANCHOR_END: printEStateMResult


/-- info:
protected def EStateM.pure.{u} : {ε σ α : Type u} → α → EStateM ε σ α :=
fun {ε σ α} a s => EStateM.Result.ok a s
-/
#check_msgs in
-- ANCHOR: printEStateMpure
#print EStateM.pure
-- ANCHOR_END: printEStateMpure

/-- info:
protected def EStateM.bind.{u} : {ε σ α β : Type u} → EStateM ε σ α → (α → EStateM ε σ β) → EStateM ε σ β :=
fun {ε σ α β} x f s =>
  match x s with
  | EStateM.Result.ok a s => f a s
  | EStateM.Result.error e s => EStateM.Result.error e s
-/
#check_msgs in
-- ANCHOR: printEStateMbind
#print EStateM.bind
-- ANCHOR_END: printEStateMbind


/-- info:
def IO.RealWorld : Type :=
Unit
-/
#check_msgs in
-- ANCHOR: printRealWorld
#print IO.RealWorld
-- ANCHOR_END: printRealWorld
