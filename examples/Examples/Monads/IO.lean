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
example {ε} {α} {σ} := EST ε σ α → EST.Out ε σ α
-- ANCHOR_END: EStateMNames
example := @EST.Out.ok
example := @EST.Out.error
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
fun ε α => EST ε IO.RealWorld α
-/
#check_msgs in
-- ANCHOR: printEIO
#print EIO
-- ANCHOR_END: printEIO

-- ANCHOR: VoidSigma
example {σ} := Void σ
-- ANCHOR_END: VoidSigma

-- ANCHOR: RealWorld
example := IO.RealWorld
-- ANCHOR_END: RealWorld


/-- info:
def EST : Type → Type → Type → Type :=
fun ε σ α => Void σ → EST.Out ε σ α
-/
#check_msgs in
-- ANCHOR: printEStateM
#print EST
-- ANCHOR_END: printEStateM


/-- info:
inductive EST.Out : Type → Type → Type → Type
number of parameters: 3
constructors:
EST.Out.ok : {ε σ α : Type} → α → Void σ → EST.Out ε σ α
EST.Out.error : {ε σ α : Type} → ε → Void σ → EST.Out ε σ α
-/
#check_msgs in
-- ANCHOR: printEStateMResult
#print EST.Out
-- ANCHOR_END: printEStateMResult


/-- info:
protected def EST.pure : {α ε σ : Type} → α → EST ε σ α :=
fun {α ε σ} a s => EST.Out.ok a s
-/
#check_msgs in
-- ANCHOR: printEStateMpure
#print EST.pure
-- ANCHOR_END: printEStateMpure

/-- info:
protected def EST.bind : {ε σ α β : Type} → EST ε σ α → (α → EST ε σ β) → EST ε σ β :=
fun {ε σ α β} x f s =>
  match x s with
  | EST.Out.ok a s => f a s
  | EST.Out.error e s => EST.Out.error e s
-/
#check_msgs in
-- ANCHOR: printEStateMbind
#print EST.bind
-- ANCHOR_END: printEStateMbind
