import Examples.Support

expect info {{{ printNat }}}
  #print Nat
message
"inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat"
end expect


expect info {{{ printCharIsAlpha }}}
  #print Char.isAlpha
message
"def Char.isAlpha : Char → Bool :=
fun c => c.isUpper || c.isLower"
end expect


expect info {{{ printListIsEmpty }}}
  #print List.isEmpty
message
"def List.isEmpty.{u} : {α : Type u} → List α → Bool :=
fun {α} x =>
  match x with
  | [] => true
  | head :: tail => false"
end expect



expect info {{{ printIO }}}
  #print IO
message
"@[reducible] def IO : Type → Type :=
EIO IO.Error"
end expect



expect info {{{ printIOError }}}
  #print IO.Error
message
"inductive IO.Error : Type
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
IO.Error.userError : String → IO.Error"
end expect


expect info {{{ printEIO }}}
  #print EIO
message
"def EIO : Type → Type → Type :=
fun ε => EStateM ε IO.RealWorld"
end expect



expect info {{{ printEStateM }}}
  #print EStateM
message
"def EStateM.{u} : Type u → Type u → Type u → Type u :=
fun ε σ α => σ → EStateM.Result ε σ α"
end expect


expect info {{{ printEStateMResult }}}
  #print EStateM.Result
message
"inductive EStateM.Result.{u} : Type u → Type u → Type u → Type u
number of parameters: 3
constructors:
EStateM.Result.ok : {ε σ α : Type u} → α → σ → EStateM.Result ε σ α
EStateM.Result.error : {ε σ α : Type u} → ε → σ → EStateM.Result ε σ α"
end expect


expect info {{{ printEStateMpure }}}
  #print EStateM.pure
message
"protected def EStateM.pure.{u} : {ε σ α : Type u} → α → EStateM ε σ α :=
fun {ε σ α} a s => EStateM.Result.ok a s"
end expect

expect info {{{ printEStateMbind }}}
  #print EStateM.bind
message
"protected def EStateM.bind.{u} : {ε σ α β : Type u} → EStateM ε σ α → (α → EStateM ε σ β) → EStateM ε σ β :=
fun {ε σ α β} x f s =>
  match x s with
  | EStateM.Result.ok a s => f a s
  | EStateM.Result.error e s => EStateM.Result.error e s"
end expect


expect info {{{ printRealWorld }}}
  #print IO.RealWorld
message
"def IO.RealWorld : Type :=
Unit"
end expect
