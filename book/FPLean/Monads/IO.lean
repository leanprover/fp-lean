import VersoManual
import FPLean.Examples

open Verso.Genre Manual
open Verso Code External

open FPLean

set_option verso.exampleProject "../examples"
set_option verso.exampleModule "Examples.Monads.IO"

#doc (Manual) "The IO Monad" =>
%%%
tag := "io-monad"
%%%

{anchorName names}`IO` as a monad can be understood from two perspectives, which were described in the section on {ref "running-a-program"}[running programs].
Each can help to understand the meanings of {anchorName names}`pure` and {anchorName names}`bind` for {anchorName names}`IO`.

From the first perspective, an {anchorName names}`IO` action is an instruction to Lean's run-time system.
For example, the instruction might be “read a string from this file descriptor, then re-invoke the pure Lean code with the string”.
This perspective is an _exterior_ one, viewing the program from the perspective of the operating system.
In this case, {anchorName names}`pure` is an {anchorName names}`IO` action that does not request any effects from the RTS, and {anchorName names}`bind` instructs the RTS to first carry out one potentially-effectful operation and then invoke the rest of the program with the resulting value.

From the second perspective, an {anchorName names}`IO` action transforms the whole world.
{anchorName names}`IO` actions are actually pure, because they receive a unique world as an argument and then return the changed world.
This perspective is an _interior_ one that matches how {anchorName names}`IO` is represented inside of Lean.
The world is represented in Lean as a token, and the {anchorName names}`IO` monad is structured to make sure that each token is used exactly once.

To see how this works, it can be helpful to peel back one definition at a time.
The {kw}`#print` command reveals the internals of Lean datatypes and definitions.
For example,
```anchor printNat
#print Nat
```
results in
```anchorInfo printNat
inductive Nat : Type
number of parameters: 0
constructors:
Nat.zero : Nat
Nat.succ : Nat → Nat
```
and
```anchor printCharIsAlpha
#print Char.isAlpha
```
results in
```anchorInfo printCharIsAlpha
def Char.isAlpha : Char → Bool :=
fun c => c.isUpper || c.isLower
```

Sometimes, the output of {kw}`#print` includes Lean features that have not yet been presented in this book.
For example,
```anchor printListIsEmpty
#print List.isEmpty
```
produces
```anchorInfo printListIsEmpty
def List.isEmpty.{u} : {α : Type u} → List α → Bool :=
fun {α} x =>
  match x with
  | [] => true
  | head :: tail => false
```
which includes a {lit}`.{u}` after the definition's name, and annotates types as {anchorTerm names}`Type u` rather than just {anchorTerm names}`Type`.
This can be safely ignored for now.

Printing the definition of {anchorName names}`IO` shows that it's defined in terms of simpler structures:
```anchor printIO
#print IO
```
```anchorInfo printIO
@[reducible] def IO : Type → Type :=
EIO IO.Error
```
{anchorName printIOError}`IO.Error` represents all the errors that could be thrown by an {anchorName names}`IO` action:
```anchor printIOError
#print IO.Error
```
```anchorInfo printIOError
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
```
{anchorTerm names}`EIO ε α` represents {anchorName names}`IO` actions that will either terminate with an error of type {anchorName names}`ε` or succeed with a value of type {anchorName names}`α`.
This means that, like the {anchorTerm names}`Except ε` monad, the {anchorName names}`IO` monad includes the ability to define error handling and exceptions.

Peeling back another layer, {anchorName names}`EIO` is itself defined in terms of a simpler structure:
```anchor printEIO
#print EIO
```
```anchorInfo printEIO
def EIO : Type → Type → Type :=
fun ε α => EST ε IO.RealWorld α
```
The {anchorName printEStateM}`EST` monad includes both errors and state—it's similar to a combination of {anchorName names}`Except` and {anchorName State (module := Examples.Monads)}`State`.
It is defined using another type, {anchorName printEStateMResult}`EST.Out`:
```anchor printEStateM
#print EST
```
```anchorInfo printEStateM
def EST : Type → Type → Type → Type :=
fun ε σ α => Void σ → EST.Out ε σ α
```
In other words, a program with type {anchorTerm EStateMNames}`EST ε σ α` is a function that accepts an initial state of type {anchorName EStateMNames}`σ` and returns an {anchorTerm EStateMNames}`EST.Out ε σ α`.
The state is wrapped in the type {anchorName VoidSigma}`Void`, which is an internal primitive that causes a value to be erased from compiled code; {anchorTerm VoidSigma}`Void σ` has the same representation as {anchorName save (module:=Examples.Monads)}`Unit`.

{anchorName EStateMNames}`EST.Out` is very much like the definition of {anchorName names}`Except`, with one constructor that indicates a successful termination and one constructor that indicates an error:
```anchor printEStateMResult
#print EST.Out
```
```anchorInfo printEStateMResult
inductive EST.Out : Type → Type → Type → Type
number of parameters: 3
constructors:
EST.Out.ok : {ε σ α : Type} → α → Void σ → EST.Out ε σ α
EST.Out.error : {ε σ α : Type} → ε → Void σ → EST.Out ε σ α
```
Just like {anchorTerm Except (module:=Examples.Monads)}`Except ε α`, the {anchorName names (show := ok)}`EST.Out.ok` constructor includes a result of type {anchorName Except (module:=Examples.Monads)}`α`, and the {anchorName names (show := error)}`EST.Out.error` constructor includes an exception of type {anchorName Except (module:=Examples.Monads)}`ε`.
Unlike {anchorName names}`Except`, both constructors have an additional state field that includes the final state of the computation.

The {anchorName names}`Monad` instance for {anchorTerm names}`EST ε σ` requires {anchorName names}`pure` and {anchorName names}`bind`.
Just as with {anchorName State (module:=Examples.Monads)}`State`, the implementation of {anchorName names}`pure` for {anchorName names}`EST` accepts an initial state and returns it unchanged, and just as with {anchorName names}`Except`, it returns its argument in the {anchorName names (show := ok)}`EST.Out.ok` constructor:
```anchor printEStateMpure
#print EST.pure
```
```anchorInfo printEStateMpure
protected def EST.pure : {α ε σ : Type} → α → EST ε σ α :=
fun {α ε σ} a s => EST.Out.ok a s
```
{kw}`protected` means that the full name {anchorName printEStateMpure}`EST.pure` is needed even if the {anchorName names}`EST` namespace has been opened.

Similarly, {anchorName names}`bind` for {anchorName names}`EST` takes an initial state as an argument.
It passes this initial state to its first action.
Like {anchorName names}`bind` for {anchorName names}`Except`, it then checks whether the result is an error.
If so, the error is returned unchanged and the second argument to {anchorName names}`bind` remains unused.
If the result was a success, then the second argument is applied to both the returned value and to the resulting state.
```anchor printEStateMbind
#print EST.bind
```
```anchorInfo printEStateMbind
protected def EST.bind : {ε σ α β : Type} → EST ε σ α → (α → EST ε σ β) → EST ε σ β :=
fun {ε σ α β} x f s =>
  match x s with
  | EST.Out.ok a s => f a s
  | EST.Out.error e s => EST.Out.error e s
```

Putting all of this together, {anchorName names}`IO` is a monad that tracks state and errors at the same time.
The collection of available errors is that given by the datatype {anchorName printIOError}`IO.Error`, which has constructors that describe many things that can go wrong in a program.
The state is a type that represents the real world, called {anchorTerm RealWorld}`IO.RealWorld`.
Each basic {anchorName names}`IO` action receives this real world and returns another one, paired either with an error or a result.
In {anchorName names}`IO`, {anchorName names}`pure` returns the world unchanged, while {anchorName names}`bind` passes the modified world from one action into the next action.

Because the entire universe doesn't fit in a computer's memory, the world being passed around is just a representation.
So long as world tokens are not re-used, the representation is safe.
The type {anchorTerm RealWorld}`IO.RealWorld` is a trivial primitive type that does not need any representation at all, because it is only used inside of {anchorName VoidSigma}`Void`.
