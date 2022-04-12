import Lean
import Lean.Message

syntax withPosition("bookExample" "{{{" ws ident ws "}}}" colGt term:60 colGt "===>" colGt term:60 "end bookExample") : command

elab_rules : command
  | `(bookExample {{{ $name:ident }}} $x:term ===> $y:term end bookExample) =>
    open Lean.Elab.Command in
    open Lean.Elab.Term in
    open Lean.Meta in liftTermElabM `bookExample do
      let x ← elabTerm x none
      let y ← elabTerm y none
      synthesizeSyntheticMVarsNoPostponing
      unless (← isDefEq x y) do
        throwError "Expected {y}, but got {← reduce x}"

bookExample {{{ one }}}
  1
  ===>
  1
end bookExample

bookExample {{{ two }}}
  1 + 1
  ===>
  2
end bookExample

syntax withPosition("bookExample" "type" "{{{" ws ident ws "}}}" colGt term:60 colGt "===>" colGt term:60 "end bookExample") : command

elab_rules : command
  | `(bookExample type {{{ $name:ident }}} $x:term ===> $y:term end bookExample) =>
    open Lean.Elab.Command in
    open Lean.Elab.Term in
    open Lean.Meta in liftTermElabM `bookExample do
      let x ← elabTerm x none
      let xType ← inferType x
      let y ← elabTerm y none
      synthesizeSyntheticMVarsNoPostponing
      unless (← isDefEq xType y) do
        throwError "Expected the type {y}, but got {← reduce xType}"

bookExample type {{{ three }}}
  2 + 1
  ===>
  Nat
end bookExample


def nats : (min : Nat) -> (howMany : Nat) -> List Nat
  | n, Nat.zero => [n]
  | n, Nat.succ k => n :: nats (Nat.succ n) k

def Std.PersistentArray.getN! [Inhabited α] (arr : Std.PersistentArray α) (howMany : Nat) : List α := nats 0 howMany |> List.map (fun i => arr.get! i)


syntax withPosition("expect" "error" "{{{" ws ident ws "}}}" colGt command "message" str "end" "expect") : command
syntax withPosition("expect" "error" colGt command "message" str "end" "expect") : command

macro_rules
  | `(expect error {{{ $name:ident }}} $cmd:command message $msg:str end expect) =>
    `(expect error  $cmd:command message $msg:str end expect)


elab_rules : command
  | `(expect error $cmd:command message $msg:str end expect) =>
    open Lean.Elab.Command in
    open Lean in
    open Lean.Meta in do
      let savedState <- get
      match msg.isStrLit? with
      | none => throwError "Desired message must be a string, but got {msg}"
      | some desiredError => do
        try
          elabCommand cmd
          let afterState <- get
          let lengthDifference := afterState.messages.msgs.size - savedState.messages.msgs.size
          let newMessages := afterState.messages.msgs.getN! lengthDifference
          let newErrors := newMessages.filter fun m => m.severity == MessageSeverity.error
          let errStrings <- newErrors.mapM fun err => err.data.toString
          unless errStrings.contains desiredError do
            throwError "The desired error {desiredError} was not found in\n{errStrings}"
        finally
          set savedState

expect error {{{ errorEx1 }}}
  def x : Nat := "I am not a Nat"
message
"type mismatch
  \"I am not a Nat\"
has type
  String : Type
but is expected to have type
  Nat : Type"
end expect


syntax withPosition("expect" "info" "{{{" ws ident ws "}}}" colGt command "message" str "end" "expect") : command
syntax withPosition("expect" "info" colGt command "message" str "end" "expect") : command

macro_rules
  | `(expect info {{{ $name:ident }}} $cmd:command message $msg:str end expect) =>
    `(expect info $cmd:command message $msg:str end expect)

elab_rules : command
  | `(expect info $cmd:command message $msg:str end expect) =>
    open Lean.Elab.Command in
    open Lean in
    open Lean.Meta in do
      let savedState <- get
      match msg.isStrLit? with
      | none => throwError "Desired message must be a string, but got {msg}"
      | some desiredInfo => do
        try
          elabCommand cmd
          let afterState <- get
          let lengthDifference := afterState.messages.msgs.size - savedState.messages.msgs.size
          let newMessages := afterState.messages.msgs.getN! lengthDifference
          let newInfos := newMessages.filter fun m => m.severity == MessageSeverity.information
          let errStrings <- newInfos.mapM fun err => err.data.toString
          unless errStrings.contains desiredInfo do
            throwError "The desired info {repr desiredInfo} was not found in\n{List.map repr errStrings}"
        finally
          set savedState

expect info {{{ infoEx1 }}}
  #check 1 + 2
message
  "1 + 2 : Nat"
end expect
