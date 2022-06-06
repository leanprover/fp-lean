import Lean
import Lean.Message

syntax withPosition("book" "declaration" "{{{" ws ident ws "}}}" (command*) "stop" "book" "declaration") : command

elab_rules : command
  | `(book declaration {{{ $name:ident }}} $decls* stop book declaration) => do
    for decl in decls do
      Lean.Elab.Command.elabCommand decl

book declaration {{{ foo }}}
  def twentyFive : Nat := 25
stop book declaration

#check twentyFive

book declaration {{{ foo }}}
  namespace MyNamespaceIsGreat
  def twentyFive : Nat := 25
  end MyNamespaceIsGreat
stop book declaration

#check MyNamespaceIsGreat.twentyFive

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

syntax withPosition("bookExample" ":" term "{{{" ws ident ws "}}}" colGt term:60 colGt "===>" colGt term:60 "end bookExample") : command

elab_rules : command
  | `(bookExample : $type:term {{{ $name:ident }}} $x:term ===> $y:term end bookExample) =>
    open Lean.Elab.Command in
    open Lean.Elab.Term in
    open Lean.Meta in liftTermElabM `bookExample do
      let t ← elabTerm type none
      let x ← elabTerm x (some t)
      let y ← elabTerm y (some t)
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


syntax withPosition("evaluation" "steps" "{{{" ws ident ws "}}}" sepBy1(colGt term, "===>") "end" "evaluation" "steps"): command
elab_rules : command
  | `(evaluation steps {{{ $name }}} $[ $exprs ]===>* end evaluation steps) =>
    open Lean.Elab.Command in
    open Lean.Elab.Term in
    open Lean in
    open Lean.Meta in do
      let mut current : Option Syntax := none
      for item in exprs do
        if let some v := current then
          liftTermElabM `evaluationSteps do
            let x <- elabTerm item none
            let y <- elabTerm v none
            synthesizeSyntheticMVarsNoPostponing
            unless (← isDefEq x y) do
              throwError "Example reduction step {y} ===> {x} is incorrect"
        current := some item

evaluation steps {{{ foo }}}
  1 + 1 + 2
  ===>
  2 + 2
  ===>
  4
end evaluation steps


def zipSameLength : List α → List β → Option (List (α × β))
  | [], [] => some []
  | x :: xs, y :: ys => do pure ((x, y) :: (← zipSameLength xs ys))
  | _, _ => none

def Lean.Name.last : Lean.Name -> Option String
  | Lean.Name.str _ s _ => some s
  | _ => none

syntax "similar datatypes" ident ident : command
elab_rules : command
  | `(similar datatypes $C1:ident $C2:ident) =>
    open Lean.Elab.Command in
    open Lean.Environment in
    open Lean in do
      let e := (<- get).env
      let t1 := C1.getId
      let t2 := C2.getId
      let i1 <- match (e.find? t1).get! with
        | ConstantInfo.inductInfo i => pure i
        | _ => throwError "Not an inductive type: {t1}"
      let i2 <- match (e.find? t2).get! with
        | ConstantInfo.inductInfo i => pure i
        | _ => throwError "Not an inductive type: {t2}"
      if i1.numParams != i2.numParams then throwError "Param count mismatch"
      if i1.numIndices != i2.numIndices then throwError "Index count mismatch"
      if i1.isRec != i1.isRec then throwError "Recursiveness mismatch"
      let ctors <- match zipSameLength i1.ctors i2.ctors with
        | some v => pure v
        | none => throwError "Different number of constructors"
      for (c1, c2) in ctors do
        let (n1, n2) := (c1.last.get!, c2.last.get!)
        if n1 != n2 then throwError "Constructor name mismatch: {n1} vs {n2}"
        let ctor1 <- match (e.find? c1).get! with
          | ConstantInfo.ctorInfo i => pure i
          | _ => throwError "Not a constructor {c1}"
        let ctor2 <- match (e.find? c2).get! with
          | ConstantInfo.ctorInfo i => pure i
          | _ => throwError "Not a constructor {c2}"
        if ctor1.numFields != ctor2.numFields then throwError "Constructor field count mismatch for {n1}"


namespace Foo
  inductive List (α : Type) : Type where
    | nil : List α
    | cons : α -> List α -> List α
end Foo

similar datatypes List Foo.List
