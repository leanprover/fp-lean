import Lean.Message
import Lean.Data.PersistentArray

import SubVerso.Examples

open SubVerso.Examples Messages

open Lean Elab Command

syntax withPosition("book" "declaration" "{{{" ws ident ws "}}}" command+ "stop" "book" "declaration") : command

open Lean in
def mkExampleStx (kind : Name) (name : Ident) (lastHeaderToken : Syntax) (commands : Array Command) : MacroM Command := do
  if h : commands.size ≥ 1 then
    `(%example (kind := $(mkIdent <| `FPLean ++ kind)) $(mkIdentFrom lastHeaderToken name.getId true):ident
        $(commands[0])
        $(commands.extract 1 commands.size)*
      %end)
  else
    Macro.throwError "Expected at least one command"

open Lean in
def wrapExampleStx (kind : Name) (name : Ident) (lastHeaderToken : Syntax) (commands : MacroM Command) : MacroM Command := do
  let cmd ← commands
  `(%example +embeddedOnly (kind := $(mkIdent <| `FPLean ++ kind)) $(mkIdentFrom lastHeaderToken name.getId true):ident
      $cmd
    %end)


macro_rules
  | `(book declaration {{{ $name:ident }}}%$tok $decls* stop book declaration) =>
    mkExampleStx `decl name tok decls

book declaration {{{ foo }}}
  def twentyFive : Nat := 25
stop book declaration

/-- info: twentyFive : Nat -/
#guard_msgs in
#check twentyFive

book declaration {{{ foo' }}}
  namespace MyNamespaceIsGreat
  def twentyFive : Nat := 25
  end MyNamespaceIsGreat
stop book declaration

/-- info: MyNamespaceIsGreat.twentyFive : Nat -/
#guard_msgs in
#check MyNamespaceIsGreat.twentyFive

syntax withPosition("bookExample" "{{{" ws ident ws "}}}" colGt term:10 colGt "===>" colGt term:10 "end" "bookExample") : command


macro_rules
  | `(bookExample {{{ $name:ident }}}%$tok $x:term ===> $y:term end bookExample) =>
    wrapExampleStx `inputOutput name tok
      `(#guard_msgs (drop info) in
        #check (rfl : %ex{$(Lean.mkIdent `in)}{$x} = %ex{$(Lean.mkIdent `out)}{$y}))

syntax withPosition("bookExample" ":" term "{{{" ws ident ws "}}}" colGt term:10 colGt "===>" colGt term:10 "end" "bookExample") : command

macro_rules
  | `(bookExample : $type:term {{{ $name:ident }}}%$tok $x:term ===> $y:term end bookExample) =>
    wrapExampleStx `inputOutput name tok
    `(#guard_msgs (drop info) in
      #check (rfl : (%ex{$(Lean.mkIdent `in)}{$x} : $type) = %ex{$(Lean.mkIdent `out)}{$y}))

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

syntax withPosition("bookExample" "type" "{{{" ws ident ws "}}}" colGt term:1 colGt "===>" colGt term:1 "end" "bookExample") : command

macro_rules
  | `(bookExample type {{{ $name:ident }}}%$tok $x:term ===> $y:term end bookExample) =>
    wrapExampleStx `inputOutput name tok
    `(noncomputable example : %ex{$(Lean.mkIdent `out)}{$y} := %ex{$(Lean.mkIdent `in)}{$x})

bookExample type {{{ three }}}
  2 + 1
  ===>
  Nat
end bookExample

bookExample type {{{ listT }}}
  List
  ===>
  Type → Type
end bookExample

syntax withPosition("bookExample" "type" "{{{" ws ident ws "}}}" colGt term:10 colGt "<===" colGt term:0 "end" "bookExample") : command

macro_rules
  | `(bookExample type {{{ $name:ident }}}%$tok $x:term <=== $y:term end bookExample) =>
    wrapExampleStx `inputOutput name tok
    `(noncomputable example : %ex{$(Lean.mkIdent `out)}{$y} := %ex{$(Lean.mkIdent `in)}{$x})

def nats : (min : Nat) -> (howMany : Nat) -> List Nat
  | n, Nat.zero => [n]
  | n, Nat.succ k => n :: nats (Nat.succ n) k

syntax withPosition("expect" "error" "{{{" ws ident ws "}}}" colGt command "message" str "end" "expect") : command
syntax withPosition("expect" "error" "{{{" ws ident ws "}}}" colGt term "message" str "end" "expect") : command

def List.containsBy (xs : List α) (pred : α → Bool) : Bool :=
  xs.find? pred |>.isSome

-- Locally modify a state for the scope of an action, undoing the modification later
def withSavedState [Monad m] [MonadStateOf σ m] [MonadFinally m] (f : σ → σ) (act : m α) := do
  let saved ← get
  set (f saved)
  try
    act
  finally
    set saved

def forgetMessages (st : Lean.Elab.Command.State) : Lean.Elab.Command.State :=
  {st with messages := Lean.MessageLog.empty}

def withEmptyMessageLog
    [Monad m]
    [MonadStateOf Lean.Elab.Command.State m]
    [MonadFinally m] :
    m α → m α :=
  withSavedState forgetMessages

elab_rules : command
  | `(expect error {{{ $name:ident }}} $expr:term message $msg:str end expect) =>
    open Lean.Elab.Command in
    open Lean in
    open Lean.Meta in do
    let hls ←
      withEmptyMessageLog do
        let desiredError := msg.getString
        let cmd ← `(command|%show_term (kind := FPLean.forMessage) $name:ident := $expr)
        elabCommand cmd
        let afterState <- get
        let newMessages := afterState.messages.toList
        let newErrors := newMessages.filter (·.severity == MessageSeverity.error)
        let errStrings <- newErrors.mapM (·.data.toString)
        unless errStrings.containsBy (messagesMatch desiredError) do
          let desired := errStrings.map (· |> repr |>.pretty |>.replace "\\n" "\n")
          let desired := Std.Format.joinSep desired .line
          throwErrorAt msg "The desired error {desiredError} was not found in:\n{desired}"
        pure <| highlighted.getState (← getEnv)
    modifyEnv (highlighted.setState · hls)


elab_rules : command
  | `(expect error {{{ $name:ident }}}%$tok $cmd:command message $msg:str end expect) =>
    open Lean.Elab.Command in
    open Lean in
    open Lean.Meta in do
    let hls ←
      withEmptyMessageLog do
        let desiredError := msg.getString
        let cmd ← Lean.Elab.liftMacroM <| mkExampleStx `forMessage name tok #[cmd]
        elabCommand cmd
        let afterState <- get
        let newMessages := afterState.messages.toList
        let newErrors := newMessages.filter (·.severity == MessageSeverity.error)
        let errStrings <- newErrors.mapM (·.data.toString)
        unless errStrings.containsBy (messagesMatch desiredError) do
          let desired := errStrings.map (· |> repr |>.pretty |>.replace "\\n" "\n")
          let desired := Std.Format.joinSep desired .line
          throwErrorAt msg "The desired error {desiredError} was not found in:\n{desired}"
        pure <| highlighted.getState (← getEnv)
    modifyEnv (highlighted.setState · hls)


expect error {{{ errorEx1 }}}
  def x : Nat := "I am not a Nat"
message
"Type mismatch
  \"I am not a Nat\"
has type
  String
but is expected to have type
  Nat"
end expect


syntax withPosition("expect" "info" "{{{" ws ident ws "}}}" colGt command "message" str "end" "expect") : command

elab_rules : command
  | `(expect info {{{ $name:ident }}}%$tok $cmd:command message $msg:str end expect) =>
  open Lean.Elab.Command in
  open Lean in
  open Lean.Meta in do
    let hls ←
      withEmptyMessageLog do
        let desiredInfo := msg.getString
        let cmd ← Lean.Elab.liftMacroM <| mkExampleStx `forMessage name tok #[cmd]
        elabCommand cmd
        let afterState <- get
        let newMessages := afterState.messages.toList
        let newInfos := newMessages.filter fun m => m.severity == MessageSeverity.information
        let errStrings <- newInfos.mapM fun err => err.data.toString
        unless errStrings.containsBy (messagesMatch desiredInfo) do
          let desired := errStrings.map (· |> repr |>.pretty |>.replace "\\n" "\n")
          let desired := Std.Format.joinSep desired .line
          throwErrorAt msg "The desired info {repr desiredInfo} was not found in\n{desired}"
        pure <| highlighted.getState afterState.env
    modifyEnv (highlighted.setState · hls)

expect info {{{ infoEx1 }}}
  #check 1 + 2
message
  "1 + 2 : Nat"
end expect

syntax withPosition("expect" "warning" "{{{" ws ident ws "}}}" colGt command "message" str "end" "expect") : command

syntax withPosition("expect" "warning" "{{{" ws ident ws "}}}" colGt term "message" str "end" "expect") : command

elab_rules : command
  | `(expect warning {{{ $name }}}%$tok $cmd:command message $msg:str end expect) =>
    open Lean.Elab Command in
    open Lean in
    open Lean.Meta in do
      let hls ← withEmptyMessageLog do
        let desiredWarning := msg.getString
        let cmd ← liftMacroM <| mkExampleStx `forMessage name tok #[cmd]
        elabCommand cmd
        let afterState <- get
        let newMessages := afterState.messages.toList
        let newWarnings := newMessages.filter (·.severity == MessageSeverity.warning)
        let errStrings <- newWarnings.mapM (·.data.toString)
        unless errStrings.containsBy (messagesMatch desiredWarning) do
          let desired := errStrings.map (· |> repr |>.pretty |>.replace "\\n" "\n")
          let desired := Std.Format.joinSep desired .line
          throwErrorAt msg "The desired warning {desiredWarning} was not found in\n{desired}"
        pure <| highlighted.getState afterState.env
      modifyEnv (highlighted.setState · hls)

elab_rules : command
  | `(expect warning {{{ $name }}} $expr:term message $msg:str end expect) =>
    open Lean.Elab.Command in
    open Lean in
    open Lean.Meta in do
      let hls ← withEmptyMessageLog do
        let desiredWarning := msg.getString
        let cmd ← `(%show_term (kind := FPLean.forMessage) $name:ident := $expr)
        elabCommand cmd
        let afterState <- get
        let newMessages := afterState.messages.toList
        let newWarnings := newMessages.filter (·.severity == MessageSeverity.warning)
        let errStrings <- newWarnings.mapM (·.data.toString)
        unless errStrings.containsBy (messagesMatch desiredWarning) do
          let desired := errStrings.map (· |> repr |>.pretty |>.replace "\\n" "\n")
          let desired := Std.Format.joinSep desired .line
          throwErrorAt msg "The desired warning {desiredWarning} was not found in\n{desired}"
        pure <| highlighted.getState afterState.env
      modifyEnv (highlighted.setState · hls)


/--
A version of `#guard_msgs` that leaves the messages in the log for extraction.

The passthrough parts of the spec are ignored.
-/
syntax (name := checkMsgsCmd)
  (docComment)? "#check_msgs" (ppSpace guardMsgsSpec)? " in" ppLine command : command

/-- Gives a string representation of a message without source position information.
Ensures the message ends with a '\n'. -/
private def messageToStringWithoutPos (msg : Message) : BaseIO String := do
  let mut str ← msg.data.toString
  unless msg.caption == "" do
    str := msg.caption ++ ":\n" ++ str
  if !("\n".isPrefixOf str) then str := " " ++ str
  match msg.severity with
  | MessageSeverity.information => str := "info:" ++ str
  | MessageSeverity.warning     => str := "warning:" ++ str
  | MessageSeverity.error       => str := "error:" ++ str
  if str.isEmpty || str.back != '\n' then
    str := str ++ "\n"
  return str


open Tactic.GuardMsgs in
@[command_elab checkMsgsCmd]
def elabCheckMsgs : CommandElab
  | `(command| $[$dc?:docComment]? #check_msgs%$tk $(spec?)? in $cmd) => do
    let expected : String := (← dc?.mapM (getDocStringText ·)).getD ""
        |>.trim |> removeTrailingWhitespaceMarker
    let (whitespace, ordering, specFn) ← parseGuardMsgsSpec spec?
    let initMsgs ← modifyGet fun st => (st.messages, { st with messages := {} })
    -- do not forward snapshot as we don't want messages assigned to it to leak outside
    withReader ({ · with snap? := none }) do
      -- The `#guard_msgs` command is special-cased in `elabCommandTopLevel` to ensure linters only run once.
      elabCommandTopLevel cmd
    -- collect sync and async messages
    let msgs := (← get).messages ++
      (← get).snapshotTasks.foldl (· ++ ·.get.getAll.foldl (· ++ ·.diagnostics.msgLog) {}) {}
    -- clear async messages as we don't want them to leak outside
    modify ({ · with snapshotTasks := #[] })
    let mut toCheck : MessageLog := .empty
    let mut toPassthrough : MessageLog := .empty
    for msg in msgs.toList do
      match specFn msg with
      | .check => toCheck := toCheck.add msg
      | .drop => pure ()
      | .pass => toPassthrough := toPassthrough.add msg
    let strings ← toCheck.toList.mapM (messageToStringWithoutPos ·)
    let strings := ordering.apply strings
    let res := "---\n".intercalate strings |>.trim
    if messagesMatch (whitespace.apply expected) (whitespace.apply res) then
      -- Passed. Put messages back on the log, downgrading errors to warnings while recording their original status
      modify fun st => { st with messages := initMsgs ++ SubVerso.Highlighting.Messages.errorsToWarnings msgs }
    else
      -- Failed. Put all the messages back on the message log and add an error
      modify fun st => { st with messages := initMsgs ++ msgs }
      let feedback :=
        let diff := Diff.diff (expected.split (· == '\n')).toArray (res.split (· == '\n')).toArray
        Diff.linesToString diff

      logErrorAt tk m!"❌️ Docstring on `#check_msgs` does not match generated message:\n\n{feedback}"
      pushInfoLeaf (.ofCustomInfo { stx := ← getRef, value := Dynamic.mk (GuardMsgFailure.mk res) })
  | _ => throwUnsupportedSyntax

attribute [command_code_action checkMsgsCmd] Tactic.GuardMsgs.guardMsgsCodeAction

/-- info: 5 -/
#check_msgs in
#eval 5

syntax withPosition("expect" "eval" "info" "{{{" ws ident ws "}}}" colGt term "message" str "end" "expect") : command

elab_rules : command
  | `(expect eval info {{{ $name:ident }}}%$tok $expr:term message $msg:str end expect) =>
    open Lean Elab Command in
    open Lean.Meta in do
    let hls ←
      withEmptyMessageLog do
        let desiredInfo := msg.getString
        let cmd ← liftMacroM <| wrapExampleStx `evalInfo name tok `(#eval %ex{$(mkIdent `in)}{$expr})
        elabCommand cmd
        let afterState <- get
        let newMessages := afterState.messages.toList
        let newInfos := newMessages.filter fun m => m.severity == MessageSeverity.information
        let errStrings <- newInfos.mapM fun err => err.data.toString
        unless errStrings.containsBy (messagesMatch desiredInfo) do
          let desired := errStrings.map (· |> repr |>.pretty |>.replace "\\n" "\n")
          let desired := Std.Format.joinSep desired .line
          throwErrorAt msg "The desired info {repr desiredInfo} was not found in\n{desired}"
        pure <| highlighted.getState afterState.env
    modifyEnv (highlighted.setState · hls)

expect eval info {{{ foo'' }}}
  IO.println "hej" >>= fun _ => IO.println "med dig"
message
"hej
med dig"
end expect



syntax withPosition("evaluation" "steps" "{{{" ws ident ws "}}}" sepBy1(colGe term, "===>") "end" "evaluation" "steps"): command

elab_rules : command
  | `(evaluation steps {{{ $name }}}%$tok $[ $exprs ]===>* end evaluation steps) =>
    open Lean Elab Command Term in
    open Lean.Meta in do
      let mut current : Option Syntax := none
      for item in exprs do
        if let some v := current then
          runTermElabM fun _ => withDeclName name.raw.getId do
            let x <- elabTerm item.raw none
            let y <- elabTerm v none
            synthesizeSyntheticMVarsNoPostponing
            unless (← isDefEq x y) do
              throwError "Example reduction step {y} ===> {x} is incorrect"
        current := some item.raw
      let named : Array Term ← exprs.mapIdxM fun i e =>
        `(%ex{$(mkIdent s!"step{i}".toName)}{$e})
      let cmd ← liftMacroM <| wrapExampleStx `evalSteps name tok `(noncomputable example := [$named,*])
      elabCommand cmd


evaluation steps {{{ fooSteps }}}
  1 + 1 + 2
  ===>
  2 + 2
  ===>
  4
end evaluation steps

syntax withPosition("evaluation" "steps" "-" noWs &"check" "{{{" ws ident ws "}}}" sepBy1(colGe term, "===>") "end" "evaluation" "steps"): command

elab_rules : command
  | `(evaluation steps -check {{{ $name }}}%$tok $[ $exprs ]===>* end evaluation steps) =>
    open Lean Elab Command Term in
    open Lean.Meta in do
      let mut current : Option Syntax := none
      for item in exprs do
        if let some v := current then
          runTermElabM fun _ => withDeclName name.raw.getId do
            let _ <- elabTerm item.raw none
            let _ <- elabTerm v none
            synthesizeSyntheticMVarsNoPostponing
        current := some item.raw
      let named : Array Term ← exprs.mapIdxM fun i e =>
        `(%ex{$(mkIdent s!"step{i}".toName)}{$e})
      let cmd ← liftMacroM <| wrapExampleStx `evalSteps name tok `(noncomputable example := [$named,*])
      elabCommand cmd


syntax withPosition("evaluation" "steps" ":" term "{{{" ws ident ws "}}}" sepBy1(colGe term, "===>") "end" "evaluation" "steps"): command
elab_rules : command
  | `(evaluation steps : $ty {{{ $name }}}%$tok $[ $exprs ]===>* end evaluation steps) =>
    open Lean Elab Command Term in
    open Lean.Meta in do
    let cmd ← runTermElabM fun _ => do
      let expected <- withDeclName name.raw.getId <|
        elabType ty <* synthesizeSyntheticMVarsNoPostponing

      let mut current : Option Syntax := none
      for item in exprs do
        if let some v := current then
          withDeclName name.raw.getId do
            let x <- elabTerm item.raw (some expected)
            let y <- elabTerm v (some expected)
            synthesizeSyntheticMVarsNoPostponing
            unless (← isDefEq x y) do
              throwError "Example reduction step {y} ===> {x} is incorrect\n----------\n\t {(← whnf y)}\n ≠\n\t {(← whnf x)}\n----------\n\t {(← reduceAll y)}\n ≠\n\t {(← reduceAll x)}"
        current := some item.raw
      let named : Array Term ← exprs.mapIdxM fun i e =>
        `((%ex{$(mkIdent s!"step{i}".toName)}{$e} : $ty))
      liftMacroM <| wrapExampleStx `evalSteps name tok `(noncomputable example := [$named,*])
    elabCommand cmd

evaluation steps : IO Unit {{{ thingy }}}
  let x := 5; IO.println s!"{x}"
  ===>
  IO.println "5"
end evaluation steps

declare_syntax_cat eqSteps

syntax term : eqSteps
syntax term "={" docComment "}=" eqSteps : eqSteps
syntax term "={" docComment term "}=" eqSteps : eqSteps

syntax withPosition("equational" "steps" "{{{" ws ident ws "}}}" (colGe eqSteps) "stop" "equational" "steps") : command
syntax withPosition("equational" "steps" ":" term "{{{" ws ident ws "}}}" (colGe eqSteps) "stop" "equational" "steps") : command

open Lean Elab Parser Command in
inductive Steps where
  | done : Term → Steps
  | cons : Term → TSyntax ``docComment → Option Term → Steps → Steps
deriving Inhabited

open Lean Elab Parser Command in
def Steps.forM [Monad m] (todo : Steps) (forStep : Term × TSyntax ``docComment × Option Term × Term → m Unit) : m Unit :=
  match todo with
  | .done _ => pure ()
  | .cons e1 txt why (.done e2) => forStep (e1, txt, why, e2)
  | .cons e1 txt why (.cons e2 txt2 why2 more) => do
    forStep (e1, txt, why, e2)
    forM (.cons e2 txt2 why2 more) forStep

open Lean Elab Parser Command in
instance : ForM m Steps (Term × TSyntax ``docComment × Option Term × Term) where
  forM := Steps.forM

open Lean Elab Parser Command in
instance : ForIn m Steps (Term × TSyntax ``docComment × Option Term × Term) where
  forIn := ForM.forIn

partial def getSteps [Monad m] [MonadError m] [MonadQuotation m] : Lean.Syntax → m Steps
  | `(eqSteps|$t:term) => pure (.done t)
  | `(eqSteps|$t:term ={ $c }= $more:eqSteps) => do
    return (.cons t c none (← getSteps more))
  | `(eqSteps|$t:term ={ $c $why:term }= $more:eqSteps) => do
    return (.cons t c (some why) (← getSteps more))
  | other => throwError "Invalid equational steps {other}"



open Internals in
open Lean Elab Command in
def Steps.asCmd [Monad m] [MonadQuotation m] (ty? : Option Term) (ss : Steps) : m Command := do
  let tms ← go 0 ss
  if let some ty := ty? then
    `(noncomputable example : List $ty := [$tms,*])
  else
    `(noncomputable example := [$tms,*])
where
  go (n : Nat) : Steps → m (Array Term)
    | .cons e txt _ ss => do
      let more ← go (n + 1) ss
      let me ←
        `(let _ : Unit := %ex{$(mkIdent s!"why{n}".toName)}{$txt:docComment ()};
          %ex{$(mkIdent s!"step{n}".toName)}{$e})
      pure <| more.push me
    | .done e => do
      let me ← `(%ex{$(mkIdent s!"step{n}".toName)}{$e})
      pure #[me]

open Lean in
def elabEquationalSteps (name : TSyntax `ident) (tok : Syntax) (stepStx : TSyntax `eqSteps) (ty : Option (TSyntax `term)) :=
  open Lean Elab Command Term in
  open Lean.Meta in do
  let cmd ← runTermElabM fun _ => do
    let expected ← match ty with
      | none => pure none
      | some t => some <$> withDeclName name.raw.getId (elabType t)
    let exprs ← getSteps stepStx
    if let .done e := exprs then withDeclName name.raw.getId do
      let _ ← elabTerm e none

    for (e1, txt, why, e2) in exprs do
      withDeclName name.raw.getId do
        let x ← elabTermEnsuringType e1 expected
        let y ← elabTermEnsuringType e2 expected
        synthesizeSyntheticMVarsNoPostponing
        match why with
        | none =>
          unless (← isDefEq x y) do
            throwErrorAt txt "Example equational step {y} ===> {x} is incorrect\n----------\n\t {(← whnf y)}\n ≠\n\t {(← whnf x)}\n----------\n\t {(← reduceAll y)}\n ≠\n\t {(← reduceAll x)}"
        | some p =>
          let e1' : TSyntax `term := ⟨e1⟩
          let e2' : TSyntax `term := ⟨e2⟩
          let stepTypeSyntax ←
            match ty with
            | none => `($e1' = $e2')
            | some t => `(($e1' : $t) = ($e2' : $t))
          let eq ← elabTermEnsuringType stepTypeSyntax (some (mkSort Level.zero))
          let _ ← elabTermEnsuringType p (some eq)
          synthesizeSyntheticMVarsNoPostponing
    liftMacroM <| wrapExampleStx `eqSteps name tok (exprs.asCmd ty)
  elabCommand cmd


elab_rules : command
  | `(equational steps {{{ $name }}}%$tok $stepStx:eqSteps stop equational steps) =>
    elabEquationalSteps name tok stepStx none
  | `(equational steps : $ty {{{ $name }}}%$tok $stepStx:eqSteps stop equational steps) =>
    elabEquationalSteps name tok stepStx (some ty)

equational steps {{{ fooStepsEqs }}}
  1 + 1
  ={
  /-- Compute forwards -/
  by rfl
  }=
  2
  ={
  /-- Compute backwards -/
  }=
  0 + 2
stop equational steps

def zipSameLength : List α → List β → Option (List (α × β))
  | [], [] => some []
  | x :: xs, y :: ys => do pure ((x, y) :: (← zipSameLength xs ys))
  | _, _ => none

def Lean.Name.last : Lean.Name -> Option String
  | Lean.Name.str _ s => some s
  | _ => none

syntax "similar " "datatypes" ident ident : command
elab_rules : command
  | `(similar datatypes $C1:ident $C2:ident) =>
    open Lean.Elab.Command in
    open Lean.Environment in
    open Lean in do
      let e := (<- get).env
      let t1 ← runTermElabM fun _ => realizeGlobalConstNoOverloadWithInfo C1
      let t2 ← runTermElabM fun _ => realizeGlobalConstNoOverloadWithInfo C2
      let i1 <- match (e.find? t1).get! with
      | ConstantInfo.inductInfo i => pure i
      | _ => throwErrorAt C1 "Not an inductive type: {t1}"
      let i2 <- match (e.find? t2).get! with
      | ConstantInfo.inductInfo i => pure i
      | _ => throwErrorAt C2 "Not an inductive type: {t2}"
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


syntax withPosition("discarding" (colGe command)* "stop " "discarding") : command
open Lean Elab Command in
elab_rules : command
  | `(discarding $cmds* stop discarding) => do
    let hls ←
      withoutModifyingEnv do
        for c in cmds do
          elabCommand c
        pure <| highlighted.getState (← getEnv)
    modifyEnv (highlighted.setState · hls)

namespace Foo
  inductive List (α : Type) : Type where
    | nil : List α
    | cons : α -> List α -> List α
end Foo

similar datatypes List Foo.List
