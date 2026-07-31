/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module

public import Expect.Basic
import Expect.Buffer
import Expect.Pty

public section

/-!
Running a script, which drives one program at a time and records what happened.

Every step that touches the program takes all of the output it has produced, so what is held
between steps is only what has not been accounted for in the transcript yet.
-/

namespace Expect

private structure State where
  /-- Output received from the terminal that is not yet part of the transcript. -/
  received : Buffer := {}
  /-- Whether the terminal has closed. -/
  ended : Bool := false
  /-- Whether the program has been waited for. -/
  finished : Bool := false
  segments : Transcript := #[]
deriving Inhabited

private def push (segments : Transcript) (text : String) (role : Role) : Transcript :=
  if text.isEmpty then segments
  else if let some last := segments.back? then
    if last.role = role then
      segments.set! (segments.size - 1) { last with text := last.text ++ text }
    else segments.push ⟨text, role⟩
  else segments.push ⟨text, role⟩

private def record (state : IO.Ref State) (text : String) (role : Role) : IO Unit :=
  state.modify fun s => { s with segments := push s.segments text role }

/-- Checks that the program has not already been waited for. -/
private def running (state : IO.Ref State) : IO Unit := do
  if (← state.get).finished then
    throw <| .userError "The program has already terminated"

/--
Why waiting for text stopped, as the start of a sentence that names the text.

A program that has gone leaves nothing to wait for, so the reason names what became of it.
-/
private def stopped (state : IO.Ref State) (child : Pty.Child) : IO String := do
  unless (← state.get).ended do return "Timed out waiting for"
  match ← child.wait 50 with
  | some code => return s!"The program exited with code {code} before writing"
  | none => return "The program closed its terminal before writing"

/-- Output received but not yet accounted for in the transcript. -/
private def unused (state : IO.Ref State) : IO String := do
  return (← state.get).received.text

/-- Records everything received so far as output of the program. -/
private def useAll (state : IO.Ref State) : IO Unit := do
  let (text, rest) := (← state.get).received.flush
  record state text .output
  state.modify ({ · with received := rest })

/--
Takes everything the program has written, waiting until `deadline` for the first of it, and reports
whether anything arrived.

A program that writes without pause is read until the deadline.
-/
private def receive (state : IO.Ref State) (child : Pty.Child) (deadline : Nat) : IO Bool := do
  if (← state.get).ended then return false
  let now ← IO.monoMsNow
  if !(← child.ready (UInt32.ofNat (deadline - now))) then return false
  let mut got := false
  repeat
    let bytes ← child.read
    if bytes.isEmpty then
      state.modify ({ · with ended := true })
      break
    let some received := (← state.get).received.push bytes
      | throw <| .userError "The program wrote bytes that are not text"
    state.modify ({ · with received })
    got := true
    if (← IO.monoMsNow) ≥ deadline then break
    unless ← child.ready 0 do break
  return got

/--
Waits for the program to write `pattern`, and returns what it wrote before it, or `none` if the
program did not write it in time.

The occurrence of the pattern is consumed along with the text before it.
-/
private def await (state : IO.Ref State) (child : Pty.Child) (pattern : String)
    (timeoutMs : UInt32) : IO (Option String) := do
  let deadline := (← IO.monoMsNow) + timeoutMs.toNat
  repeat
    if let some (before, rest) := (← state.get).received.take pattern then
      state.modify ({ · with received := rest })
      return some before
    if (← state.get).ended then break
    if (← IO.monoMsNow) ≥ deadline then break
    discard <| receive state child deadline
  return none

/--
How long to read for before asking again whether the program has terminated.
-/
private def checkEveryMs : Nat := 20

/--
Reads until the program has terminated and its terminal holds nothing more, or until `deadline`,
and reports the exit code if it terminated.

Reading continues while the program is on its way out, so that a program with output still to write
can finish writing it and reach its own exit.
-/
private def settle (state : IO.Ref State) (child : Pty.Child) (deadline : Nat) :
    IO (Option UInt32) := do
  let mut code ← child.wait 0
  repeat
    let now ← IO.monoMsNow
    if now ≥ deadline then break
    discard <| receive state child (min deadline (now + checkEveryMs))
    if code.isNone then code ← child.wait 0
    if (← state.get).ended then break
    if code.isSome && !(← child.ready 0) then break
  -- The terminal can close before the program has been reaped
  if code.isNone then
    let now ← IO.monoMsNow
    if now < deadline then
      code ← child.wait (UInt32.ofNat (deadline - now))
  return code

private def step (state : IO.Ref State) (child : Pty.Child) : Directive → IO Unit
  | .expect text timeoutMs => do
    running state
    let some before ← await state child text timeoutMs
      | throw <| .userError
          s!"{← stopped state child} {repr text}.\nReceived: {repr (← unused state)}"
    record state (before ++ text) .output
  | .send text timeoutMs => do
    running state
    -- Whatever the program has written by now came before what is typed
    useAll state
    child.write (text ++ "\n") timeoutMs
    let some before ← await state child (text ++ "\n") timeoutMs
      | throw <| .userError
          s!"{← stopped state child} the terminal's echo of {repr text}.\n\
             Received: {repr (← unused state)}"
    record state before .output
    record state (text ++ "\n") .input
  | .sendEOF timeoutMs => do
    running state
    -- Whatever the program has written by now came before the end of input
    useAll state
    child.writeEOF timeoutMs
  | .exit timeoutMs => do
    discard <| finish state timeoutMs
  | .exitCode code timeoutMs => do
    let actual ← finish state timeoutMs
    if actual != code then
      throw <| .userError s!"Expected exit code {code}, but got {actual}"
where
  /-- Waits for the program to terminate, and reports its exit code. -/
  finish (state : IO.Ref State) (timeoutMs : UInt32) : IO UInt32 := do
    running state
    let code? ← settle state child ((← IO.monoMsNow) + timeoutMs.toNat)
    useAll state
    state.modify ({ · with finished := true })
    let some code := code?
      | child.kill
        child.close
        throw <| .userError s!"The program did not terminate within {timeoutMs} ms"
    child.close
    unless (← state.get).received.incomplete.isEmpty do
      throw <| .userError "The program's output ends partway through a character"
    return code

/--
Runs a session in `cwd` and returns its transcript, or the reason it failed together with the
transcript up to that point.

The program's environment is the current one, with the names in `envUnset` removed and the
`"NAME=VALUE"` entries of `envOverrides` added.
-/
def run (session : Session) (cwd : System.FilePath)
    (envOverrides : Array String := #[]) (envUnset : Array String := #[]) :
    IO (Except (String × Transcript) (Transcript)) := do
  let state : IO.Ref State ← IO.mkRef {}
  let child ←
    try Pty.Child.spawn session.command session.args cwd envOverrides envUnset
    catch e => return .error (toString e, #[])
  record state (" ".intercalate (session.command :: session.args.toList)) .command
  try
    for directive in session.script do
      step state child directive
    unless (← state.get).finished do
      child.kill
      child.close
      throw <| .userError "The script ends without waiting for the program to exit"
    return .ok (← state.get).segments
  catch e =>
    unless (← state.get).finished do
      child.kill
      child.close
    return .error (toString e, (← state.get).segments)
