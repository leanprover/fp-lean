/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public section
/-!
The script language for terminal sessions, and the transcripts that running one produces.
-/

namespace Expect

/-- Who produced a part of a transcript. -/
inductive Role where
  /-- The command that started the session. -/
  | command
  /-- Text written by the program. -/
  | output
  /-- Text typed by the user. -/
  | input
deriving Repr, DecidableEq, Inhabited

/-- A run of text in a transcript, all of it from the same source. -/
structure Segment where
  text : String
  role : Role
deriving Repr, Inhabited

abbrev Transcript := Array Segment

/--
A step of a terminal session.

The timeouts are in milliseconds, and each bounds its own step. A program that takes its time to
respond is waited for by the step that expects the response.
-/
inductive Directive where
  /-- Waits for the program to write the given text. -/
  | expect (text : String) (timeoutMs : UInt32 := 1500)
  /-- Types a line, and waits for the terminal to echo it into the transcript. -/
  | send (text : String) (timeoutMs : UInt32 := 1500)
  /-- Types the character that ends the program's input, which the transcript shows nothing for. -/
  | sendEOF (timeoutMs : UInt32 := 1500)
  /-- Waits for the program to terminate, whatever its exit code. -/
  | exit (timeoutMs : UInt32 := 1500)
  /-- Waits for the program to terminate with the given exit code. -/
  | exitCode (code : UInt32) (timeoutMs : UInt32 := 1500)
deriving Repr, Inhabited

/-- A terminal session: one program, and the steps that drive it. -/
structure Session where
  /-- The program to run, which is looked up on the `PATH` that it is given. -/
  command : String
  /-- The arguments to pass to the program. -/
  args : Array String := #[]
  /-- The steps to take, in order. -/
  script : Array Directive
deriving Repr, Inhabited

/--
The text of a transcript, with each line marked by where it came from: `$` for the command that
started the session, `>` for what was typed, and `<` for what the program wrote.
-/
def Transcript.toString (segments : Transcript) : String := Id.run do
  let mut out := ""
  for ⟨text, role⟩ in segments do
    out := out ++ pre role text
  return out
where
  /-- A line that has no text carries its mark alone, so that no line ends in a space. -/
  line (mark : String) (text : String) : String :=
    if text.isEmpty then mark ++ "\n" else s!"{mark} {text}\n"
  pre
    | .command, txt => line "$" txt
    | .output, txt => txt.lines.map (line "<" ·.toString) |>.toList |> String.join
    | .input, txt => txt.lines.map (line ">" ·.toString) |>.toList |> String.join
