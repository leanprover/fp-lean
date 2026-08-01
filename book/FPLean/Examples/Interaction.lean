/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public meta import Expect.Run
public meta import FPLean.Examples.Commands
public import Lean.Exception
public import Lean.CoreM
public import Verso.Doc.ArgParse
public import VersoManual

public section

/-!
Sessions with interactive programs.

The body of an {lit}`interaction` block is a script in the `Expect` language, which says what the
program is expected to write and what is typed in response. Elaborating the block runs the script
against the real program, and the transcript that results is what the book shows.
-/

open Lean.Doc.Syntax
open Verso Doc Elab Genre.Manual ArgParse Output Html Log SyntaxUtils
open Lean Elab Term Meta

namespace FPLean

structure InteractionConfig where
  container : Ident
  dir : StrLit
  /-- Whether the transcript begins with the command that started the session. -/
  showCommand : Bool

meta instance [Monad m] [MonadError m] [MonadLiftT CoreM m] : FromArgs InteractionConfig m where
  fromArgs :=
    InteractionConfig.mk <$> .positional `container .ident <*> .positional `dir .strLit <*>
      .flag `showCommand true

private meta def roleName : Expect.Role → String
  | .command => "command"
  | .output => "output"
  | .input => "input"

/--
Whether a line separates a script from the transcript that it is expected to produce.
-/
private meta def isSeparator (line : String) : Bool :=
  let dashes := line.dropWhile ' ' |>.dropEndWhile Char.isWhitespace
  !(dashes.drop 2).isEmpty && dashes.all '-'

/--
Puts a block's indentation back on each line of text that it is compared against.
-/
private meta def indentBy (indent : String) (text : String) : String :=
  if indent.isEmpty then text
  else
    text.lines.map indentLine |>.toList |> String.join
where
  indentLine line :=
    let line := line.toString
    if line.isEmpty then "\n" else indent ++ line ++ "\n"

private unsafe def evalSessionUnsafe (stx : Syntax) : TermElabM (Option Expect.Session) := do
  let type := Lean.mkConst ``Expect.Session
  let e ← withoutErrToSorry <| Elab.Term.elabTerm stx (some type)
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  if e.hasSorry || e.hasExprMVar then return none
  some <$> evalExpr Expect.Session type e

@[implemented_by evalSessionUnsafe]
private meta opaque evalSession (stx : Syntax) : TermElabM (Option Expect.Session)

block_extension Block.interaction (segments : Array (String × String)) where
  traverse _ _ _ := pure none
  data := toJson segments
  toTeX := none
  toHtml := some fun _ _ _ data _ => do
    let .ok (segments : Array (String × String)) := fromJson? data
      | reportError s!"Failed to deserialize interaction:\n{data}"
        return .empty
    let pieces : Array Html := segments.map fun (content, who) =>
      {{ <code class={{who}}>{{content}}</code> }}
    pure {{
      <div class="interaction">{{pieces}}</div>
    }}
  extraCss := [
    r#"
.interaction {
  overflow-x: auto;
}
.interaction > * {
  display: inline;
  white-space: pre;
}
.interaction .command::before {
  content: "$ ";
  font-weight: 600;
}
.interaction .input {
  font-weight: 600;
  color: #0000c0;
}

div.paragraph > .interaction:not(:first-child) {
  margin-top: 0.5rem;
}

div.paragraph > .interaction:not(:last-child) {
  margin-bottom: 0.5rem;
}
"#
  ]

@[code_block_expander interaction]
meta def interaction : CodeBlockExpander
  | args, str => do
    let {container, dir, showCommand} ← parseThe InteractionConfig args
    let directory : System.FilePath := dir.getString
    unless directory.isRelative do
      throwErrorAt dir "Relative directory expected, got '{dir.getString}'"

    -- Before the script, so that a failure here does not leave later blocks without a container
    let c ← Commands.ensureContainer container
    let cwd := c.workingDirectory / "examples" / directory
    IO.FS.createDirAll cwd

    let (script, expected, indent) ← blockParts str
    let stx ← parseStrLitAsCategory `term script
    if stx.isMissing then return #[]
    let some session ← evalSession stx
      | throwErrorAt str "Could not evaluate the script"

    let (envOverrides, envUnset) ← Commands.containerEnvEntries

    match ← Expect.run session cwd envOverrides envUnset with
    | .error (why, transcript) =>
      throwErrorAt str "{why}\nTranscript:{indentD transcript.toString}"
    | .ok transcript =>
      let shown := if showCommand then transcript else transcript.filter (!·.role matches .command)
      let actual := shown.toString
      logSilentInfo actual
      discard <| ExpectString.expectString "transcript" expected (indentBy indent actual)
        (preEq := (·.trimAsciiEnd.copy))
      let segments := shown.map fun ⟨content, who⟩ =>
        (if who matches .command then content ++ "\n" else content, roleName who)
      return #[← ``(Block.other (Block.interaction $(quote segments)) #[])]
where
  /--
  The script that a block contains, the transcript that it is expected to produce, and the
  indentation that the block carries in the source.

  The two parts are string literals that point at their own part of the block, so that errors and
  replacements land where they belong. A block that is nested in a list or an admonition is
  indented in the source but not in its contents, and the parts keep the indentation, so that a
  replacement stays nested where the author put it.
  -/
  blockParts (str : StrLit) : DocElabM (StrLit × StrLit × String) := do
    let some blockStart := str.raw.getPos?
      | throwErrorAt str "Expected a block with a source position"
    let blockStop := str.raw.getTailPos?.getD blockStart
    let text ← getFileMap
    let sourceLines := (blockStart.extract text.source blockStop).splitOn "\n"
    let contentLines := str.getString.splitOn "\n"
    unless sourceLines.length == contentLines.length do
      throwErrorAt str "The source of this block and its contents do not agree line for line"
    let indent :=
      (sourceLines.zip contentLines).findSome? fun (source, content) =>
        if content.isEmpty then none else some (source.take (source.length - content.length)).copy
    let mut offset := 0
    let mut parts := none
    for (source, content) in sourceLines.zip contentLines do
      if isSeparator content then
        parts := some (offset, offset + source.utf8ByteSize + 1)
        break
      offset := offset + source.utf8ByteSize + 1
    let some (scriptEnd, transcriptStart) := parts
      | throwErrorAt str
          "Expected a line of three or more dashes, separating the script from the transcript that \
           it is expected to produce"
    let offsetOf (offset : Nat) : String.Pos.Raw := ⟨blockStart.byteIdx + offset⟩
    return (part blockStart (offsetOf scriptEnd) text,
            part (offsetOf transcriptStart) blockStop text,
            indent.getD "")
  /-- The part of a block between two positions, as a string literal that points at it. -/
  part (start stop : String.Pos.Raw) (text : FileMap) : StrLit :=
    Syntax.mkStrLit (start.extract text.source stop)
      (info := .original "".toRawSubstring start "".toRawSubstring stop)
