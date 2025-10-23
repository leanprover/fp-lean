import SubVerso.Examples
import Lean.Data.NameMap
import Lean.DocString.Syntax
import VersoManual
import FPLean.Examples.Commands
import FPLean.Examples.OtherLanguages

open Lean (NameMap MessageSeverity)
open Lean.Doc.Syntax

namespace FPLean


open Verso Doc Elab Genre.Manual ArgParse Code Highlighted WebAssets Output Html Log Code External
open SubVerso.Highlighting
open SubVerso.Examples.Messages
open Lean
open Std

open InlineLean (FileType)



private def oneCodeStr [Monad m] [MonadError m] (inlines : Array (TSyntax `inline)) : m StrLit := do
  let #[code] := inlines
    | (if inlines.size == 0 then (throwError ·) else (throwErrorAt (mkNullNode inlines) ·)) "Expected one code element"
  let `(inline|code($code)) := code
    | throwErrorAt code "Expected a code element"
  return code

private def oneCodeStr? [Monad m] [MonadError m] [MonadLog m] [AddMessageContext m] [MonadOptions m]
    (inlines : Array (TSyntax `inline)) : m (Option StrLit) := do
  let #[code] := inlines
    | if inlines.size == 0 then
        logError "Expected a code element"
      else
        logErrorAt (mkNullNode inlines) "Expected one code element"
      return none
  let `(inline|code($code)) := code
    | logErrorAt code "Expected a code element"
      return none
  return some code


private def oneCodeName [Monad m] [MonadError m] (inlines : Array (TSyntax `inline)) : m Ident := do
  let code ← oneCodeStr inlines
  let str := code.getString
  let name := if str.contains '.' then str.toName else Name.str .anonymous str
  return mkIdentFrom code name


section
open Elab Term

variable {m} [Monad m] [MonadReaderOf Term.Context m] [MonadLiftT TermElabM m] [MonadLiftT MetaM m] [MonadMCtx m] [MonadError m] [MonadLCtx m]

structure ExampleModule (module : Name) where

partial def currentExampleModule : m Name := do
  let ctx ← readThe Term.Context
  let mut theName : Name := .anonymous
  for (_, fv) in ctx.sectionFVars do
    let t ← Meta.inferType fv >>= instantiateExprMVars
    let t ← Meta.whnf t
    if t.isAppOfArity' ``ExampleModule 1 then
      let nameExpr := t.getArg! 0
      let nameExpr ← Meta.reduceAll nameExpr
      theName ← nameFromExpr nameExpr
  if theName.isAnonymous then throwError "No default example module provided with 'example_module'"
  else return theName
where
  nameFromExpr expr : m Name := do
    match_expr expr with
    | Name.anonymous => return .anonymous
    | Name.str x y =>
      if let .lit (.strVal s) := y then
        return .str (← nameFromExpr x) s
      else throwError "Not a string literal: {y}"
    | Name.num x y =>
      if let .lit (.natVal n) := y then
        return .num (← nameFromExpr x) n
      else throwError "Not a natural number literal: {y}"
    | _ => throwError "Failed to reify expression as name: {expr}"

macro "example_module" name:ident : command => `(variable (_ : ExampleModule $(quote name.getId)))

def mod (ref : Syntax) : ArgParse m Ident :=
  (.positional `module .ident <* .done) <|>
  (.lift "Default example module" (mkIdentFrom ref <$> currentExampleModule) <* .done)

def modAndName (ref : Syntax) : ArgParse m (Ident × Ident) :=
  ((·, ·) <$> .positional `module .ident <*> .positional `decl .ident <* .done) <|>
  ((·, ·) <$> .lift "Default example module" (mkIdentFrom ref <$> currentExampleModule) <*> .positional `decl .ident <* .done)


def modAndNameAndSev [MonadLiftT CoreM m] (ref : Syntax) : ArgParse m (Ident × Ident × MessageSeverity) :=
  ((·, ·, ·) <$> .positional `module .ident <*> .positional `decl .ident <*> .positional `severity .messageSeverity) <|>
  ((·, ·, ·) <$> .lift "Default example module" (mkIdentFrom ref <$> currentExampleModule) <*> .positional `decl .ident <*> .positional `severity .messageSeverity)

def modAndNameThen (ref : Syntax) (more : ArgParse m α) : ArgParse m (Ident × Ident × α) :=
  ((·, ·, ·) <$> .positional `module .ident <*> .positional `decl .ident <*> more <* .done) <|>
  ((·, ·, ·) <$> .lift "Default example module" (mkIdentFrom ref <$> currentExampleModule) <*> .positional `decl .ident <*> more <* .done)


def modAndThen (ref : Syntax) (more : ArgParse m α) : ArgParse m (Ident × α) :=
  ((·, ·) <$> .positional `module .ident <*>  more <* .done) <|>
  ((·, ·) <$> .lift "Default example module" (mkIdentFrom ref <$> currentExampleModule) <*> more <* .done)

end

block_extension Block.creativeCommons where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ _ _ =>
      pure {{
        <a rel="license" href="http://creativecommons.org/licenses/by/4.0/">
          <img alt="Creative Commons License" style="border-width:0" src="https://i.creativecommons.org/l/by/4.0/88x31.png" />
        </a>
        <br />
        "This work is licensed under a "
        <a rel="license" href="http://creativecommons.org/licenses/by/4.0/">
          "Creative Commons Attribution 4.0 International License"
        </a>"."
      }}

@[block_command]
def creativeCommons : BlockCommandOf Unit
  | () => do
    ``(Block.other (Block.creativeCommons) #[])

def evalStepsStyle := r#"
div.paragraph > .eval-steps:not(:first-child), div.paragraph > .eval-steps:not(:first-child) > * {
  margin-top: 0.5rem;
}

div.paragraph > .eval-steps:not(:last-child), div.paragraph > .eval-steps:not(:last-child) > * {
  margin-bottom: 0.5rem;
}

.eval-steps .hl.lean.block {
  margin-top: 0.25em;
  margin-bottom: 0.25em;
}

.eval-steps .hl.lean.block:not(:last-child)::after {
  content: "⟹";
  display: block;
  margin-left: 1em;
  font-size: 175%;
}

"#

block_extension Block.leanEvalSteps (steps : Array Highlighted) where
  data := ToJson.toJson steps
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle, evalStepsStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [{filename := "popper.js", contents := popper, sourceMap? := none}, {filename := "tippy.js", contents := tippy, sourceMap? := none}]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (steps : Array Highlighted) =>
        let i := steps.map (·.indentation) |>.toList |>.min? |>.getD 0
        return {{
          <div class="eval-steps">
            {{← steps.mapM (·.deIndent i |>.blockHtml "examples" (g := Verso.Genre.Manual))}}
          </div>
        }}

block_extension Block.leanEqReason where
  traverse _ _ _ := pure none
  toTeX := none
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ contents => do
      return {{
        <div class="reason">
          {{ ← contents.mapM goB }}
        </div>
      }}
  extraCss := [
  r#"
.eq-steps .hl.lean.block {
  background-color: #f6f7f6;
  padding: 1rem;
  margin-top: 0.25rem;
  margin-bottom: 0.25rem;
}
.eq-steps .reason {
  font-style: italic;
  margin-left: 2.5em;
  display: flex;
}
.eq-steps .reason::before {
  content: "={";
  font-family: var(--verso-code-font-family);
  font-style: normal;
  font-weight: 600;
  margin-right: 0.5em;
  align-self: center;
}
.eq-steps .reason > p {
  margin: 0;
  max-width: 25em;
  align-self: center;
}
.eq-steps .reason::after {
  content: "}=";
  font-family: var(--verso-code-font-family);
  font-style: normal;
  font-weight: 600;
  margin-left: 1em;
  align-self: center;
}
"#
  ]

def eqStepsStyle := r#"
div.paragraph > .eq-steps:not(:first-child) {
  margin-top: 0.5rem;
}

div.paragraph > .eq-steps:not(:last-child) {
  margin-bottom: 0.5rem;
}
"#

block_extension Block.leanEqSteps where
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [eqStepsStyle]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ goB _ _ contents => do
      return {{
        <div class="eq-steps">
          {{ ← contents.mapM goB }}
        </div>
      }}


private def getClass : MessageSeverity → String
  | .error => "error"
  | .information => "information"
  | .warning => "warning"

block_extension Block.leanOutput (severity : MessageSeverity) (message : String) (summarize : Bool := false) where
  data := ToJson.toJson (severity, message, summarize)
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun _ go _ _ content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [{filename := "popper.js", contents := popper, sourceMap? := none}, {filename := "tippy.js", contents := tippy, sourceMap? := none}]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok ((sev, txt, summarize) : MessageSeverity × String × Bool) =>
        let wrap html :=
          if summarize then {{<details><summary>"Expand..."</summary>{{html}}</details>}}
          else html
        pure <| wrap {{<div class={{getClass sev}}><pre>{{txt}}</pre></div>}}

@[role_expander kw]
def kw : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    let hl : Highlighted := .token ⟨.keyword none none none, kw.getString⟩ -- TODO kw xref
    return #[← ``(Inline.other (Inline.lean $(quote hl) {}) #[Inline.code $(quote kw.getString)])]

structure OutputInlineConfig where
  module : Ident
  severity : Option MessageSeverity
  plain : Bool := true

section
variable [Monad m] [MonadError m] [MonadLiftT CoreM m] [MonadReaderOf Elab.Term.Context m] [MonadLiftT MetaM m] [MonadMCtx m]
def OutputInlineConfig.parse : ArgParse m OutputInlineConfig :=
  (OutputInlineConfig.mk <$>
     .lift "Default example module" (do return mkIdentFrom (← getRef) (← currentExampleModule)) <*>
     (some <$> .positional `severity .messageSeverity <|> pure none) <*>
     .namedD `plain .bool true <* .done) <|>
  (OutputInlineConfig.mk <$>
     .positional `module .ident <*>
     (some <$> .positional `severity .messageSeverity <|> pure none) <*>
     .namedD `plain .bool true <* .done)

end

private inductive SplitCtxF where
  | tactics : Array (Highlighted.Goal Highlighted) → Nat → Nat → SplitCtxF
  | span : Array Highlighted.Message → SplitCtxF

private def SplitCtxF.wrap (hl : Highlighted) : SplitCtxF → Highlighted
  | .tactics g s e => .tactics g s e hl
  | .span xs => .span (xs.map (fun m => (m.1, m.2))) hl

private structure SplitCtx where
  contents : Array (Highlighted × SplitCtxF) := #[]
deriving Inhabited

private def SplitCtx.push (ctx : SplitCtx) (current : Highlighted) (info : SplitCtxF) : SplitCtx where
  contents := ctx.contents.push (current, info)

private def SplitCtx.pop (ctx : SplitCtx) : SplitCtx where
  contents := ctx.contents.pop

private def SplitCtx.close (ctx : SplitCtx) (current : Highlighted) : Highlighted × SplitCtx :=
  match ctx.contents.back? with
  | none => panic! s!"Popping empty context around '{current.toString}'"
  | some (left, f) => (left ++ f.wrap current, ctx.pop)

private def SplitCtx.split (ctx : SplitCtx) (current : Highlighted) : Highlighted × SplitCtx where
  fst := ctx.contents.foldr (init := current) fun (left, f) curr => left ++ f.wrap curr
  snd := { contents := ctx.contents.map (.empty, ·.2) }


def splitHighlighted (p : String → Bool) (hl : Highlighted) : Array Highlighted := Id.run do
  let mut todo := [some hl]
  let mut out := #[]
  let mut ctx : SplitCtx := {}
  let mut current : Highlighted := .empty
  repeat
    match todo with
    | [] =>
      out := out.push current
      break
    | none :: hs =>
      todo := hs
      let (c, ctx') := ctx.split current
      current := c
      ctx := ctx'
    | some (.seq xs) :: hs =>
      todo := xs.toList.map some ++ hs
    | some this@(.token ⟨_, t⟩) :: hs =>
      todo := hs
      if p t then
        out := out.push current
        current := .empty
      else
        current := current ++ this
    | some this@(.text ..) :: hs
    | some this@(.unparsed ..) :: hs
    | some this@(.point ..) :: hs =>
      todo := hs
      current := current ++ this
    | some (.span msgs x) :: hs =>
      todo := some x :: none :: hs
      ctx := ctx.push current (.span <| msgs.map fun x => ⟨x.1, x.2⟩)
      current := .empty
    | some (.tactics gs b e x) :: hs =>
      todo := some x :: none :: hs
      ctx := ctx.push current (.tactics gs b e)
      current := .empty

  return out

structure EvalStepContext extends CodeContext where
  step : WithSyntax Nat

instance [Monad m] [MonadOptions m] [MonadError m] [MonadLiftT CoreM m] : FromArgs EvalStepContext m where
  fromArgs := (fun x y => EvalStepContext.mk y x) <$> .positional' `step <*> fromArgs

private def quoteCode (str : String) : String := Id.run do
  let str := if str.startsWith "`" || str.endsWith "`" then " " ++ str ++ " " else str
  let mut n := 1
  let mut run := none
  let mut iter := str.iter
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next
    if c == '`' then
      run := some (run.getD 0 + 1)
    else if let some k := run then
      if k > n then n := k
      run := none

  let delim := String.mk (List.replicate n '`')
  return delim ++ str ++ delim



@[role_expander moduleEvalStep]
def moduleEvalStep : RoleExpander
  | args, inls => do
    let {project, module := moduleName, anchor?, step, showProofStates := _, defSite := _} ← parseThe EvalStepContext args
    let code? ← oneCodeStr? inls

    let modStr := moduleName.getId.toString

    let items ← loadModuleContent project modStr
    let highlighted := Highlighted.seq (items.map (·.code))

    let fragment ←
      if let some anchor := anchor? then
        try
          let {anchors, ..} ← anchored project moduleName anchor
          if let some hl := anchors[anchor.getId.toString]? then
            pure hl
          else
            logErrorAt anchor "Anchor not found"
            for x in anchors.keys do
              Suggestion.saveSuggestion anchor x x
            return #[← ``(sorryAx _ true)]
        catch
          | .error refStx e =>
            logErrorAt refStx e
            return #[← ``(sorryAx _ true)]
          | e =>
            throw e
      else pure highlighted

    let steps := splitHighlighted (· == "===>") fragment

    if let some step := steps[step.val]? then
      if let some code := code? then
        _ ← ExpectString.expectString "step" code step.toString.trim
        return #[← ``(Inline.other (Inline.lean $(quote step) {}) #[])]
      else
        let stepStr := step.toString
        Lean.logError m!"No expected term provided for `{stepStr}`."
        if let `(inline|role{$_ $_*} [%$tok1 $contents* ]%$tok2) := (← getRef) then
          let stx :=
            if tok1.getHeadInfo matches .original .. && tok2.getHeadInfo matches .original .. then
              mkNullNode #[tok1, tok2]
            else mkNullNode contents
          Suggestion.saveSuggestion stx (ExpectString.abbreviateString (quoteCode stepStr)) (quoteCode stepStr)
        return #[← ``(sorryAx _ true)]

    else
      let ok := steps.mapIdx fun i s => ({suggestion := toString i, postInfo? := some s.toString})
      let h ← MessageData.hint "Use a step in the range 0–{steps.size}" ok (ref? := some step.syntax)
      logErrorAt step.syntax m!"Step not found - only {steps.size} are available{h}"
      return #[← ``(sorryAx _ true)]

macro_rules
  | `(inline|role{anchorEvalStep $a:arg_val $n:arg_val $arg*}[$i*]) =>
    `(inline|role{moduleEvalStep $n:arg_val $arg* anchor := $a }[$i*])

private def editCodeBlock [Monad m] [MonadFileMap m] (stx : Syntax) (newContents : String) : m (Option String) := do
  let txt ← getFileMap
  let some rng := stx.getRange?
    | pure none
  let { start := {line := l1, ..}, .. } := txt.utf8RangeToLspRange rng
  let line1 := (txt.lineStart (l1 + 1)).extract txt.source (txt.lineStart (l1 + 2))
  if line1.startsWith "```" then
    return some s!"{delims}{line1.dropWhile (· == '`') |>.trim}\n{withNl newContents}{delims}"
  else
    return none
where
  delims : String := Id.run do
    let mut n := 3
    let mut run := none
    let mut iter := newContents.iter
    while h : iter.hasNext do
      let c := iter.curr' h
      iter := iter.next
      if c == '`' then
        run := some (run.getD 0 + 1)
      else if let some k := run then
        if k > n then n := k
        run := none
    if let some k := run then
      if k > n then n := k
    n.fold (fun _ _ s => s.push '`') ""

@[code_block_expander moduleEvalStep]
def moduleEvalStepBlock : CodeBlockExpander
  | args, code => do
    let {project, module := moduleName, anchor?, step, showProofStates := _, defSite := _} ← parseThe EvalStepContext args

    withAnchored project moduleName anchor? fun fragment => do
      let steps := splitHighlighted (· == "===>") fragment

      if let some step := steps[step.val]? then
        _ ← ExpectString.expectString "step" code (withNl step.toString.trim)
        return #[← ``(Block.other (Block.lean $(quote step) {}) #[])]
      else
        let ok := steps.mapIdx fun i s => ({suggestion := toString i, postInfo? := some s.toString})
        let h ← MessageData.hint "Use a step in the range 0–{steps.size}" ok (ref? := some step.syntax)
        logErrorAt step.syntax m!"Step not found - only {steps.size} are available{h}"
        return #[← ``(sorryAx _ true)]

macro_rules
  | `(block|```%$t1 anchorEvalStep $a:arg_val $n:arg_val $arg* | $s ```%$t2) =>
    `(block|```%$t1 moduleEvalStep $n:arg_val $arg* anchor := $a | $s ```%$t2)


@[code_block_expander moduleEvalSteps]
def moduleEvalSteps : CodeBlockExpander
  | args, str => do
    let {project, module := moduleName, anchor?, showProofStates := _, defSite := _} ← parseThe CodeContext args

    withAnchored project moduleName anchor? fun fragment => do
      _ ← ExpectString.expectString "steps" str fragment.toString

      let steps := splitHighlighted (· == "===>") fragment

      return #[← ``(Block.other (Block.leanEvalSteps $(quote steps)) #[])]

macro_rules
  | `(block|```%$t1 anchorEvalSteps $a:arg_val $arg* | $s ```%$t2) =>
    `(block|```%$t1 moduleEvalSteps $arg* anchor := $a | $s ```%$t2)


@[code_block_expander moduleEqSteps]
def moduleEqSteps : CodeBlockExpander
  | args, str => do
    let {project, module := moduleName, anchor?, showProofStates := _, defSite := _} ← parseThe CodeContext args

    withAnchored project moduleName anchor? fun fragment => do
      _ ← ExpectString.expectString "steps" str fragment.toString

      let steps := splitHighlighted (· ∈ ["={", "}="]) fragment
      let steps ← steps.mapM fun hl => do
        if let some ((.token ⟨.docComment, txt⟩), _) := hl.firstToken then
          let txt := txt.trim |>.stripPrefix "/--" |>.stripSuffix "-/" |>.trim
          if let some ⟨#[.p txts]⟩ := MD4Lean.parse txt then
            let mut out : Array Term := #[]
            for txt in txts do
              match txt with
              | .normal s => out := out.push (← ``(Inline.text $(quote s)))
              | .softbr s => out := out.push (← ``(Inline.linebreak $(quote s)))
              | .code c =>
                let code := String.join c.toList
                if let some hl := hl.matchingExpr? code <|> fragment.matchingExpr? code then
                   out := out.push (← ``(Inline.other (Inline.lean $(quote hl) {}) #[]))
                else
                  logWarning m!"Failed to match `{code}` in `{hl.toString}`"
                  out := out.push  (← ``(Inline.code $(quote code)))
              | o => logWarning m!"Unsupported Markdown: {repr o}"
            ``(Block.other Block.leanEqReason #[Block.para #[$(out),*] ])
          else
            ``(Block.other Block.leanEqReason #[Block.para #[Inline.text $(quote txt) ] ])
        else ``(ExternalCode.leanBlock $(quote hl) {})
      let steps : Array Term := steps.map quote
      return #[← ``(Block.other Block.leanEqSteps #[$steps,*])]

macro_rules
  | `(block|```%$t1 anchorEqSteps $a:arg_val $arg* | $s ```%$t2) =>
    `(block|```%$t1 moduleEqSteps $arg* anchor := $a | $s ```%$t2)

def withNl (s : String) : String := if s.endsWith "\n" then s else s ++ "\n"

structure ContainerConfig where
  container : Ident
  dir : StrLit

structure CommandsConfig extends ContainerConfig where
  «show» : Bool

structure CommandConfig extends ContainerConfig where
  «show» : Option StrLit := none
  viaShell : Bool := false

section

variable [Monad m] [MonadError m] [MonadLiftT CoreM m]

instance : FromArgs ContainerConfig m where
  fromArgs := ContainerConfig.mk <$> .positional `container .ident <*> .positional `dir .strLit

instance : FromArgs CommandConfig m where
  fromArgs := CommandConfig.mk <$> fromArgs <*> .named `show .strLit true <*> .namedD `shell .bool false

instance : FromArgs CommandsConfig m where
  fromArgs := CommandsConfig.mk <$> fromArgs <*> .namedD `show .bool true

end

inline_extension Inline.shellCommand (command : String) where
  traverse _ _ _ := pure none
  data := .str command
  toTeX := none
  toHtml := some fun _ _ data _ => do
    let .str command := data
      | HtmlT.logError s!"Failed to deserialize commands:\n{data}"
        return .empty
    let piece := {{ <code class="command">{{command}}</code> }}
    pure {{
      <span class="shell-command inline">{{piece}}</span>
    }}
  extraCss := [
    r#"
.shell-command {

}
.shell-command.inline > * {
  display: inline;
  white-space: pre;
}
.shell-command.inline .command::before {
  content: "$ ";
  font-weight: 600;
}
"#
  ]

block_extension Block.shellCommand (command : String) (prompt : Option String) where
  traverse _ _ _ := pure none
  data := .arr #[.str command, prompt.map .str |>.getD .null]
  toTeX := none
  toHtml := some fun _ _ _ data _ => do
    let .arr #[.str command, prompt?] := data
      | HtmlT.logError s!"Failed to deserialize commands:\n{data}"
        return .empty
    let prompt? :=
      match prompt? with
      | .str p => some p
      | _ => none
    let piece := {{ <code class="command"><code class="prompt">{{prompt?.getD "$ "}}</code>{{command}}</code> }}
    pure {{
      <div class="shell-command block">{{piece}}</div>
    }}
  extraCss := [
    r#"
.shell-command {

}
.shell-command.block > * {
  display: block;
  white-space: pre;
}
.shell-command .command .prompt {
  font-weight: 600;
}

div.paragraph > .shell-command:not(:first-child) {
  margin-top: 0.5rem;
}

div.paragraph > .shell-command:not(:last-child) {
  margin-bottom: 0.5rem;
}
"#
  ]

@[role_expander command]
def command : RoleExpander
  | args, inls => do
    let { container, dir, «show», viaShell } ← parseThe CommandConfig args
    let cmd ← oneCodeStr inls
    let output ← Commands.command container dir.getString cmd (viaShell := viaShell)
    unless output.stdout.isEmpty do
      logSilentInfo <| "Stdout:\n" ++ output.stdout
    unless output.stderr.isEmpty do
      logSilentInfo <| "Stderr:\n" ++ output.stderr
    let out := «show».getD cmd |>.getString
    return #[← ``(Inline.other (Inline.shellCommand $(quote out)) #[Inline.code $(quote out)])]

structure CommandBlockConfig extends CommandConfig where
  command : StrLit
  prompt : Option StrLit := none

section
variable [Monad m] [MonadError m] [MonadLiftT CoreM m]

def CommandBlockConfig.parse  : ArgParse m CommandBlockConfig :=
  (fun container dir command «show» prompt viaShell => {container, dir, command, «show», prompt, viaShell}) <$>
    .positional `container .ident <*>
    .positional `dir .strLit <*>
    .positional `command .strLit <*>
    .named `show .strLit true <*>
    .named `prompt .strLit true <*>
    .namedD `shell .bool false

instance : FromArgs CommandBlockConfig m where
  fromArgs := CommandBlockConfig.parse

end

@[block_command command]
def commandBlock : BlockCommandOf CommandBlockConfig
  | { container, dir, command, «show», prompt, viaShell } => do
    let output ← Commands.command container dir.getString command (viaShell := viaShell)
    unless output.stdout.isEmpty do
      logSilentInfo <| "Stdout:\n" ++ output.stdout
    unless output.stderr.isEmpty do
      logSilentInfo <| "Stderr:\n" ++ output.stderr
    let out := «show».getD command |>.getString
    ``(Block.other (Block.shellCommand $(quote out) $(quote <| prompt.map (·.getString))) #[Block.code $(quote out)])

instance : Coe StrLit (TSyntax `doc_arg) where
  coe stx := ⟨mkNode ``Lean.Doc.Syntax.anon #[mkNode ``Lean.Doc.Syntax.arg_str #[stx.raw]]⟩

macro_rules
  | `(block|```command $args* | $s```) => `(block|command{command $args* $s})

@[role_expander commandOut]
def commandOut : RoleExpander
  | args, inls => do
    let container ← ArgParse.run (.positional `container .ident) args
    let cmd ← oneCodeStr inls
    let output ← Commands.commandOut container cmd
    logSilentInfo output
    return #[← ``(Inline.code $(quote output.trim))]

@[code_block_expander commandOut]
def commandOutCodeBlock : CodeBlockExpander
  | args, outStr => do
    let (container, command) ← ArgParse.run ((·, ·) <$> .positional `container .ident <*> .positional `command .strLit) args
    let output ← Commands.commandOut container command

    _ ← ExpectString.expectString "command output" outStr (withNl output) (useLine := fun l => !l.trim.isEmpty) (preEq := String.trim)

    logSilentInfo output
    return #[← ``(Block.code $(quote output))]



block_extension Block.shellCommands (segments : Array (String × Bool)) where
  traverse _ _ _ := pure none
  data := toJson segments
  toTeX := none
  toHtml := some fun _ _ _ data _ => do
    let .ok (segments : Array (String × Bool)) := fromJson? data
      | HtmlT.logError s!"Failed to deserialize commands:\n{data}"
        return .empty
    let pieces := segments.map fun (s, cmd) =>
      {{ <code class={{if cmd then "command" else "output"}}>{{s}}</code> }}
    pure {{
      <div class="shell-commands">{{pieces}}</div>
    }}
  extraCss := [
    r#"
.shell-commands {

}
.shell-commands > * {
  display: block;
  white-space: pre;
}
.shell-commands .command::before {
  content: "$ ";
  font-weight: 600;
}

div.paragraph > .shell-commands:not(:first-child) {
  margin-top: 0.5rem;
}

div.paragraph > .shell-commands:not(:last-child) {
  margin-bottom: 0.5rem;
}
"#
  ]


private inductive CommandSpec where
  | run (cmd : String) (show? : Option String)
  | quote (cmd : String)
  | out (text : String)

@[code_block_expander commands]
def commands : CodeBlockExpander
  | args, str => do
    let {container, dir, «show»} ← parseThe CommandsConfig args
    let specStr := str.getString
    let mut commands : Array CommandSpec := #[]
    let mut quoted := false
    for line in specStr.splitOn "\n" do
      if line.startsWith "$$" then
        commands := commands.push (.quote (line.drop 2 |>.trim))
        quoted := true
      else if line.startsWith "$" then
        let line := line.drop 1 |>.trim
        quoted := false
        if line.contains '#' then
          let cmd := line.takeWhile (· ≠ '#')
          let rest := (line.drop (cmd.length + 1)).trim
          commands := commands.push (.run cmd.trim (some rest))
        else
          commands := commands.push (.run line none)

      else if quoted then
        commands := commands.push (.out line.trimRight)
    let mut out := #[]
    let mut outStr := ""
    for cmdSpec in commands do
      match cmdSpec with
      | .quote command =>
        out := out.push (command, true)
        outStr := outStr ++ s!"$$ {command}\n"
      | .run command show? =>
        if let some toShow := show? then
          out := out.push (toShow, true)
          outStr := outStr ++ s!"$ {command} # {toShow}\n"
        else
          out := out.push (command, true)
          outStr := outStr ++ s!"$ {command}\n"
        let output ← Commands.command container dir.getString (Syntax.mkStrLit command (info := str.raw.getHeadInfo)) (viaShell := true)
        unless output.stdout.isEmpty do
          out := out.push (output.stdout, false)
          outStr := outStr ++ withNl output.stdout
        unless output.stderr.isEmpty do
          out := out.push (output.stderr, false)
          outStr := outStr ++ withNl output.stderr
      | .out txt =>
        out := out.push (txt, false)
        outStr := outStr ++ withNl txt
    unless str.getString.trim == "" && outStr.trim == "" do
      _ ← ExpectString.expectString "commands" str outStr (preEq := String.trim)
    if «show» then
      pure #[← ``(Block.other (Block.shellCommands $(quote out)) #[])]
    else pure #[]


@[code_block_expander file]
def file : CodeBlockExpander
  | args, expectedContentsStr => do
    let (container, file, show?) ← ArgParse.run ((·, ·, ·) <$> .positional `container .ident <*> .positional `file .strLit <*> (some <$> .positional `show .strLit <|> pure none)) args
    let show? := show?.map (·.getString)
    let c ← Commands.requireContainer container
    let fn := c.workingDirectory / "examples" / file.getString
    let contents ← IO.FS.readFile fn
    let _ ← ExpectString.expectString "file" expectedContentsStr (withNl contents)
    logSilentInfo contents
    return #[← ``(Block.other (InlineLean.Block.exampleFile (FileType.other $(quote (show?.getD (fn.fileName.getD fn.toString))))) #[Block.code $(quote contents)])]

structure PlainFileConfig where
  project : StrLit
  file : StrLit
  show? : Option StrLit

instance [Monad m] [MonadOptions m] [MonadError m] : FromArgs PlainFileConfig m where
  fromArgs := PlainFileConfig.mk <$> projectOrDefault <*> .positional' `file <*> (some <$> .positional `show .strLit <|> pure none)

@[code_block_expander plainFile]
def plainFile : CodeBlockExpander
  | args, expectedContentsStr => do
    let {project := projectDir, file, show?} ← parseThe PlainFileConfig args
    let show? := show?.map (·.getString)

    let projectDir : System.FilePath := projectDir.getString
    let fn :=  projectDir / file.getString
    let contents ← IO.FS.readFile fn

    let _ ← ExpectString.expectString "file" expectedContentsStr (withNl contents)
    logSilentInfo contents

    return #[← ``(Block.other (InlineLean.Block.exampleFile (FileType.other $(quote (show?.getD (fn.fileName.getD fn.toString))))) #[Block.code $(quote contents)])]


private def severityName {m} [Monad m] [MonadEnv m] [MonadResolveName m] [MonadOptions m] [MonadLog m] [AddMessageContext m] : MessageSeverity → m String
  | .error => unresolveNameGlobal ``MessageSeverity.error <&> (·.toString)
  | .warning => unresolveNameGlobal ``MessageSeverity.warning <&> (·.toString)
  | .information => unresolveNameGlobal ``MessageSeverity.information <&> (·.toString)

deriving instance Repr for MessageSeverity

private def severityHint (wanted : String) (stx : Syntax) : DocElabM MessageData := do
  if stx.getHeadInfo matches .original .. then
    MessageData.hint m!"Use '{wanted}'" #[wanted] (ref? := some stx)
  else pure m!""

open Lean.Meta.Hint in
@[role_expander moduleOutText]
def moduleOutText : RoleExpander
  | args, inls => withTraceNode `Elab.Verso (fun _ => pure m!"moduleOutText") <| do
    let str? ← oneCodeStr? inls

    let {project, module := moduleName, anchor?, severity, showProofStates := _, defSite := _, expandTraces, onlyTrace} ← parseThe MessageContext args
    if onlyTrace.isSome then throwError "Unsupported option: `onlyTrace`"

    withAnchored project moduleName anchor? fun hl => do
      let infos := allInfo hl
      if let some str := str? then
        let mut strings := #[]
        for (msg, _) in infos do
          let s := msg.toString (expandTraces := expandTraces)
          strings := strings.push s
          if messagesMatch s str.getString then
            if msg.severity.toSeverity == severity.1 then
              return #[← ``(Inline.text $(quote s))]
            else
              let wanted ← severityName msg.severity.toSeverity
              throwError "Mismatched severity. Expected '{repr severity.1}', got '{wanted}'.{← severityHint wanted severity.2}"

        let ref :=
          if let `(inline|role{ $_ $_* }[ $x ]) := (← getRef) then x.raw else str

        let suggs : Array Suggestion := strings.map fun msg => {
          suggestion := quoteCode msg.trim
        }
        let h ←
          if suggs.isEmpty then pure m!""
          else MessageData.hint "Use one of these." suggs (ref? := some ref)

        let err :=
          m!"Expected one of:{indentD (m!"\n".joinSep <| infos.toList.map (·.1.toString))}" ++
          m!"\nbut got:{indentD str.getString}\n" ++ h
        logErrorAt str err
      else
        let err := m!"Expected one of:{indentD (m!"\n".joinSep <| infos.toList.map (·.1.toString))}"
        Lean.logError m!"No expected term provided. {err}"
        if let `(inline|role{$_ $_*} [%$tok1 $contents* ]%$tok2) := (← getRef) then
          let stx :=
            if tok1.getHeadInfo matches .original .. && tok2.getHeadInfo matches .original .. then
              mkNullNode #[tok1, tok2]
            else mkNullNode contents
          for (msg, _) in infos do
            let msg := msg.toString.trim
            Suggestion.saveSuggestion stx (quoteCode <| ExpectString.abbreviateString msg) (quoteCode msg)

      return #[← ``(sorryAx _ true)]

where
  quoteCode (str : String) : String := Id.run do
    let str := if str.startsWith "`" || str.endsWith "`" then " " ++ str ++ " " else str
    let mut n := 1
    let mut run := none
    let mut iter := str.iter
    while h : iter.hasNext do
      let c := iter.curr' h
      iter := iter.next
      if c == '`' then
        run := some (run.getD 0 + 1)
      else if let some k := run then
        if k > n then n := k
        run := none

    let delim := String.mk (List.replicate n '`')
    return delim ++ str ++ delim

macro_rules
  | `(inline|role{%$rs moduleInfoText $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOutText MessageSeverity.information $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs moduleErrorText $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOutText MessageSeverity.error $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs moduleWarningText $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOutText MessageSeverity.warning $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs anchorInfoText $a:arg_val $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOutText MessageSeverity.information anchor:=$a $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs anchorErrorText $a:arg_val $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOutText MessageSeverity.error anchor:=$a $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs anchorWarningText $a:arg_val $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOutText MessageSeverity.warning anchor:=$a $arg*}%$re [%$s $str* ]%$e)


def hasSubstring (s pattern : String) : Bool :=
  if h : pattern.endPos.1 = 0 then false
  else
    have hPatt := Nat.zero_lt_of_ne_zero h
    let rec loop (pos : String.Pos.Raw) :=
      if h : pos.byteIdx + pattern.endPos.byteIdx > s.endPos.byteIdx then
        false
      else
        have := Nat.lt_of_lt_of_le (Nat.add_lt_add_left hPatt _) (Nat.ge_of_not_lt h)
        if pos.substrEq s pattern 0 pattern.endPos.byteIdx then
          have := Nat.sub_lt_sub_left this (Nat.add_lt_add_left hPatt _)
          true
        else
          have := Nat.sub_lt_sub_left this (pos.byteIdx_lt_byteIdx_next s)
          loop (pos.next s)
      termination_by s.endPos.1 - pos.1
    loop 0
