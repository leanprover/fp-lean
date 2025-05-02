import SubVerso.Examples
import Lean.Data.NameMap
import VersoManual
import FPLean.Examples.Data
import FPLean.Examples.Commands
import FPLean.Examples.OtherLanguages
import FPLean.Examples.Files

open Lean (NameMap MessageSeverity)


namespace FPLean


open Verso Doc Elab Genre.Manual ArgParse Code Highlighted WebAssets Output Html
open SubVerso.Highlighting
open SubVerso.Examples.Messages
open Lean
open Std

open InlineLean (FileType)

section
variable [Monad m] [MonadOptions m] [MonadLog m] [AddMessageContext m] [MonadRef m]

def logSilentInfoAt  (ref : Syntax) (message : MessageData) : m Unit :=
  logAt ref message (severity := .information) (isSilent := true)

def logSilentInfo (message : MessageData) : m Unit := do
  logAt (← getRef) message (severity := .information) (isSilent := true)

end

private def hlToString : Highlighted → String
  | .seq xs => xs.foldl (init := "") (fun s hl => s ++ hlToString hl)
  | .point .. => ""
  | .tactics _ _ _ x | .span _ x => hlToString x
  | .text s | .token ⟨_, s⟩ => s



private def oneCodeStr [Monad m] [MonadError m] (inlines : Array (TSyntax `inline)) : m StrLit := do
  let #[code] := inlines
    | (if inlines.size == 0 then (throwError ·) else (throwErrorAt (mkNullNode inlines) ·)) "Expected one code element"
  let `(inline|code($code)) := code
    | throwErrorAt code "Expected a code element"
  return code

private def oneCodeName [Monad m] [MonadError m] (inlines : Array (TSyntax `inline)) : m Ident := do
  let code ← oneCodeStr inlines
  let str := code.getString
  let name := if str.contains '.' then str.toName else Name.str .anonymous str
  return mkIdentFrom code name


def minIndentString (str : String) : Nat :=
  let indents := str.split (· == '\n') |>.filterMap fun line =>
    if line.all (· == ' ') then none
    else some (line.takeWhile (· == ' ') |>.length)
  indents.min?.getD 0

/-- info: 2 -/
#guard_msgs in
#eval minIndentString "  x\n     \n\n    y"

/-- info: 3 -/
#guard_msgs in
#eval minIndentString "   x\n     \n\n    y"

/-- info: 0 -/
#guard_msgs in
#eval minIndentString "     "

/-- info: 0 -/
#guard_msgs in
#eval minIndentString ""

def minIndent (hl : Highlighted) : Nat := Id.run do
  let mut hl := [hl]
  let mut asStr := ""
  repeat
    match hl with
    | [] => break
    | .seq xs :: more =>
      hl := xs.toList ++ more
    | .point .. :: more => hl := more
    | .tactics _ _ _ x :: more => hl := x :: more
    | .span _ x :: more => hl := x :: more
    | .text str :: more => asStr := asStr ++ str; hl := more
    | .token ⟨_, s⟩ :: more => asStr := asStr ++ s; hl := more
  minIndentString asStr

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

block_extension Block.leanDecl (hls : Highlighted) where
  data :=
    let defined := hls.definedNames.toArray
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined]
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      let .arr #[hlJson, _] := data
        | HtmlT.logError "Expected four-element JSON for Lean code"
          pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        let i := minIndent hl
        let hl := hl.deIndent i
        hl.blockHtml "examples"

block_extension Block.leanEvalSteps (steps : Array Highlighted) where
  data := ToJson.toJson steps
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (steps : Array Highlighted) =>
        let i := steps.map minIndent |>.toList |>.min? |>.getD 0
        return {{<div class="eval-steps">{{← steps.mapM (·.deIndent i |>.blockHtml "examples")}}</div>}}

inline_extension Inline.leanTerm (hls : Highlighted) where
  data :=
    let defined := hls.definedNames.toArray
    Json.arr #[ToJson.toJson hls, ToJson.toJson defined]
  traverse _ _ _ := pure none
  toTeX := none
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      let .arr #[hlJson, _] := data
        | HtmlT.logError "Expected four-element JSON for Lean code"
          pure .empty
      match FromJson.fromJson? hlJson with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code block while rendering HTML: " ++ err
        pure .empty
      | .ok (hl : Highlighted) =>
        let i := minIndent hl
        let hl := hl.deIndent i
        hl.inlineHtml "examples"

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
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
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

inline_extension Inline.leanOutput (severity : MessageSeverity) (message : String) (plain : Bool) where
  data := ToJson.toJson (severity, message, plain)
  traverse _ _ _ := do
    pure none
  toTeX :=
    some <| fun go _ _  content => do
      pure <| .seq <| ← content.mapM fun b => do
        pure <| .seq #[← go b, .raw "\n"]
  extraCss := [highlightingStyle]
  extraJs := [highlightingJs]
  extraJsFiles := [("popper.js", popper), ("tippy.js", tippy)]
  extraCssFiles := [("tippy-border.css", tippy.border.css)]
  toHtml :=
    open Verso.Output.Html in
    some <| fun _ _ data _ => do
      match FromJson.fromJson? data with
      | .error err =>
        HtmlT.logError <| "Couldn't deserialize Lean code while rendering HTML: " ++ err
        pure .empty
      | .ok ((sev, txt, plain) : MessageSeverity × String × Bool) =>
        let plainHtml := {{<code>{{txt}}</code>}}
        if plain then pure plainHtml
        else pure {{<span class={{getClass sev}}>{{plainHtml}}</span>}}

@[block_role_expander exampleDecl]
def exampleDecl : BlockRoleExpander
  | args, #[] => do
    let (module, name) ← modAndName (← getRef) |>.run args
    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"
    if ex.kind != some `FPLean.decl then
      throwErrorAt name m!"Expected example kind 'FPLean.decl', got '{ex.kind}'"
    return #[← ``(Block.other (Block.leanDecl $(quote (Highlighted.seq ex.highlighted))) #[Block.code $(quote ex.original)])]
  | _args, _blocks =>
    throwError "Unexpected block arguments"

@[code_block_expander exampleDecl]
def exampleDeclCode : CodeBlockExpander
  | args, codeStr => do
    let (module, name) ← modAndName (← getRef) |>.run args
    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"
    _ ← ExpectString.expectString s!"'{name}' in '{module.getId}'" codeStr (hlToString (.seq ex.highlighted))
    if ex.kind != some `FPLean.decl then
      throwErrorAt name m!"Expected example kind 'FPLean.decl', got '{ex.kind}'"
    return #[← ``(Block.other (Block.leanDecl $(quote (Highlighted.seq ex.highlighted))) #[Block.code $(quote ex.original)])]


@[role_expander exampleDecl]
def exampleDeclInline : RoleExpander
  | args, inls => do
    let name ← oneCodeName inls
    let (module) ← mod (← getRef) |>.run args
    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"
    if ex.kind != some `FPLean.decl then
      throwErrorAt name m!"Expected example kind 'FPLean.decl', got '{ex.kind}'"
    return #[← ``(Inline.other (Inline.leanTerm $(quote (Highlighted.seq ex.highlighted))) #[Inline.code $(quote ex.original)])]

@[block_role_expander exampleIn]
def exampleIn : BlockRoleExpander
  | args, #[] => do
    let (module, name) ← modAndName (← getRef) |>.run args
    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"

    match ex.kind with
    | some `FPLean.decl | some `FPLean.evalInfo =>
      let some exIn := mod.find? (name.getId ++ `in)
        | throwErrorAt name "Example input not found: '{name.getId ++ `in}'"
      return #[← ``(Block.other (Block.leanDecl $(quote (Highlighted.seq exIn.highlighted))) #[Block.code $(quote exIn.original)])]
    | some `FPLean.forMessage =>
      return #[← ``(Block.other (Block.leanDecl $(quote (Highlighted.seq ex.highlighted))) #[Block.code $(quote ex.original)])]
    | _ =>
      throwErrorAt name m!"Expected example kind 'FPLean.inputOutput' or 'FPLean.forMessage', got '{ex.kind}'"

  | _args, _blocks =>
    throwError "Unexpected block arguments"

@[code_block_expander exampleIn]
def exampleInCode : CodeBlockExpander
  | args, codeStr => do
    let (module, name) ← modAndName (← getRef) |>.run args
    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"

    match ex.kind with
    | some `FPLean.decl | some `FPLean.evalInfo =>
      let some exIn := mod.find? (name.getId ++ `in)
        | throwErrorAt name "Example input not found: '{name.getId ++ `in}'"
      let _ ← ExpectString.expectString s!"'{name.getId ++ `in}' in {module.getId}" codeStr (hlToString <| .seq exIn.highlighted)
      return #[← ``(Block.other (Block.leanDecl $(quote (Highlighted.seq exIn.highlighted))) #[Block.code $(quote exIn.original)])]
    | some `FPLean.forMessage =>
      let _ ← ExpectString.expectString s!"'{name.getId}' in {module.getId}" codeStr (hlToString <| .seq ex.highlighted)
      return #[← ``(Block.other (Block.leanDecl $(quote (Highlighted.seq ex.highlighted))) #[Block.code $(quote ex.original)])]

    | _ =>
      throwErrorAt name m!"Expected example kind 'FPLean.inputOutput' or 'FPLean.forMessage', got '{ex.kind}'"


@[block_role_expander exampleEval]
def exampleEval : BlockRoleExpander
  | args, #[] => do
    let (module, name, step?) ← modAndNameThen (← getRef) (some <$> .positional `step .nat <|> pure none) |>.run args
    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"

    match ex.kind with
    | some `FPLean.evalSteps =>
      if let some step := step? then
        let some exIn := mod.find? (name.getId ++ s!"step{step}".toName)
          | throwErrorAt name m!"Example input not found: '{name.getId ++ s!"step{step}".toName}'"
        return #[← ``(Block.other (Block.leanDecl $(quote (Highlighted.seq exIn.highlighted))) #[Block.code $(quote exIn.original)])]
      else
        let mut hls := #[]
        repeat
          let some exIn := mod.find? (name.getId ++ s!"step{hls.size}".toName)
            | break
          hls := hls.push (Highlighted.seq exIn.highlighted)
        if hls.size = 0 then
          throwErrorAt name m!"Example input not found: '{name.getId ++ `step0}"
        return #[← ``(Block.other (Block.leanEvalSteps $(quote hls)) #[])]
    | _ =>
      throwErrorAt name m!"Expected example kind 'FPLean.evalSteps', got '{ex.kind}'"
  | _args, _blocks =>
    throwError "Unexpected block arguments"

@[role_expander exampleEval]
def exampleEvalInline : RoleExpander
  | args, inls => do
    let (module, step) ← modAndThen (← getRef) (.positional `step .nat) |>.run args
    let name ← oneCodeName inls

    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"

    match ex.kind with
    | some `FPLean.evalSteps =>
      let some exIn := mod.find? (name.getId ++ s!"step{step}".toName)
        | throwErrorAt name m!"Example input not found: '{name.getId ++ s!"step{step}".toName}'"
      return #[← ``(Inline.other (Inline.leanTerm $(quote (Highlighted.seq exIn.highlighted))) #[Inline.code $(quote exIn.original)])]
    | _ =>
      throwErrorAt name "Expected example kind 'FPLean.evalSteps', got '{ex.kind}'"

@[role_expander kw]
def kw : RoleExpander
  | args, inls => do
    ArgParse.done.run args
    let kw ← oneCodeStr inls
    let hl : Highlighted := .token ⟨.keyword none none none, kw.getString⟩ -- TODO kw xref
    return #[← ``(Inline.other (Inline.leanTerm $(quote hl)) #[Inline.code $(quote kw.getString)])]


@[block_role_expander exampleOut]
def exampleOut : BlockRoleExpander
  | args, #[] => do
    let (module, name, sev) ← modAndNameAndSev (← getRef) |>.run args

    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"

    match ex.kind with
    | some `FPLean.forMessage | some `FPLean.evalInfo =>
      let [txt] := ex.messages.filterMap fun (sev', txt) => if sev == sev' then pure txt else failure
        | let msgs := ex.messages.map fun (sev, msg) => m!"{repr sev}:{indentD (repr msg)}"
          let msgs := MessageData.joinSep msgs Std.Format.line
          throwErrorAt name "Expected exactly one message with severity {repr sev}, got {ex.messages.length}:{indentD msgs}"

      return #[← ``(Block.other (Block.leanOutput $(quote sev) $(quote txt)) #[Block.code $(quote txt)])]
    | _ =>
      throwErrorAt name "Unexpected example kind '{ex.kind}'"

  | _args, _blocks =>
    throwError "Unexpected block arguments"

macro_rules
  | `(block|block_role{exampleInfo $arg*}) =>
    `(block|block_role{exampleOut $arg* MessageSeverity.information})
  | `(block|block_role{exampleError $arg*}) =>
    `(block|block_role{exampleOut $arg* MessageSeverity.error})
  | `(block|block_role{exampleWarning $arg*}) =>
    `(block|block_role{exampleOut $arg* MessageSeverity.warning})

@[code_block_expander exampleOut]
def exampleOutCode : CodeBlockExpander
  | args, str => do
    let (module, name, sev) ← modAndNameAndSev (← getRef) |>.run args
    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"

    match ex.kind with
    | some `FPLean.forMessage  | some `FPLean.evalInfo =>
      let txts := ex.messages.filterMap fun (sev', txt) => do
        guard <| sev == sev'
        pure txt
      let [txt] := txts.filter (messagesMatch str.getString)
        | let msgs := ex.messages.map fun (_, msg) => msg
          for msg in msgs do
            Suggestion.saveSuggestion str (ExpectString.abbreviateString msg) msg
          let msgs := msgs.map fun msg => m!"{repr sev}:{indentD (repr msg)}"
          let msgs := MessageData.joinSep msgs Std.Format.line
          throwErrorAt name "Expected exactly one message with severity {repr sev}, got {ex.messages.length}:{indentD msgs}"

      return #[← ``(Block.other (Block.leanOutput $(quote sev) $(quote txt)) #[Block.code $(quote txt)])]
    | _ =>
      throwErrorAt name "Unexpected example kind '{ex.kind}'"

macro_rules
  | `(block|```exampleInfo $arg* | $s ```) =>
    `(block|```exampleOut $arg* MessageSeverity.information | $s ```)
  | `(block|```exampleError $arg* | $s ```) =>
    `(block|```exampleOut $arg* MessageSeverity.error | $s ```)
  | `(block|```exampleWarning $arg* | $s ```) =>
    `(block|```exampleOut $arg* MessageSeverity.warning | $s ```)


@[block_role_expander exampleOuts]
def exampleOuts : BlockRoleExpander
  | args, #[] => do
    let (module, name, sev) ← modAndNameAndSev (← getRef) |>.run args

    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"

    match ex.kind with
    | some `FPLean.forMessage =>
      let txts := ex.messages.filterMap fun (sev', txt) => if sev == sev' then pure txt else failure
      txts.toArray.mapM fun txt =>
        ``(Block.other (Block.leanOutput $(quote sev) $(quote txt)) #[Block.code $(quote txt)])
    | _ =>
      throwErrorAt name "Unexpected example kind '{ex.kind}'"

  | _args, _blocks =>
    throwError "Unexpected block arguments"

macro_rules
  | `(block|block_role{exampleInfos $arg*}) =>
    `(block|block_role{exampleOuts $arg* MessageSeverity.information})
  | `(block|block_role{exampleErrors $arg*}) =>
    `(block|block_role{exampleOuts $arg* MessageSeverity.error})
  | `(block|block_role{exampleWarnings $arg*}) =>
    `(block|block_role{exampleOuts $arg* MessageSeverity.warning})

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



@[role_expander exampleIn]
def exampleInInline : RoleExpander
  | args, inls => do
    let name ← oneCodeName inls
    let module ← mod (← getRef) |>.run args
    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"

    match ex.kind with
    | some `FPLean.decl | some `FPLean.evalInfo =>
      let some exIn := mod.find? (name.getId ++ `in)
        | throwErrorAt name m!"Example input not found: '{name.getId ++ `in}'"
      return #[← ``(Inline.other (Inline.leanTerm $(quote (Highlighted.seq exIn.highlighted))) #[Inline.code $(quote exIn.original)])]
    | some `FPLean.forMessage =>
      return #[← ``(Inline.other (Inline.leanTerm $(quote (Highlighted.seq ex.highlighted))) #[Inline.code $(quote ex.original)])]
    | some `FPLean.inputOutput =>
      let inName := name.getId ++ `in
      let some ex := mod.find? name.getId
        | throwErrorAt name m!"Example not found: '{inName}'"
      return #[← ``(Inline.other (Inline.leanTerm $(quote (Highlighted.seq ex.highlighted))) #[Inline.code $(quote ex.original)])]
    | _ =>
      throwErrorAt name m!"Expected example kind 'FPLean.inputOutput' or 'FPLean.forMessage', got '{ex.kind}'"


@[role_expander exampleOut]
def exampleOutInline : RoleExpander
  | args, inls => do
    let name ← oneCodeName inls
    let { module, severity := sev, plain } ← OutputInlineConfig.parse.run args
    let some mod := exampleCode.code.find? module.getId
      | throwErrorAt module m!"Module not found: '{module.getId}'"
    let some ex := mod.find? name.getId
      | throwErrorAt name m!"Example not found: '{name.getId}'"

    match ex.kind with
    | some `FPLean.forMessage =>
      let some sev := sev
        | throwError "No message severity provided"
      let [txt] := ex.messages.filterMap fun (sev', txt) => if sev == sev' then pure txt else failure
        | let msgs := ex.messages.map fun (sev, msg) => m!"{repr sev}:{indentD (repr msg)}"
          let msgs := MessageData.joinSep msgs Std.Format.line
          throwErrorAt name "Expected exactly one message with severity {repr sev}, got {ex.messages.length}:{indentD msgs}"
      let txt :=
        if txt.splitOn "\n" |>.filter (!·.isEmpty) |>.length |> (· < 2) then
          txt.trim
        else
          txt
      return #[← ``(Inline.other (Inline.leanOutput $(quote sev) $(quote txt) $(quote plain)) #[Inline.code $(quote txt)])]
    | some `FPLean.inputOutput =>
      if let some sev := sev then throwError "Unexpected message severity '{repr sev}'"
      let outName := name.getId ++ `out
      let some out := mod.find? outName
        | throwErrorAt name "Example not found: '{outName}'"
      return #[← ``(Inline.other (Inline.leanTerm $(quote (Highlighted.seq out.highlighted))) #[Inline.code $(quote out.original)])]
    | _ =>
      throwErrorAt name "Unexpected example kind '{ex.kind}'"

macro_rules
  | `(inline|role{exampleInfo $arg*}[$i*]) =>
    `(inline|role{exampleOut $arg* MessageSeverity.information}[$i*])
  | `(inline|role{exampleError $arg*}[$i*]) =>
    `(inline|role{exampleOut $arg* MessageSeverity.error}[$i*])
  | `(inline|role{exampleWarning $arg*}[$i*]) =>
    `(inline|role{exampleOut $arg* MessageSeverity.warning}[$i*])

@[role_expander term]
def term : RoleExpander
  | args, inls => do
    let module? ← ArgParse.run ((some <$> .positional `module .ident) <|> pure none) args
    let name ← oneCodeName inls

    let module ← if let some m := module? then pure m else mkIdentFrom (← getRef) <$> currentExampleModule

    let some mod := exampleCode.code.find? module.getId
      | logErrorAt module m!"Module not found: '{module.getId}'"
        return #[]
    let some ex := mod.find? name.getId
      | logErrorAt name m!"Example not found: '{name.getId}'"
        return #[]

    return #[← ``(Inline.other (Inline.leanTerm $(quote (Highlighted.seq ex.highlighted))) #[Inline.code $(quote ex.original)])]


private def appendHl : Highlighted → Highlighted → Highlighted
  | .text str1, .text str2 => .text (str1 ++ str2)
  | .text "", other => other
  | other, .text "" => other
  | .seq xs, .seq ys => .seq (xs ++ ys)
  | .seq #[],  x => x
  | x, .seq #[] => x
  | .seq xs,  x => .seq (xs ++ #[x])
  | x, .seq xs => .seq (#[x] ++ xs)
  | x, y => .seq #[x, y]

local instance : HAppend Highlighted String Highlighted where
  hAppend x s := appendHl x (.text s)

local instance : HAppend String Highlighted Highlighted where
  hAppend s x := appendHl (.text s) x


private def normHl : Highlighted → Highlighted
  | .seq xs => xs.attach.map (fun ⟨x, _⟩ => normHl x) |>.foldl (init := .empty) appendHl
  | hl@(.point ..) => hl
  | .tactics x y z m => .tactics x y z (normHl m)
  | .span x y => .span x (normHl y)
  | .text "" => .empty
  | .text s => .text s
  | .token t => .token t

def anchor? (line : String) : Option (String × Bool) := do
  let mut line := line.trim
  unless line.startsWith "--" do failure
  line := line.stripPrefix "--"
  line := line.trimLeft
  if line.startsWith "ANCHOR:" then
    line := line.stripPrefix "ANCHOR:"
    line := line.trimLeft
    if line.isEmpty then failure else return (line, true)
  else if line.startsWith "ANCHOR_END:" then
    line := line.stripPrefix "ANCHOR_END:"
    line := line.trimLeft
    if line.isEmpty then failure else return (line, false)
  else failure

/-- info: some ("foo", true) -/
#guard_msgs in
#eval anchor? "-- ANCHOR: foo"

/-- info: some ("foo", true) -/
#guard_msgs in
#eval anchor? "-- ANCHOR:foo"

/-- info: some ("foo", true) -/
#guard_msgs in
#eval anchor? "           -- ANCHOR:    foo"

/-- info: some ("foo", false) -/
#guard_msgs in
#eval anchor? "-- ANCHOR_END: foo"

/-- info: some ("foo", false) -/
#guard_msgs in
#eval anchor? "-- ANCHOR_END:foo"

/-- info: some ("foo", false) -/
#guard_msgs in
#eval anchor? "           -- ANCHOR_END:    foo"

/-- info: none -/
#guard_msgs in
#eval anchor? "           -- ANCHOR_END :    foo"

inductive HlCtx where
  | tactics (info : Array (Highlighted.Goal Highlighted)) (startPos endPos : Nat)
  | span (info : Array (Highlighted.Span.Kind × String))

structure Hl where
  here : Highlighted
  context : Array (Highlighted × HlCtx)

def Hl.empty : Hl where
  here := .empty
  context := #[]

def Hl.close (hl : Hl) : Hl :=
  match hl.context.back? with
  | none => hl
  | some (left, .tactics info s e) => {
    here := left ++ .tactics info s e hl.here,
    context := hl.context.pop
  }
  | some (left, .span info) => {
    here := left ++ .span info hl.here,
    context := hl.context.pop
  }

def Hl.open (ctx : HlCtx) (hl : Hl) : Hl where
  here := .empty
  context := hl.context.push (hl.here, ctx)

def Hl.toHighlighted (hl : Hl) : Highlighted :=
  hl.context.foldr (init := hl.here) fun
    | (left, .tactics info startPos endPos), h => left ++ .tactics info startPos endPos h
    | (left, .span info), h => left ++ .span info h

instance : HAppend Hl Highlighted Hl where
  hAppend hl h :=
    { hl with here := appendHl hl.here h }

instance : HAppend Hl String Hl where
  hAppend hl s :=
    { hl with here := hl.here ++ s }

private def getLines (str : String) : Array String := Id.run do
  let mut iter := str.iter
  let mut lines := #[]
  let mut here := ""
  while h : iter.hasNext do
    let c := iter.curr' h
    iter := iter.next' h
    here := here.push c
    if c == '\n' then
      lines := lines.push here
      here := ""
  return lines.push here

def anchored' (hl : Highlighted) : Except String (HashMap String Highlighted) := do
  let mut out : HashMap String Highlighted := {}
  let mut openAnchors : HashMap String Hl := {}
  let mut todo := [some (normHl hl)]
  let mut ctx : Array HlCtx := #[]
  repeat
    match todo with
    | [] => break
    | none :: hs =>
      todo := hs
      ctx := ctx.pop
      openAnchors := openAnchors.map fun _ h => h.close
    | some (.text s) :: hs =>
      todo := hs
      for line in getLines s do
        match anchor? line with
        | none =>
          openAnchors := openAnchors.map fun _ hl => hl ++ line
        | some (a, true) =>
          if openAnchors.contains a then throw s!"Anchor already opened: {a}"
          if out.contains a then throw s!"Anchor already used: {a}"
          openAnchors := openAnchors.insert a { here := .empty, context := ctx.map (.empty, ·) }
        | some (a, false) =>
          if let some hl := openAnchors[a]? then
            out := out.insert a hl.toHighlighted
            openAnchors := openAnchors.erase a
          else throw s!"Anchor not open: {a}"
    | some h@(.token ..) :: hs | some h@(.point ..) :: hs =>
      todo := hs
      openAnchors := openAnchors.map fun _ hl => hl ++ h
    | some (.seq xs) :: hs =>
      todo := xs.toList.map some ++ hs
    | some (.tactics info startPos endPos x) :: hs =>
      ctx := ctx.push (.tactics info startPos endPos)
      todo := some x :: none :: hs
      openAnchors := openAnchors.map fun _ hl => hl.open (.tactics info startPos endPos)
    | some (.span info x) :: hs =>
      ctx := ctx.push (.span info)
      todo := some x :: none :: hs
      openAnchors := openAnchors.map fun _ hl => hl.open (.span info)
  if openAnchors.isEmpty then return out
  else throw s!"Unclosed anchors: {", ".intercalate openAnchors.keys}"

def anchored [Monad m] [MonadEnv m] [MonadLift IO m] [MonadError m] [MonadOptions m] (moduleName : Ident) (blame : Syntax) : m (HashMap String Highlighted) := do
  let modName := moduleName.getId
  let modStr := modName.toString

  if let some cached := (loadedModuleAnchorExt.getState (← getEnv)).find? modName then return cached

  let items ← Examples.Files.loadModuleContent modStr
  let highlighted := Highlighted.seq (items.map (·.code))

  match anchored' highlighted with
  | .error e => throwErrorAt blame e
  | .ok anchors => return anchors


deriving instance Repr for SubVerso.Module.ModuleItem

def withNl (s : String) : String := if s.endsWith "\n" then s else s ++ "\n"


@[code_block_expander module]
def module : CodeBlockExpander
  | args, code => do
    let (moduleName, anchor?) ← ArgParse.run ((·, ·) <$> .positional `module .ident <*> .named `anchor .ident true) args
    let modStr := moduleName.getId.toString
    let items ← Examples.Files.loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    if let some anchor := anchor? then
      try
        let anchors ← anchored moduleName anchor
        if let some hl := anchors[anchor.getId.toString]? then
          let _ ← ExpectString.expectString "module contents" code (hlToString hl |> withNl)
            (useLine := fun l => !l.trim.isEmpty)
          return #[← ``(Block.other (Block.leanDecl $(quote hl)) #[])]
        else
          logErrorAt anchor "Anchor not found"
          for x in anchors.keys do
            Suggestion.saveSuggestion anchor x x
          return #[]
      catch
        | .error ref e =>
          logErrorAt ref e
          return #[← ``(sorryAx _ true)]
        | e => throw e
    else
      let _ ← ExpectString.expectString "module contents" code (hlToString highlighted |> withNl)
        (useLine := fun l => !l.trim.isEmpty)
      return #[← ``(Block.other (Block.leanDecl $(quote highlighted)) #[])]

@[role_expander module]
def moduleInline : RoleExpander
  | args, inls => do
    let moduleName ← oneCodeName inls
    let anchor? ← ArgParse.run (.named `anchor .ident true) args
    let modStr := moduleName.getId.toString
    let items ← Examples.Files.loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    if let some anchor := anchor? then
      try
        let anchors ← anchored moduleName anchor
        if let some hl := anchors[anchor.getId.toString]? then
          return #[← ``(Inline.other (Inline.leanTerm $(quote hl)) #[])]
        else
          logErrorAt anchor "Anchor not found"
          for x in anchors.keys do
            Suggestion.saveSuggestion anchor x x
          return #[]
      catch
        | .error ref e =>
          logErrorAt ref e
          return #[← ``(sorryAx _ true)]
        | e => throw e
    else

      return #[← ``(Inline.other (Inline.leanTerm $(quote highlighted)) #[])]


private def matchingName? (hl : Highlighted) (name : String) : Option Token := do
  match hl with
  | .seq xs => xs.attach.findSome? fun ⟨x, _⟩ => matchingName? x name
  | .point .. | .text .. => none
  | .tactics _ _ _ x | .span _ x => matchingName? x name
  | .token t@⟨k, s⟩ =>
    match k with
    | .const .. | .var .. => if s == name then return t else none
    | _ => none

private partial def firstToken (hl : Highlighted) : Option (Highlighted × Highlighted) :=
  match hl with
  | .seq xs => do
    let mut xs := xs
    repeat
      if let some x := xs[0]? then
        xs := xs.drop 1
        if let some (t, xs') := firstToken x then
          return (t, xs' ++ .seq xs)
        else continue
      else failure
    failure
  | .point .. | .text .. => none
  | .tactics _ _ _ x | .span _ x => firstToken x
  | .token .. => pure (hl, .empty)

private def matchingExprPrefix? (hl : Highlighted) (term : String) : Option Highlighted := do
  let mut out : Highlighted := .empty
  let mut term := term
  let mut hl := hl
  while !term.isEmpty do
    let ws := term.takeWhile (·.isWhitespace)
    out := out ++ ws
    term := term.trimLeft
    let (first, rest) ← firstToken hl
    hl := rest
    let firstStr := hlToString first
    let term' ← term.dropPrefix? firstStr
    term := term'.toString
    out := out ++ first
  return out

private def matchingExpr? (hl : Highlighted) (term : String) : Option Highlighted := do
  let mut hl := hl
  repeat
    let (first, rest) ← firstToken hl
    if let some out := matchingExprPrefix? (first ++ rest) term then return out
    else hl := rest
  failure



private partial def toks (hl : Highlighted) : HashSet String :=
  match hl with
  | .seq xs => xs.map toks |>.foldl (init := {}) HashSet.union
  | .point .. | .text .. => {}
  | .tactics _ _ _ x | .span _ x => toks x
  | .token ⟨_, s⟩ => {s}

@[role_expander moduleName]
def moduleName : RoleExpander
  | args, inls => do
    let (moduleName, anchor?, show?) ←
      ArgParse.run ((·, ·, ·) <$> .positional `module .ident <*> .named `anchor .ident true <*> (.named `show .ident true)) args
    let name ← oneCodeStr inls

    let modStr := moduleName.getId.toString
    let items ← Examples.Files.loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    let fragment ←
      if let some anchor := anchor? then
        try
          let anchors ← anchored moduleName anchor
          if let some hl := anchors[anchor.getId.toString]? then
            pure hl
          else
            logErrorAt anchor "Anchor not found"
            for x in anchors.keys do
              Suggestion.saveSuggestion anchor x x
            return #[← ``(sorryAx _ true)]
          catch
            | .error ref e => logErrorAt ref e; return #[← ``(sorryAx _ true)]
            | e => throw e
      else pure highlighted

      if let some tok@⟨k, _txt⟩ := matchingName? fragment name.getString then
        let tok := show?.map (⟨k, ·.getId.toString⟩) |>.getD tok
        return #[← ``(Inline.other (Inline.leanTerm $(quote (Highlighted.token tok))) #[])]
      else
        logErrorAt name m!"'{name.getString}' not found in:{indentD (hlToString fragment)}"
        for t in toks fragment do
          Suggestion.saveSuggestion name t t
        return #[← ``(sorryAx _ true)]

@[role_expander moduleTerm]
def moduleTerm : RoleExpander
  | args, inls => do
    let (moduleName, anchor?) ← ArgParse.run ((·, ·) <$> .positional `module .ident <*> .named `anchor .ident true) args
    let term ← oneCodeStr inls

    let modStr := moduleName.getId.toString
    let items ← Examples.Files.loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    let fragment ←
      if let some anchor := anchor? then
        try
          let anchors ← anchored moduleName anchor
          if let some hl := anchors[anchor.getId.toString]? then
            pure hl
          else
            logErrorAt anchor "Anchor not found"
            for x in anchors.keys do
              Suggestion.saveSuggestion anchor x x
            return #[← ``(sorryAx _ true)]
        catch
          | .error ref e => logErrorAt ref e; return #[← ``(sorryAx _ true)]
          | e => throw e
      else pure highlighted

      if let some e := matchingExpr? fragment term.getString then
        return #[← ``(Inline.other (Inline.leanTerm $(quote e)) #[])]
      else
        logErrorAt term m!"Not found: '{term.getString}' in{indentD (hlToString fragment)}"
        return #[← ``(sorryAx _ true)]

def _root_.Verso.ArgParse.ValDesc.strLit [Monad m] [MonadError m] : ValDesc m StrLit where
  description := m!"a string"
  get
    | .str s => pure s
    | other => throwError "Expected string, got {toMessageData other}"




structure CommandConfig where
  container : Ident
  dir : StrLit
  «show» : Option StrLit := none
  viaShell : Bool := false

def CommandConfig.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m CommandConfig :=
  CommandConfig.mk <$> .positional `container .ident <*> .positional `dir .strLit <*> .named `show .strLit true <*> .namedD `shell .bool false

@[role_expander command]
def command : RoleExpander
  | args, inls => do
    let { container, dir, «show», viaShell } ← CommandConfig.parse.run args
    let cmd ← oneCodeStr inls
    let output ← Commands.command container dir.getString cmd (viaShell := viaShell)
    unless output.stdout.isEmpty do
      logSilentInfo <| "Stdout:\n" ++ output.stdout
    unless output.stderr.isEmpty do
      logSilentInfo <| "Stderr:\n" ++ output.stderr
    let out := «show».getD cmd |>.getString
    return #[← ``(Inline.code $(quote out ))]

structure CommandBlockConfig extends CommandConfig where
  command : StrLit

def CommandBlockConfig.parse [Monad m] [MonadError m] [MonadLiftT CoreM m] : ArgParse m CommandBlockConfig :=
  (fun container dir command «show» viaShell => {container, dir, command, «show», viaShell}) <$>
    .positional `container .ident <*>
    .positional `dir .strLit <*>
    .positional `command .strLit <*>
    .named `show .strLit true <*>
    .namedD `shell .bool false

@[block_role_expander command]
def commandBlock : BlockRoleExpander
  | args, blks => do
    unless blks.isEmpty do
      throwErrorAt (mkNullNode blks) "Expected no blocks"
    let { container, dir, command, «show», viaShell } ← CommandBlockConfig.parse.run args
    let output ← Commands.command container dir.getString command (viaShell := viaShell)
    unless output.stdout.isEmpty do
      logSilentInfo <| "Stdout:\n" ++ output.stdout
    unless output.stderr.isEmpty do
      logSilentInfo <| "Stderr:\n" ++ output.stderr
    let out := «show».getD command |>.getString
    return #[← ``(Block.code $(quote out))]

instance : Coe StrLit (TSyntax `argument) where
  coe stx := ⟨mkNode ``Verso.Syntax.anon #[mkNode ``Verso.Syntax.arg_str #[stx.raw]]⟩

macro_rules
  | `(block|```command $args* | $s```) => `(block|block_role{command $args* $s})

@[role_expander commandOut]
def commandOut : RoleExpander
  | args, inls => do
    let container ← ArgParse.run (.positional `container .ident) args
    let cmd ← oneCodeStr inls
    let output ← Commands.commandOut container cmd
    logSilentInfo output
    return #[← ``(Inline.code $(quote output ))]

@[code_block_expander commandOut]
def commandOutCodeBlock : CodeBlockExpander
  | args, outStr => do
    let (container, command) ← ArgParse.run ((·, ·) <$> .positional `container .ident <*> .positional `command .strLit) args
    let output ← Commands.commandOut container command

    _ ← ExpectString.expectString "command output" outStr (withNl output) (useLine := fun l => !l.trim.isEmpty) (preEq := String.trim)

    logSilentInfo output
    return #[← ``(Block.code $(quote output))]

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

@[code_block_expander plainFile]
def plainFile : CodeBlockExpander
  | args, expectedContentsStr => do
    let (file, show?) ← ArgParse.run ((·, ·) <$> .positional `file .strLit <*> (some <$> .positional `show .strLit <|> pure none)) args
    let show? := show?.map (·.getString)

    let projectDir : System.FilePath← Examples.Files.getProjectDir
    let fn :=  projectDir / file.getString
    let contents ← IO.FS.readFile fn

    let _ ← ExpectString.expectString "file" expectedContentsStr (withNl contents)
    logSilentInfo contents

    return #[← ``(Block.other (InlineLean.Block.exampleFile (FileType.other $(quote (show?.getD (fn.fileName.getD fn.toString))))) #[Block.code $(quote contents)])]
