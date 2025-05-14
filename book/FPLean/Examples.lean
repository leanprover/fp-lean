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

def logSilentAt (ref : Syntax) (severity : MessageSeverity) (message : MessageData) : m Unit :=
  logAt ref message (severity := severity) (isSilent := true)

def logSilent (severity : MessageSeverity) (message : MessageData) : m Unit := do
  logSilentAt (← getRef) severity message

def logSilentInfoAt  (ref : Syntax) (message : MessageData) : m Unit :=
  logSilentAt ref .information message

def logSilentInfo (message : MessageData) : m Unit := do
  logSilent .information message

end

section
variable [Functor m]
defmethod ValDesc.withSyntax (desc : ValDesc m α) : ValDesc m (α × Syntax) where
  description := desc.description
  get v := (·, v.syntax) <$> desc.get v

def _root_.Verso.ArgParse.ValDesc.strLit [Monad m] [MonadError m] : ValDesc m StrLit where
  description := m!"a string"
  get
    | .str s => pure s
    | other => throwError "Expected string, got {toMessageData other}"

end


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


section
open FPLean.Examples Files

variable [Monad m] [MonadOptions m] [MonadError m] [MonadLiftT CoreM m]

private def defaultProject : m String := do
  if let some p := verso.exampleProject.get? (← getOptions) then pure p else throwError "No default project specified"

private def defaultModule : m Name := do
  if let some m := verso.exampleModule.get? (← getOptions) then pure m.toName else throwError "No default module specified"

def projectOrDefault : ArgParse m StrLit :=
  .named `project .strLit false <|> (Syntax.mkStrLit <$> .lift "default project" defaultProject) <|> .fail none (some m!"No `(project := ...)` parameter provided and no default project set")

def moduleOrDefault : ArgParse m Ident :=
  .named `module .ident false <|> (mkIdent <$> .lift "default module" defaultModule) <|> .fail none (some m!"No `(module := ...)` parameter provided and no default module set")

structure CodeModuleContext where
  module : Ident
  warningsAsErrors : Bool

def CodeModuleContext.parse : ArgParse m CodeModuleContext :=
  CodeModuleContext.mk <$> moduleOrDefault <*> .namedD `warningsAsErrors .bool false

structure CodeContext extends CodeModuleContext where
  anchor? : Option Ident

def CodeContext.parse : ArgParse m CodeContext :=
  CodeContext.mk <$> CodeModuleContext.parse <*> .named `anchor .ident true

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
        let i := hl.indentation
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
        let i := steps.map (·.indentation) |>.toList |>.min? |>.getD 0
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
        let i := hl.indentation
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
    _ ← ExpectString.expectString s!"'{name}' in '{module.getId}'" codeStr (Highlighted.seq ex.highlighted).toString
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
      let _ ← ExpectString.expectString s!"'{name.getId ++ `in}' in {module.getId}" codeStr (Highlighted.seq exIn.highlighted).toString
      return #[← ``(Block.other (Block.leanDecl $(quote (Highlighted.seq exIn.highlighted))) #[Block.code $(quote exIn.original)])]
    | some `FPLean.forMessage =>
      let _ ← ExpectString.expectString s!"'{name.getId}' in {module.getId}" codeStr (Highlighted.seq ex.highlighted).toString
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

@[code_block_expander exampleEval]
def exampleEvalCodeblock : CodeBlockExpander
  | args, str => do
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
        _ ← ExpectString.expectString "step" str (Highlighted.seq exIn.highlighted).toString (preEq := String.trim)
        return #[← ``(Block.other (Block.leanDecl $(quote (Highlighted.seq exIn.highlighted))) #[Block.code $(quote exIn.original)])]
      else
        let mut hls := #[]
        repeat
          let some exIn := mod.find? (name.getId ++ s!"step{hls.size}".toName)
            | break
          hls := hls.push (Highlighted.seq exIn.highlighted)
        if hls.size = 0 then
          throwErrorAt name m!"Example input not found: '{name.getId ++ `step0}"
        _ ← ExpectString.expectString "step" str ("\n===>\n".intercalate (hls.map (·.toString.trim) |>.toList) ++ "\n") (preEq := String.trim)
        return #[← ``(Block.other (Block.leanEvalSteps $(quote hls)) #[])]
    | _ =>
      throwErrorAt name m!"Expected example kind 'FPLean.evalSteps', got '{ex.kind}'"


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

def anchored [Monad m] [MonadEnv m] [MonadLift IO m] [MonadError m] [MonadOptions m] (moduleName : Ident) (blame : Syntax) : m Highlighted.AnchoredExamples := do
  let modName := moduleName.getId
  let modStr := modName.toString

  if let some cached := (loadedModuleAnchorExt.getState (← getEnv)).find? modName then return cached

  let items ← Examples.Files.loadModuleContent modStr
  let highlighted := Highlighted.seq (items.map (·.code))

  match highlighted.anchored with
  | .error e => throwErrorAt blame e
  | .ok anchors => return anchors


deriving instance Repr for SubVerso.Module.ModuleItem

def withNl (s : String) : String := if s.endsWith "\n" then s else s ++ "\n"

def warningsToErrors (hl : Highlighted) : Highlighted :=
  match hl with
  | .seq xs => .seq <| xs.map warningsToErrors
  | .point .warning str => .point .error str
  | .point .. => hl
  | .tactics info start stop x => .tactics info start stop <| warningsToErrors x
  | .span infos x => .span (infos.map fun (k, str) => (if k matches .warning then .error else k, str)) (warningsToErrors x)
  | .text .. | .token .. => hl

def allInfo (hl : Highlighted) : Array (MessageSeverity × String × Option Highlighted) :=
  match hl with
  | .seq xs => xs.flatMap allInfo
  | .point k str => #[(toSev k, str, none)]
  | .tactics _ _ _ x => allInfo x
  | .span infos x => (infos.map fun (k, str) => (toSev k, str, some x)) ++ allInfo x
  | .text .. | .token .. => #[]
where
  toSev : Highlighted.Span.Kind → MessageSeverity
    | .error => .error
    | .info => .information
    | .warning => .warning

@[code_block_expander module]
def module : CodeBlockExpander
  | args, code => do
    let {module := moduleName, anchor?, warningsAsErrors} ← CodeContext.parse.run args
    let modStr := moduleName.getId.toString
    let items ← Examples.Files.loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    let highlighted := if warningsAsErrors then warningsToErrors highlighted else highlighted
    if let some anchor := anchor? then
      try
        let {anchors, ..} ← anchored moduleName anchor
        if let some hl := anchors[anchor.getId.toString]? then
          let _ ← ExpectString.expectString "module contents" code (hl.toString |> withNl)
            (useLine := fun l => !l.trim.isEmpty)
          for (sev, msg, _) in allInfo hl do
            logSilentInfo m!"{sevStr sev}:\n{msg}"
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
      let _ ← ExpectString.expectString "module contents" code (highlighted.toString |> withNl)
        (useLine := fun l => !l.trim.isEmpty)
      for (sev, msg, _) in allInfo highlighted do
        logSilentInfo m!"{sevStr sev}:\n{msg}"
      return #[← ``(Block.other (Block.leanDecl $(quote highlighted)) #[])]
where
  sevStr
    | .error => "error"
    | .warning => "warning"
    | .information => "info"

macro_rules
  | `(block|```anchor $arg:arg_val $args* | $s ```) =>
    `(block|```module anchor:=$arg $args* | $s ```)
  | `(block|```%$tok anchor $args* | $_s ```) =>
    Macro.throwErrorAt (mkNullNode (#[tok] ++ args)) "Expected a positional identifier as first argument"

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
        let {anchors, ..} ← anchored moduleName anchor
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

macro_rules
  | `(inline|role{ anchor $arg:arg_val $args* } [%$t1 $s ]%$t2) =>
    `(inline|role{ module anchor:=$arg $args* } [%$t1 $s ]%$t2)
  | `(inline|role{%$tok anchor $args* } [ $_s ]) =>
    Macro.throwErrorAt (mkNullNode (#[tok] ++ args)) "Expected a positional identifier as first argument"

private partial def allTokens (hl : Highlighted) : HashSet String :=
  match hl with
  | .seq xs => xs.map allTokens |>.foldl (init := {}) HashSet.union
  | .point .. | .text .. => {}
  | .tactics _ _ _ x | .span _ x => allTokens x
  | .token ⟨_, s⟩ => {s}

@[role_expander moduleName]
def moduleName : RoleExpander
  | args, inls => do
    let ({module := moduleName, anchor?, warningsAsErrors}, show?) ←
      ArgParse.run ((·, ·) <$> CodeContext.parse <*> (.named `show .ident true)) args
    let name ← oneCodeStr inls

    let modStr := moduleName.getId.toString
    let items ← Examples.Files.loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    let fragment ←
      if let some anchor := anchor? then
        try
          let {anchors, ..} ← anchored moduleName anchor
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
    let fragment := if warningsAsErrors then warningsToErrors fragment else fragment

    if let some tok@⟨k, _txt⟩ := fragment.matchingName? name.getString then
      let tok := show?.map (⟨k, ·.getId.toString⟩) |>.getD tok
      return #[← ``(Inline.other (Inline.leanTerm $(quote (Highlighted.token tok))) #[])]
    else
      logErrorAt name m!"'{name.getString}' not found in:{indentD fragment.toString}"
      for t in allTokens fragment do
        Suggestion.saveSuggestion name t t
      return #[← ``(sorryAx _ true)]

@[role_expander moduleTerm]
def moduleTerm : RoleExpander
  | args, inls => do
    let {module := moduleName, anchor?, warningsAsErrors} ← CodeContext.parse.run args
    let term ← oneCodeStr inls

    let modStr := moduleName.getId.toString
    let items ← Examples.Files.loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    let highlighted := if warningsAsErrors then warningsToErrors highlighted else highlighted
    let fragment ←
      if let some anchor := anchor? then
        try
          let {anchors, ..} ← anchored moduleName anchor
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

      if let some e := fragment.matchingExpr? term.getString then
        return #[← ``(Inline.other (Inline.leanTerm $(quote e)) #[])]
      else
        logErrorAt term m!"Not found: '{term.getString}' in{indentD fragment.toString}"
        return #[← ``(sorryAx _ true)]

macro_rules
  | `(inline|role{%$rs anchorTerm $a:arg_val $arg* }%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleTerm $arg*  anchor:=$a }%$re [%$s $str* ]%$e)



def severityName {m} [Monad m] [MonadEnv m] [MonadResolveName m] : MessageSeverity → m String
  | .error => unresolveNameGlobal ``MessageSeverity.error <&> (·.toString)
  | .warning => unresolveNameGlobal ``MessageSeverity.warning <&> (·.toString)
  | .information => unresolveNameGlobal ``MessageSeverity.information <&> (·.toString)

@[code_block_expander moduleOut]
def moduleOut : CodeBlockExpander
  | args, str => do
    let (severity, {module := moduleName, anchor?, warningsAsErrors}) ← ArgParse.run ((·, ·) <$> .positional `severity (.withSyntax .messageSeverity) <*> CodeContext.parse) args

    let modStr := moduleName.getId.toString
    let items ← Examples.Files.loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    let fragment ←
      if let some anchor := anchor? then
        try
          let {anchors, ..} ← anchored moduleName anchor
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
    let fragment := if warningsAsErrors then warningsToErrors fragment else fragment

    let infos : Array _ := allInfo fragment

    for (sev, msg, _) in infos do
      if messagesMatch msg str.getString then
        if sev == severity.1 then
          return #[← ``(Block.other (Block.leanOutput $(quote sev) $(quote msg)) #[])]
        else
        let wanted ← severityName sev
          if severity.2.getHeadInfo matches .original .. then
            Suggestion.saveSuggestion severity.2 wanted wanted
          throwError "Mismatched severity. Expected '{repr severity.1}', got '{wanted}'."

    -- Didn't find it. Add suggestions.
    for (_, msg, _) in infos do
      Suggestion.saveSuggestion str (ExpectString.abbreviateString msg) (withNl msg)

    let err := m!"Expected one of:{indentD (m!"\n".joinSep <| infos.toList.map (·.2.1))}\nbut got:{indentD str.getString}"
    logErrorAt str err

    return #[← ``(sorryAx _ true)]

macro_rules
  | `(block|```moduleInfo $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.information $arg* | $s ```)
  | `(block|```moduleError $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.error $arg* | $s ```)
  | `(block|```moduleWarning $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.warning $arg* | $s ```)
  | `(block|```anchorInfo $a:arg_val $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.information anchor:=$a $arg* | $s ```)
  | `(block|```anchorError $a:arg_val $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.error anchor:=$a $arg* | $s ```)
  | `(block|```anchorWarning $a:arg_val $arg* | $s ```) =>
    `(block|```moduleOut MessageSeverity.warning anchor:=$a $arg* | $s ```)

@[role_expander moduleOut]
def moduleOutRole : RoleExpander
  | args, inls => do

    let str? ← oneCodeStr? inls

    let (severity, {module := moduleName, anchor?, warningsAsErrors}) ← ArgParse.run ((·, ·) <$> .positional `severity (.withSyntax .messageSeverity) <*> CodeContext.parse) args

    let modStr := moduleName.getId.toString
    let items ← Examples.Files.loadModuleContent modStr
    let highlighted := Highlighted.seq (items.map (·.code))
    let fragment ←
      if let some anchor := anchor? then
        try
          let {anchors, ..} ← anchored moduleName anchor
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
    let fragment := if warningsAsErrors then warningsToErrors fragment else fragment

    let infos := allInfo fragment

    if let some str := str? then
      for (sev, msg, _) in infos do
        if messagesMatch msg str.getString then
          if sev == severity.1 then
            return #[← ``(Inline.other (Inline.leanOutput $(quote sev) $(quote msg) true) #[])]
          else
          let wanted ← severityName sev
            if severity.2.getHeadInfo matches .original .. then
              Suggestion.saveSuggestion severity.2 wanted wanted
            throwError "Mismatched severity. Expected '{repr severity.1}', got '{wanted}'."

      -- Didn't find it. Add suggestions.
      for (_, msg, _) in infos do
        Suggestion.saveSuggestion str (quoteCode <| ExpectString.abbreviateString msg.trim) msg.trim

      let err := m!"Expected one of:{indentD (m!"\n".joinSep <| infos.toList.map (·.2.1))}\nbut got:{indentD str.getString}"
      logErrorAt str err
    else
      let err := m!"Expected one of:{indentD (m!"\n".joinSep <| infos.toList.map (·.2.1))}"
      logError m!"No expected term provided. {err}"
      if let `(inline|role{$_ $_*} [%$tok1 $contents* ]%$tok2) := (← getRef) then
        let stx :=
          if tok1.getHeadInfo matches .original .. && tok2.getHeadInfo matches .original .. then
            mkNullNode #[tok1, tok2]
          else mkNullNode contents
        for (_, msg, _) in infos do
          Suggestion.saveSuggestion stx (quoteCode <| ExpectString.abbreviateString msg.trim) (quoteCode msg.trim)

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
  | `(inline|role{%$rs moduleInfo $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.information $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs moduleError $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.error $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs moduleWarning $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.warning $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs anchorInfo $a:arg_val $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.information anchor:=$a $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs anchorError $a:arg_val $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.error anchor:=$a $arg*}%$re [%$s $str* ]%$e)
  | `(inline|role{%$rs anchorWarning $a:arg_val $arg*}%$re [%$s $str* ]%$e) =>
    `(inline|role{%$rs moduleOut MessageSeverity.warning anchor:=$a $arg*}%$re [%$s $str* ]%$e)

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
