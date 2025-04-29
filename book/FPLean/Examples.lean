import SubVerso.Examples
import Lean.Data.NameMap
import VersoManual
import FPLean.Examples.Data
import FPLean.Examples.OtherLanguages

open Lean (NameMap MessageSeverity)


namespace FPLean


open Verso Doc Elab Genre.Manual ArgParse Code Highlighted WebAssets Output Html
open SubVerso.Highlighting
open SubVerso.Examples.Messages
open Lean

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
    | some `FPLean.decl =>
      let some exIn := mod.find? (name.getId ++ `in)
        | throwErrorAt name "Example input not found: '{name.getId ++ `in}'"
      return #[← ``(Block.other (Block.leanDecl $(quote (Highlighted.seq exIn.highlighted))) #[Block.code $(quote exIn.original)])]
    | some `FPLean.forMessage =>
      return #[← ``(Block.other (Block.leanDecl $(quote (Highlighted.seq ex.highlighted))) #[Block.code $(quote ex.original)])]
    | _ =>
      throwErrorAt name m!"Expected example kind 'FPLean.inputOutput' or 'FPLean.forMessage', got '{ex.kind}'"

  | _args, _blocks =>
    throwError "Unexpected block arguments"

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
    | some `FPLean.forMessage =>
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
    | some `FPLean.forMessage =>
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
    | some `FPLean.decl =>
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
