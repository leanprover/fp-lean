import SubVerso.Examples
import Lean.Data.NameMap
import VersoManual

open Lean (NameMap MessageSeverity)


namespace FPLean


open Verso Doc Elab Genre.Manual ArgParse Code Highlighted WebAssets Output Html
open SubVerso.Highlighting
open Lean

-- TODO syntax highlighting for C#, TypeScript, Python etc (use the same technique as C in the manual)

@[code_block_expander CSharp]
def CSharp : CodeBlockExpander
  | _args, code => do
    return #[← ``(Block.code $(quote code.getString))]

@[role_expander CSharp]
def inlineCSharp : RoleExpander
  | _args, code => do
    let #[code] := code
      | throwErrorAt (mkNullNode code) "Expected exactly one code argument"
    let `(inline|code($code)) := code
      | throwErrorAt code "Exected code"
    return #[← ``(Inline.code $(quote code.getString))]

@[code_block_expander Kotlin]
def Kotlin : CodeBlockExpander
  | _args, code => do
    return #[← ``(Block.code $(quote code.getString))]

@[role_expander Kotlin]
def inlineKotlin : RoleExpander
  | _args, code => do
    let #[code] := code
      | throwErrorAt (mkNullNode code) "Expected exactly one code argument"
    let `(inline|code($code)) := code
      | throwErrorAt code "Exected code"
    return #[← ``(Inline.code $(quote code.getString))]

@[code_block_expander cpp]
def cpp : CodeBlockExpander
  | _args, code => do
    return #[← ``(Block.code $(quote code.getString))]

@[role_expander cpp]
def inlineCpp : RoleExpander
  | _args, code => do
    let #[code] := code
      | throwErrorAt (mkNullNode code) "Expected exactly one code argument"
    let `(inline|code($code)) := code
      | throwErrorAt code "Exected code"
    return #[← ``(Inline.code $(quote code.getString))]


@[code_block_expander typescript]
def typescript : CodeBlockExpander
  | _args, code => do
    return #[← ``(Block.code $(quote code.getString))]

@[role_expander typescript]
def inlineTypescript : RoleExpander
  | _args, code => do
    let #[code] := code
      | throwErrorAt (mkNullNode code) "Expected exactly one code argument"
    let `(inline|code($code)) := code
      | throwErrorAt code "Exected code"
    return #[← ``(Inline.code $(quote code.getString))]
