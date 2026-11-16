/-
Copyright (c) 2026 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
module
public import Lean.Elab.Attributes
public meta import Lean.DocString.Parser
public meta import Lean.DocString.View

public section

/-!
Macros for roles of a given name.

A function of type {lit}`RoleView → MacroM Syntax` with the attribute {lit}`@[role_macro name]`
rewrites each use of the role {lit}`name` into the syntax that it returns.
-/

namespace FPLean
open Lean Elab
open Lean.Doc (RoleView)

/-- The macro that applies `f` to each use of the role `name`. -/
meta def roleMacro (name : Name) (f : RoleView → MacroM Syntax) : Macro := fun stx => do
  let some v := RoleView.of ⟨stx⟩ | Macro.throwUnsupported
  unless v.name.getId.eraseMacroScopes == name do Macro.throwUnsupported
  f v

/--
Syntax for the same role as `v` that has the name `name` and the arguments `args`.

The braces, brackets, and content of `v` are kept.
-/
meta def _root_.Lean.Doc.RoleView.withNameArgs (v : RoleView) (name : Name)
    (args : TSyntaxArray ``Lean.Doc.Parser.arg) : MacroM Syntax := do
  let name := mkIdentFrom v.name name
  let (bo, bc, inl) := (v.braceOpen, v.braceClose, v.content)
  match v.brackets with
  | some (so, sc) =>
    `(Lean.Doc.Parser.Inline.role| {%$bo $name:ident $args* }%$bc [%$so $inl* ]%$sc)
  | none =>
    `(Lean.Doc.Parser.Inline.role| {%$bo $name:ident $args* }%$bc $inl:inline*)

/-- Marks a function of type {lit}`RoleView → MacroM Syntax` as the macro for a role. -/
syntax (name := role_macro) "role_macro " ident : attr

initialize registerBuiltinAttribute {
  name := `role_macro
  descr := "Rewrites each use of a role with a function of type `RoleView → MacroM Syntax`"
  applicationTime := .afterCompilation
  add declName stx kind := do
    let `(attr| role_macro $roleName:ident) := stx
      | throwError "Invalid `role_macro` attribute"
    let n := declName ++ `roleMacro
    let decl := Declaration.defnDecl {
      name := n
      levelParams := []
      type := mkConst ``Macro
      value := mkApp2 (mkConst ``roleMacro) (toExpr roleName.getId) (mkConst declName)
      hints := .opaque
      safety := .safe
    }
    addDecl decl
    if (← getEnv).header.isModule then
      modifyEnv (markMeta · n)
    compileDecl decl
    Attribute.add n `macro (← `(attr| macro $(mkIdent ``Lean.Doc.Parser.Inline.role):ident)) kind
}
