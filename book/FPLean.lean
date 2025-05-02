import VersoManual

import FPLean.Intro
import FPLean.GettingToKnow
import FPLean.HelloWorld

open Verso.Genre Manual

open Verso Doc Elab in
open Lean (quote) in
@[role_expander versionString]
def versionString : RoleExpander
  | #[], #[] => do
    let version ← IO.FS.readFile "../examples/lean-toolchain"
    let version := version.stripPrefix "leanprover/lean4:" |>.trim
    pure #[← ``(Verso.Doc.Inline.code $(quote version))]
  | _, _ => throwError "Unexpected arguments"


#doc (Manual) "Functional Programming in Lean" =>

%%%
authors := ["David Thrane Christiansen"]
%%%


_Copyright Microsoft Corporation 2023 and Lean FRO, LLC 2023–2025_



This is a free book on using Lean as a programming language. All code samples are tested with Lean release {versionString}[].

{include 1 FPLean.Intro}

{include 1 FPLean.GettingToKnow}

{include 1 FPLean.HelloWorld}
