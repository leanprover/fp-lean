import VersoManual

import FPLean.Intro
import FPLean.Acks
import FPLean.GettingToKnow
import FPLean.HelloWorld
import FPLean.PropsProofsIndexing
import FPLean.TypeClasses
import FPLean.Monads
import FPLean.FunctorApplicativeMonad
import FPLean.MonadTransformers
import FPLean.DependentTypes
import FPLean.TacticsInductionProofs
import FPLean.ProgramsProofs
import FPLean.NextSteps

open Verso.Genre Manual
open Verso Code External

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

{include 1 FPLean.Acks}

{include 1 FPLean.GettingToKnow}

{include 1 FPLean.HelloWorld}

{include 1 FPLean.PropsProofsIndexing}

{include 1 FPLean.TypeClasses}

{include 1 FPLean.Monads}

{include 1 FPLean.FunctorApplicativeMonad}

{include 1 FPLean.MonadTransformers}

{include 1 FPLean.DependentTypes}

{include 1 FPLean.TacticsInductionProofs}

{include 1 FPLean.ProgramsProofs}

{include 1 FPLean.NextSteps}
