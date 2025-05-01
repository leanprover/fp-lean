/-
Copyright (c) 2023-2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/
import SubVerso.Helper
import SubVerso.Module
import MD4Lean
import FPLean.Examples.Commands.Env

open Lean

open SubVerso.Highlighting
open SubVerso.Helper
open SubVerso.Module

namespace FPLean.Examples.Files

open System in
def loadModuleContent' (mod : String) (overrideToolchain : Option String := none) : IO (Array ModuleItem) := do

  let projectDir : FilePath := "../examples"

  -- Validate that the path is really a Lean project
  let lakefile := projectDir / "lakefile.lean"
  let lakefile' := projectDir / "lakefile.toml"
  if !(← lakefile.pathExists) && !(← lakefile'.pathExists) then
    throw <| .userError s!"Neither {lakefile} nor {lakefile'} exist, couldn't load project"
  let toolchain ← match overrideToolchain with
    | none =>
      let toolchainfile := projectDir / "lean-toolchain"
      if !(← toolchainfile.pathExists) then
        throw <| .userError s!"File {toolchainfile} doesn't exist, couldn't load project"
      pure (← IO.FS.readFile toolchainfile).trim
    | some override => pure override

  -- Kludge: remove variables introduced by Lake. Clearing out DYLD_LIBRARY_PATH and
  -- LD_LIBRARY_PATH is useful so the version selected by Elan doesn't get the wrong shared
  -- libraries.
  let lakeVars :=
    #["LAKE", "LAKE_HOME", "LAKE_PKG_URL_MAP",
      "LEAN_SYSROOT", "LEAN_AR", "LEAN_PATH", "LEAN_SRC_PATH",
      "ELAN_TOOLCHAIN", "DYLD_LIBRARY_PATH", "LD_LIBRARY_PATH"]


  IO.FS.withTempFile fun h f => do
    let cmd := "elan"
    let args := #["run", "--install", toolchain, "lake", "env", "which", "subverso-extract-mod"]

    let res ← IO.Process.output {
      cmd, args, cwd := projectDir
      -- Unset Lake's environment variables
      env := lakeVars.map (·, none)
    }
    if res.exitCode != 0 then
      let args := #["run", "--install", toolchain, "lake", "build", "subverso-extract-mod"]

      let res ← IO.Process.output {
        cmd, args, cwd := projectDir
        -- Unset Lake's environment variables
        env := lakeVars.map (·, none)
      }
      if res.exitCode != 0 then reportFail projectDir cmd args res

    let args := #["run", "--install", toolchain, "lake", "env", "subverso-extract-mod", mod, f.toString]
    let res ← IO.Process.output {
      cmd, args, cwd := projectDir
      -- Unset Lake's environment variables
      env := lakeVars.map (·, none)
    }
    if res.exitCode != 0 then reportFail projectDir cmd args res
    h.rewind

    let .ok (.arr json) := Json.parse (← h.readToEnd)
      | throw <| IO.userError s!"Expected JSON array"
    match json.mapM fromJson? with
    | .error err =>
      throw <| IO.userError s!"Couldn't parse JSON from output file: {err}\nIn:\n{json}"
    | .ok val => pure val

where
  decorateOut (name : String) (out : String) : String :=
    if out.isEmpty then "" else s!"\n{name}:\n{out}\n"
  reportFail {α} (projectDir : FilePath) (cmd : String) (args : Array String) (res : IO.Process.Output) : IO α := do
    IO.eprintln <|
      "Build process failed." ++
      "\nCWD: " ++ projectDir.toString ++
      "\nCommand: " ++ cmd ++
      "\nArgs: " ++ repr args ++
      "\nExit code: " ++ toString res.exitCode ++
      "\nstdout: " ++ res.stdout ++
      "\nstderr: " ++ res.stderr

    throw <| .userError <|
      "Build process failed." ++
      decorateOut "stdout" res.stdout ++
      decorateOut "stderr" res.stderr

open FPLean

variable [Monad m] [MonadLift IO m] [MonadEnv m]

def loadModuleContent (mod : String) (overrideToolchain : Option String := none) : m (Array ModuleItem) := do
  let modName := mod.toName
  if let some m := (loadedModulesExt.getState (← getEnv)).find? modName then return m
  else
    let items ← loadModuleContent' mod overrideToolchain
    modifyEnv (loadedModulesExt.modifyState · (·.insert modName items))
    return items
