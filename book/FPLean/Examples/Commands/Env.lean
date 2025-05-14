import Lean.Environment
import Std.Data.HashMap
import SubVerso.Highlighting.Highlighted
import SubVerso.Module


open Lean Std

open SubVerso Highlighting Module Highlighted

namespace FPLean

structure Container where
  /-- The container's temporary working directory -/
  workingDirectory : System.FilePath
  /-- The saved outputs from each command run in the container -/
  outputs : HashMap String String := {}

initialize containersExt : (EnvExtension (NameMap Container)) ← registerEnvExtension (pure {})

initialize loadedModulesExt : (EnvExtension (NameMap (Array ModuleItem))) ← registerEnvExtension (pure {})

initialize loadedModuleAnchorExt : (EnvExtension (NameMap AnchoredExamples)) ← registerEnvExtension (pure {})
