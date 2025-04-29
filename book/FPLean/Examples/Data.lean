import SubVerso.Examples
import Lean.Data.NameMap

import Verso

open Lean

namespace FPLean

open SubVerso Examples


local instance [ToJson α] : ToJson (NameMap α) where
  toJson nm := Json.mkObj <| nm.toList.map (fun (k, v) => (k.toString, ToJson.toJson v))

local instance [FromJson α] : FromJson (NameMap α) where
  fromJson?
    | .obj xs => do
      let objs ← xs.toArray.mapM (fun ⟨k, v⟩ => do return (k.toName, ← fromJson? v))
      return .fromArray objs _
    | other =>
      let what := other.compress
      let what := if what.length > 50 then what.take 50 ++ "…" else what
      throw s!"Expected object for a 'NameMap', got {what}"

instance [Repr α] : Repr (NameMap α) where
  reprPrec x p :=
    let doc := .group <| .nest 2 <| "fromList" ++ .line ++ repr x.toList ++ .line ++ "_"
    Repr.addAppParen doc p

structure Examples where
  code : NameMap (NameMap Example)
  messages : NameMap (NameMap (List (MessageSeverity × String)))
deriving Inhabited, ToJson, FromJson, Repr

def loadExampleProject (path : String) : IO Examples := do
  let loadedExamples ← loadExamples path
  return {
    code := loadedExamples
    messages := loadedExamples.filterMap fun _k v =>
      some <| v.filterMap fun _k v =>
        v.messages
  }

-- This could have been:
--
--    initialize
--     exampleCode : Examples ← loadExampleProject "../examples/"
--
-- but there's no need to do it again at run-time. It's super expensive to load the data, quote it,
-- and add it to the environment, so it is instead saved as JSON and reconstituted in the initializer.
open Lean Elab Command in
run_cmd do
  let exs ← loadExampleProject "../examples"
  let str := ToJson.toJson exs |>.compress
  let cmd ← `(def $(mkIdent `exampleCode.data) := $(quote str))
  elabCommand cmd

initialize
  exampleCode : Examples ←
    match Json.parse exampleCode.data with
    | .error err => throw <| IO.userError s!"Parse error with JSON examples: {err}"
    | .ok json =>
      match FromJson.fromJson? json with
      | .error err => throw <| IO.userError s!"Failed to deserialize JSON examples: {err}"
      | .ok v => pure v
