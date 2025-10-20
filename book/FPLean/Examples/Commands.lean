import FPLean.Examples.Commands.Env
import FPLean.Examples.Commands.ShLex
import Lean.Elab
import Verso.FS

namespace FPLean.Commands
open Lean

variable {m : _} [Monad m] [MonadEnv m] [MonadLiftT IO m] [MonadLiftT BaseIO m] [MonadError m]

def ensureContainer (container : Ident) : m Container := do
  let name := container.getId
  if let some c := (containersExt.getState (← getEnv)).find? name then return c
  let tmp ← IO.FS.createTempDir
  let c : Container := ⟨tmp, {}⟩
  let projectRoot : System.FilePath := ".."
  let copyErrors : IO.Ref (Array String) ← IO.mkRef #[]
  Verso.FS.copyRecursively (fun s => copyErrors.modify (·.push s)) projectRoot tmp shouldCopy
  let errs ← (copyErrors.get : IO _)
  unless errs.isEmpty do
    throwErrorAt container "Errors copying project to container {name}: {indentD <| MessageData.joinSep (errs.toList.map toMessageData) Format.line}"
  modifyEnv (containersExt.modifyState · (·.insert name c))
  return c
where
  shouldCopy (path : System.FilePath) : IO Bool := do
    let some x := path.fileName
      | return true
    return !(x.startsWith ".") && !(x == "site-packages") && !(x == "_out") && !(x == "static")

def requireContainer (container : Ident) : m Container := do
  let name := container.getId
  if let some c := (containersExt.getState (← getEnv)).find? name then return c
  else throwErrorAt container "Not found: '{name}'"

private def localeVars : Array String :=
  #["LANG", "LC_ALL"]

def command (container : Ident) (dir : System.FilePath) (command : StrLit) (viaShell := false) : m IO.Process.Output := do
  let c ← ensureContainer container
  unless dir.isRelative do
    throwError "Relative directory expected, got '{dir}'"
  let dir := c.workingDirectory / "examples" / dir
  IO.FS.createDirAll dir
  let (cmd, args) ← if viaShell then pure ("bash", #["-c", command.getString]) else cmdAndArgs
  let extraPath := (← IO.currentDir) / ".." / "examples" / ".lake" / "build" / "bin" |>.toString
  let extraPath := if extraPath.contains ' ' || extraPath.contains '"' || extraPath.contains '\'' then extraPath.quote else extraPath
  let path := (← IO.getEnv "PATH").map (System.SearchPath.separator.toString ++ ·) |>.getD ""
  let out ← IO.Process.output {
    cmd := cmd,
    args := args,
    cwd := dir,
    env := #[("PATH", some (extraPath ++ path))] ++ localeVars.map (·, some "C.UTF-8")
  }
  if out.exitCode != 0 then
    let stdout := m!"Stdout: {indentD out.stdout}"
    let stderr := m!"Stderr: {indentD out.stderr}"
    throwErrorAt command "Non-zero exit code from '{command.getString}' ({out.exitCode}).\n{indentD stdout}\n{indentD stderr}"
  modifyEnv (containersExt.modifyState · (·.insert container.getId { c with outputs := c.outputs.insert command.getString.trim out.stdout }))
  return out

where
  cmdAndArgs : m (String × Array String) := do
    match Shell.shlex command.getString with
    | .error e => throwErrorAt command e
    | .ok components =>
      if h : components.size = 0 then
        throwErrorAt command "No command provided"
      else
        return (components[0], components.extract 1)


def commandOut (container : Ident) (command : StrLit) : m String := do
  let c ← requireContainer container
  if let some out := c.outputs[command.getString.trim]? then
    return out
  else throwErrorAt command "Output not found: {indentD command}"

def fileContents (container : Ident) (file : StrLit) : m String := do
  let c ← requireContainer container
  let filename := c.workingDirectory / "examples" / file.getString
  unless (← filename.pathExists) do
    throwErrorAt file "{filename} does not exist"
  if (← filename.isDir) then
    throwErrorAt file "{filename} is a directory"
  IO.FS.readFile filename


end Commands
