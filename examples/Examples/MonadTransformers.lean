import Examples.Support
import Examples.Monads

namespace Evaluator

inductive Prim where
  | plus
  | minus
  | times
  | div

def Var := String

deriving instance BEq, ToString for Var

inductive Expr where
  | var : Var → Expr
  | prim : Prim → Expr → Expr → Expr
  | const : Int → Expr
  | lett : Var → Expr → Expr → Expr

abbrev Env := List (Var × Int)

def Eval (α : Type) : Type :=
  Env → Except String α

instance : Monad Eval where
  pure x := fun _ => .ok x
  bind m f := fun ρ =>
    match m ρ with
    | .error e => .error e
    | .ok x => f x ρ

def currentEnv : Eval Env := fun ρ => .ok ρ

def bind (x : Var) (v : Int) (during : Eval α) : Eval α :=
  fun ρ =>
    during ((x, v) :: ρ)

def crash (msg : String) : Eval α :=
  fun _ => .error msg

def lookup (x : Var) : Eval Int := do
  let ρ ← currentEnv
  match ρ.lookup x with
  | none => crash s!"Unknown variable {x}"
  | some i => pure i

def applyPrim (op : Prim) (v1 v2 : Int) : Eval Int :=
  match op with
  | .plus => pure (v1 + v2)
  | .minus => pure (v1 - v2)
  | .times => pure (v1 * v2)
  | .div =>
    if v2 == 0 then
      crash s!"Attempted to divide {v1} by 0"
    else
      pure (v1 + v2)

def evaluate : Expr → Eval Int
  | .var x => lookup x
  | .prim op e1 e2 => do
    let v1 ← evaluate e1
    let v2 ← evaluate e2
    applyPrim op v1 v2
  | .const i => pure i
  | .lett x e1 e2 => do
    let v1 ← evaluate e1
    bind x v1 (evaluate e2)

end Evaluator


namespace DirTree


book declaration {{{ Config }}}
  structure Config where
    useASCII : Bool := false
    currentPrefix : String := ""
stop book declaration


book declaration {{{ filenames }}}
  def Config.preFile (cfg : Config) :=
    if cfg.useASCII then "|--" else "├──"

  def Config.preDir (cfg : Config) :=
    if cfg.useASCII then "|  " else "│  "

  def Config.fileName (cfg : Config) (file : String) : String :=
    s!"{cfg.currentPrefix}{cfg.preFile} {file}"

  def Config.dirName (cfg : Config) (dir : String) : String :=
    s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"
stop book declaration


book declaration {{{ inDirectory }}}
  def Config.inDirectory (cfg : Config) : Config :=
    {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}
stop book declaration

book declaration {{{ configFromArgs }}}
  def configFromArgs : List String → Option Config
    | [] => some {}
    | ["--ascii"] => some {useASCII := true}
    | _ => none
stop book declaration


book declaration {{{ usage }}}
def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"
stop book declaration


book declaration {{{ Entry }}}
  inductive Entry where
    | file : String → Entry
    | dir : String → Entry
stop book declaration


book declaration {{{ toEntry }}}
  def toEntry (path : System.FilePath) : IO (Option Entry) := do
    match path.components.getLast? with
    | none => pure (some (.dir ""))
    | some "." | some ".." => pure none
    | some name =>
      pure (some (if (← path.isDir) then .dir name else .file name))
stop book declaration

namespace Old


book declaration {{{ OldShowFile }}}
  def showFileName (cfg : Config) (file : String) : IO Unit := do
    IO.println (cfg.fileName file)

  def showDirName (cfg : Config) (dir : String) : IO Unit := do
    IO.println (cfg.dirName dir)
stop book declaration


book declaration {{{ doList }}}
  def doList : (List α) → (α → IO Unit) → IO Unit
    | [], _ => pure ()
    | x :: xs, action => do
      action x
      doList xs action
stop book declaration

book declaration {{{ OldDirTree }}}
  partial def dirTree (cfg : Config) (path : System.FilePath) : IO Unit := do
    match (← toEntry path) with
    | none => pure ()
    | some (.file name) => showFileName cfg name
    | some (.dir name) =>
      showDirName cfg name
      let contents ← path.readDir
      let newConfig := cfg.inDirectory
      doList contents.toList fun d =>
        dirTree newConfig d.path
stop book declaration

book declaration {{{ OldMain }}}
  def main (args : List String) : IO UInt32 := do
    match configFromArgs args with
    | some config =>
      dirTree config (← IO.currentDir)
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
      IO.eprintln usage
      pure 1
stop book declaration

-- #eval main ["--ascii"]


end Old

namespace Readerish

def ConfigIO (β : Type) (α : Type) : Type := β → IO α

instance : Monad (ConfigIO β) where
  pure x := fun _ => pure x
  bind m f := fun cfg => do
    let v ← m cfg
    f v cfg

def config {β : Type} : ConfigIO β β := fun x => pure x

def locally (change : β → γ) (action : ConfigIO γ α) : ConfigIO β α :=
  fun cfg => action (change cfg)

def io (action : IO α) : ConfigIO β α :=
  fun _ => action

def showFileName (file : String) : ConfigIO Config Unit := do
  io (IO.println ((← config).fileName file))

def showDirName (dir : String) : ConfigIO Config Unit := do
  io (IO.println ((← config).dirName dir))

def doList : (List α) → (α → ConfigIO β Unit) → ConfigIO β Unit
  | [], _ => pure ()
  | x :: xs, action => do
    action x
    doList xs action

def inDir (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}

partial def dirTree (path : System.FilePath) : ConfigIO Config Unit := do
  match path.fileName with
  | none => pure ()
  | some name =>
    if !(← io path.isDir) then
      showFileName name
    else
      showDirName name
      let contents ← io path.readDir
      locally inDir (doList contents.toList (fun d => dirTree d.path))
end Readerish

namespace T

abbrev ConfigIO (β : Type) (α : Type) : Type := ReaderT β IO α

def showFileName (file : String) : ConfigIO Config Unit := do
  IO.println s!"{(← read).currentPrefix} {file}"

def showDirName (dir : String) : ConfigIO Config Unit := do
  IO.println s!"{(← read).currentPrefix} {dir}/"

def inDir (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}

partial def dirTree (path : System.FilePath) : ConfigIO Config Unit := do
  match path.fileName with
  | none => pure ()
  | some name =>
    if !(← path.isDir) then
      showFileName name
    else
      showDirName name
      for d in (← path.readDir) do dirTree d.path

end T

end DirTree


namespace MyVersions

def ReaderT (ρ : Type) (m : Type → Type) (α : Type) : Type :=
  ρ → m α

end MyVersions

example : ReaderT = MyVersions.ReaderT := by rfl
