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


book declaration {{{ doList }}}
  def doList [Monad m] : List α → (α → m Unit) → m Unit
    | [], _ => pure ()
    | x :: xs, action => do
      action x
      doList xs action
stop book declaration

namespace Old


book declaration {{{ OldShowFile }}}
  def showFileName (cfg : Config) (file : String) : IO Unit := do
    IO.println (cfg.fileName file)

  def showDirName (cfg : Config) (dir : String) : IO Unit := do
    IO.println (cfg.dirName dir)
stop book declaration

book declaration {{{ OldDirTree }}}
  partial def dirTree (cfg : Config) (path : System.FilePath) : IO Unit := do
    match ← toEntry path with
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


book declaration {{{ ConfigIO }}}
  def ConfigIO (α : Type) : Type :=
    Config → IO α

  instance : Monad ConfigIO where
    pure x := fun _ => pure x
    bind result next := fun cfg => do
      let v ← result cfg
      next v cfg
stop book declaration


book declaration {{{ currentConfig }}}
  def currentConfig : ConfigIO Config :=
    fun cfg => pure cfg
stop book declaration


book declaration {{{ locally }}}
  def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
    fun cfg => action (change cfg)
stop book declaration


book declaration {{{ runIO }}}
  def runIO (action : IO α) : ConfigIO α :=
    fun _ => action
stop book declaration


book declaration {{{ MedShowFileDir }}}
  def showFileName (file : String) : ConfigIO Unit := do
    runIO (IO.println ((← currentConfig).fileName file))

  def showDirName (dir : String) : ConfigIO Unit := do
    runIO (IO.println ((← currentConfig).dirName dir))
stop book declaration



book declaration {{{ MedDirTree }}}
  partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
    match ← runIO (toEntry path) with
      | none => pure ()
      | some (.file name) => showFileName name
      | some (.dir name) =>
        showDirName name
        let contents ← runIO path.readDir
        locally (·.inDirectory)
          (doList contents.toList fun d =>
            dirTree d.path)
stop book declaration


book declaration {{{ MedMain }}}
  def main (args : List String) : IO UInt32 := do
      match configFromArgs args with
      | some config =>
        dirTree (← IO.currentDir) config
        pure 0
      | none =>
        IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
        IO.eprintln usage
        pure 1
stop book declaration

-- #eval main ["--ascii"]

end Readerish

namespace T

abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α

def showFileName (file : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {file}"

def showDirName (dir : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {dir}/"

  partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
    match ← toEntry path with
      | none => pure ()
      | some (.file name) => showFileName name
      | some (.dir name) =>
        showDirName name
        let contents ← path.readDir
        withReader (·.inDirectory)
          (doList contents.toList fun d =>
            dirTree d.path)

book declaration {{{ NewMain }}}
  def main (args : List String) : IO UInt32 := do
      match configFromArgs args with
      | some config =>
        dirTree (← IO.currentDir) config
        pure 0
      | none =>
        IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
        IO.eprintln usage
        pure 1
stop book declaration
end T

end DirTree


namespace MyVersions

def ReaderT (ρ : Type) (m : Type → Type) (α : Type) : Type :=
  ρ → m α

def StateT (σ : Type) (m : Type → Type) (α : Type) : Type :=
  σ → m (α × σ)

end MyVersions

example : ReaderT = MyVersions.ReaderT := by rfl
example : StateT = MyVersions.StateT := by rfl
