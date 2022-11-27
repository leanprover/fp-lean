import Examples.Support

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

structure Config where
  useAscii : Bool := false
  currentPrefix := ""

def preFile := "├──"
def preDir := "│  "

namespace Old
def showFile (cfg : Config) (file : String) : IO Unit := do
  IO.println s!"{cfg.currentPrefix} {file}"

def showDirName (cfg : Config) (dir : String) : IO Unit := do
  IO.println s!"{cfg.currentPrefix} {dir}/"

def doList : (List α) → (α → IO Unit) → IO Unit
  | [], _ => pure ()
  | x :: xs, action => do
    action x
    doList xs action

partial def dirTree (cfg : Config) (path : System.FilePath) : IO Unit := do
  match path.fileName with
  | none => pure ()
  | some name =>
    if !(← path.isDir) then
      showFile cfg name
    else
      showDirName cfg name
      let contents ← path.readDir
      let newConfig := {cfg with currentPrefix := preDir ++ " " ++ cfg.currentPrefix}
      doList contents.toList (fun d =>
        dirTree newConfig d.path)
end Old

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

def showFile (file : String) : ConfigIO Config Unit := do
  let cfg ← config
  io (IO.println s!"{cfg.currentPrefix} {file}")

def showDirName (dir : String) : ConfigIO Config Unit := do
  let cfg ← config
  io (IO.println s!"{cfg.currentPrefix} {dir}/")

def doList : (List α) → (α → ConfigIO β Unit) → ConfigIO β Unit
  | [], _ => pure ()
  | x :: xs, action => do
    action x
    doList xs action

def inDir (cfg : Config) : Config :=
  {cfg with currentPrefix := preDir ++ " " ++ cfg.currentPrefix}

partial def dirTree' (path : System.FilePath) : ConfigIO Config Unit := do
  match path.fileName with
  | none => pure ()
  | some name =>
    if !(← io path.isDir) then
      showFile name
    else
      showDirName name
      let contents ← io path.readDir
      locally inDir (doList contents.toList (fun d => dirTree' d.path))

end DirTree
