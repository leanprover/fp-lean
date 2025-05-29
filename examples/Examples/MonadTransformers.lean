import ExampleSupport
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

-- ANCHOR: Summary
example := Monad
example := MonadLift
example := StateT
example := ExceptT
example := Unit
-- ANCHOR_END: Summary
