import ExampleSupport

import Examples.DependentTypes

set_option linter.unusedVariables false

-- ANCHOR: plusL
def Nat.plusL : Nat → Nat → Nat
  | 0, k => k
  | n + 1, k => plusL n k + 1
-- ANCHOR_END: plusL


-- ANCHOR: plusR
def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1
-- ANCHOR_END: plusR


discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n k n✝ : Nat
x : α
xs : Vect α n✝
ys : Vect α k
⊢ Vect α ((n✝ + 1).plusL k)
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)
-/
#check_msgs in
-- ANCHOR: appendL1
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => _
  | .cons x xs, ys => _
-- ANCHOR_END: appendL1
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n k n✝ : Nat
x : α
xs : Vect α n✝
ys : Vect α k
⊢ Vect α ((n✝ + 1).plusL k)
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)
-/
#check_msgs in
-- ANCHOR: appendL2
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => _
  | .cons x xs, ys => _
-- ANCHOR_END: appendL2
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusL k)
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)
-/
#check_msgs in
-- ANCHOR: appendL3
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
-- ANCHOR_END: appendL3
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusL k)
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)
-/
#check_msgs in
-- ANCHOR: appendL4
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
-- ANCHOR_END: appendL4
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k + 1)
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k
-/
#check_msgs in
-- ANCHOR: appendL5
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
-- ANCHOR_END: appendL5
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k + 1)
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k
-/
#check_msgs in
-- ANCHOR: appendL6
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
-- ANCHOR_END: appendL6
stop discarding

discarding
/-- error:
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k + 1)
-/
#check_msgs in
-- ANCHOR: appendL7
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
-- ANCHOR_END: appendL7
stop discarding

discarding
/-- error:
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (n.plusL k)
-/
#check_msgs in
-- ANCHOR: appendL8
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => .cons x (_ : Vect α (n.plusL k))
-- ANCHOR_END: appendL8
stop discarding

namespace Almost

-- ANCHOR: appendL9
def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
  | 0, k, .nil, ys => ys
  | n + 1, k, .cons x xs, ys => .cons x (appendL n k xs ys)
-- ANCHOR_END: appendL9
end Almost



-- ANCHOR: appendL
def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (appendL xs ys)
-- ANCHOR_END: appendL

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusR k)
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusR 0 k)
-/
#check_msgs in
-- ANCHOR: appendR1
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
-- ANCHOR_END: appendR1
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusR k)
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusR 0 k)
-/
#check_msgs in
-- ANCHOR: appendR2
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => _
  | n + 1, k, .cons x xs, ys => _
-- ANCHOR_END: appendR2
stop discarding

discarding
/--
error: Type mismatch
  ?m.11
has type
  Vect α k
but is expected to have type
  Vect α (Nat.plusR 0 k)
-/
#check_msgs in
-- ANCHOR: appendR3
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
-- ANCHOR_END: appendR3
stop discarding

discarding
/--
error: Type mismatch
  ?m.15
has type
  Vect α k
but is expected to have type
  Vect α (0 + k)
-/
#check_msgs in
-- ANCHOR: appendR4
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n + k)
  | 0, k, .nil, ys => (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
-- ANCHOR_END: appendR4
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 (k + 1)
---
error: don't know how to synthesize placeholder
context:
⊢ 0 = Nat.plusR 0 0
-/
#check_msgs in
-- ANCHOR: plusR_zero_left1
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => _
  | k + 1 => _
-- ANCHOR_END: plusR_zero_left1
stop discarding

discarding
/--
error: don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 (k + 1)
---
error: don't know how to synthesize placeholder
context:
⊢ 0 = Nat.plusR 0 0
-/
#check_msgs in
-- ANCHOR: plusR_zero_left2
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => _
  | k + 1 => _
-- ANCHOR_END: plusR_zero_left2
stop discarding

discarding
/-- error:
don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 (k + 1)
-/
#check_msgs in
-- ANCHOR: plusR_zero_left3
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 => _
-- ANCHOR_END: plusR_zero_left3
stop discarding

namespace Adding
axiom k : Nat
-- ANCHOR: plusRStep
example : (
Nat.plusR 0 k + 1
) = (
Nat.plusR 0 (k + 1)
) := rfl
-- ANCHOR_END: plusRStep

end Adding

discarding
/-- error:
don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 k + 1
-/
#check_msgs in
-- ANCHOR: plusR_zero_left4
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 => (_ : k + 1 = Nat.plusR 0 k + 1)
-- ANCHOR_END: plusR_zero_left4
stop discarding

discarding
-- ANCHOR: plusR_zero_left_done
def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
-- ANCHOR_END: plusR_zero_left_done
stop discarding

-- ANCHOR: plusR_zero_left_thm
theorem plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
  | 0 => by rfl
  | k + 1 =>
    congrArg (· + 1) (plusR_zero_left k)
-- ANCHOR_END: plusR_zero_left_thm

discarding
/--
error: don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusR k)
---
error: don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k
-/
#check_msgs in
-- ANCHOR: appendRsubst
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ (_ : Vect α k)
  | n + 1, k, .cons x xs, ys => _
-- ANCHOR_END: appendRsubst
stop discarding

discarding
/-- error:
don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α ((n + 1).plusR k)
-/
#check_msgs in
-- ANCHOR: appendR5
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys => plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys => _
-- ANCHOR_END: appendR5
stop discarding

discarding
/-- error:
don't know how to synthesize placeholder
context:
n k : Nat
⊢ (n + 1).plusR (k + 1) = n.plusR (k + 1) + 1
-/
#check_msgs in
-- ANCHOR: plusR_succ_left_0
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => _
-- ANCHOR_END: plusR_succ_left_0
stop discarding

discarding
/-- error:
don't know how to synthesize placeholder
context:
n k : Nat
⊢ (n + 1).plusR (k + 1) = n.plusR (k + 1) + 1
-/
#check_msgs in
-- ANCHOR: plusR_succ_left_2
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => _
-- ANCHOR_END: plusR_succ_left_2
stop discarding

-- ANCHOR: plusR_succ_left
theorem plusR_succ_left (n : Nat) :
    (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
  | 0 => by rfl
  | k + 1 => congrArg (· + 1) (plusR_succ_left n k)
-- ANCHOR_END: plusR_succ_left


-- ANCHOR: appendR
def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
  | 0, k, .nil, ys =>
    plusR_zero_left k ▸ ys
  | n + 1, k, .cons x xs, ys =>
    plusR_succ_left n k ▸ .cons x (appendR n k xs ys)
-- ANCHOR_END: appendR

namespace Impl
-- ANCHOR: appendRImpl
def appendR : Vect α n → Vect α k → Vect α (n.plusR k)
  | .nil, ys => plusR_zero_left _ ▸ ys
  | .cons x xs, ys => plusR_succ_left _ _ ▸ .cons x (appendR xs ys)
-- ANCHOR_END: appendRImpl
end Impl

def plusRAdd (n : Nat) : (k : Nat) → n.plusR k = n + k
  | 0 => by rfl
  | k + 1 =>  congrArg (· + 1) (plusRAdd n k)


-- ANCHOR: moreNames
example : (
-- ANCHOR: moreFun
(n : Nat) → Vect String n
-- ANCHOR_END: moreFun
) = (
(k : Nat) → Vect String k
) := rfl
-- ANCHOR: againFun
example := (n : Nat) → Vect String (Nat.plusL 0 n)
-- ANCHOR_END: againFun
-- ANCHOR: stuckFun
example := (n : Nat) → Vect String (Nat.plusL n 0)
-- ANCHOR_END: stuckFun
example := List String
example : List Nat := [5, 3, 1]
example := (n k : Nat) → Vect Int n
example := (n k : Nat) → Vect Int k
example : (Vect String (1 + 4)) = (Vect String (3 + 2)) := rfl
example := 5
example := 17
example := 33
example := ["a", "b"] ++ ["c"]
example := List Nat
example := Int
example := List
example := @List.append
section
open List
example := @nil
example := @cons
end
section
open Nat
variable (k : Nat)
example := plusL 0 k
example := zero
example := succ
end
example {α} {k} := (Vect α (Nat.plusL 0 k)) = (Vect α k)
-- ANCHOR_END: moreNames

-- ANCHOR: plusRinfo
example {k} := (Nat.plusR 0 k, k)
example := Nat.add
section
open Nat
example := plusR
example := plusL
end
-- ANCHOR_END: plusRinfo

-- ANCHOR: congr
example := @congrArg
section
variable {x y : α} {f : α → β}
example : x = y → f x = f y := congrArg f
end
example {n k} := Nat.plusR (n + 1) k + 1 = Nat.plusR n (k + 1) + 1
-- ANCHOR_END: congr

-- ANCHOR: exercises
example {n k : Nat} := n.plusR k = n + k
-- ANCHOR_END: exercises

-- ANCHOR: Vect
section
open Vect
example := @cons
example := @nil
end
-- ANCHOR_END: Vect

namespace Eta
axiom α : Type
axiom β : Type
axiom f : α → β
example : f = fun x => f x := Eq.refl f
end Eta
