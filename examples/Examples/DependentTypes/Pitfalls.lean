import Examples.Support

import Examples.DependentTypes


book declaration {{{ plusL }}}
  def Nat.plusL : Nat → Nat → Nat
    | 0, k => k
    | n + 1, k => plusL n k + 1
stop book declaration


book declaration {{{ plusR }}}
  def Nat.plusR : Nat → Nat → Nat
    | n, 0 => n
    | n, k + 1 => plusR n k + 1
stop book declaration



expect error {{{ appendL1 }}}
  def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
    | .nil, ys => _
    | .cons x xs, ys => _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)"
end expect


expect error {{{ appendL2 }}}
  def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
    | .nil, ys => _
    | .cons x xs, ys => _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n k n✝ : Nat
x : α
xs : Vect α n✝
ys : Vect α k
⊢ Vect α (Nat.plusL (n✝ + 1) k)"
end expect

expect error {{{ appendL3 }}}
  def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
    | 0, k, .nil, ys => _
    | n + 1, k, .cons x xs, ys => _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusL 0 k)"
end expect


expect error {{{ appendL4 }}}
  def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
    | 0, k, .nil, ys => _
    | n + 1, k, .cons x xs, ys => _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (Nat.plusL (n + 1) k)"
end expect


expect error {{{ appendL5 }}}
  def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
    | 0, k, .nil, ys => (_ : Vect α k)
    | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
message
"don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k"
end expect


expect error {{{ appendL6 }}}
  def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
    | 0, k, .nil, ys => (_ : Vect α k)
    | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (Nat.plusL n k + 1)"
end expect


expect error {{{ appendL7 }}}
  def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
    | 0, k, .nil, ys => ys
    | n + 1, k, .cons x xs, ys => (_ : Vect α (n.plusL k + 1))
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (Nat.plusL n k + 1)"
end expect

expect error {{{ appendL8 }}}
  def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
    | 0, k, .nil, ys => ys
    | n + 1, k, .cons x xs, ys => .cons x (_ : Vect α (n.plusL k))
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (Nat.plusL n k)"
end expect

namespace Almost

book declaration {{{ appendL9 }}}
  def appendL : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusL k)
    | 0, k, .nil, ys => ys
    | n + 1, k, .cons x xs, ys => .cons x (appendL n k xs ys)
stop book declaration
end Almost



book declaration {{{ appendL }}}
  def appendL : Vect α n → Vect α k → Vect α (n.plusL k)
    | .nil, ys => ys
    | .cons x xs, ys => .cons x (appendL xs ys)
stop book declaration


expect error {{{ appendR1 }}}
  def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
    | 0, k, .nil, ys => _
    | n + 1, k, .cons x xs, ys => _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α (Nat.plusR 0 k)"
end expect

expect error {{{ appendR2 }}}
  def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
    | 0, k, .nil, ys => _
    | n + 1, k, .cons x xs, ys => _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (Nat.plusR (n + 1) k)"
end expect


expect error {{{ appendR3 }}}
  def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
    | 0, k, .nil, ys => (_ : Vect α k)
    | n + 1, k, .cons x xs, ys => _
message
"type mismatch
  ?m.3036
has type
  Vect α k : Type ?u.2973
but is expected to have type
  Vect α (Nat.plusR 0 k) : Type ?u.2973"
end expect

expect error {{{ appendR4 }}}
  def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n + k)
    | 0, k, .nil, ys => (_ : Vect α k)
    | n + 1, k, .cons x xs, ys => _
message
"type mismatch
  ?m.3068
has type
  Vect α k : Type ?u.2973
but is expected to have type
  Vect α (0 + k) : Type ?u.2973"
end expect

expect error {{{ plusR_zero_left1 }}}
  def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
    | 0 => _
    | k + 1 => _
message
"don't know how to synthesize placeholder
context:
⊢ 0 = Nat.plusR 0 0"
end expect


expect error {{{ plusR_zero_left2 }}}
  def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
    | 0 => _
    | k + 1 => _
message
"don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 (k + 1)"
end expect

expect error {{{ plusR_zero_left3 }}}
  def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
    | 0 => by rfl
    | k + 1 => _
message
"don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 (k + 1)"
end expect

namespace Adding
axiom k : Nat
bookExample {{{ plusRStep }}}
  Nat.plusR 0 k + 1
  ===>
  Nat.plusR 0 (k + 1)
end bookExample

end Adding


expect error {{{ plusR_zero_left4 }}}
  def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
    | 0 => by rfl
    | k + 1 => (_ : k + 1 = Nat.plusR 0 k + 1)
message
"don't know how to synthesize placeholder
context:
k : Nat
⊢ k + 1 = Nat.plusR 0 k + 1"
end expect


book declaration {{{ plusR_zero_left_done }}}
  def plusR_zero_left : (k : Nat) → k = Nat.plusR 0 k
    | 0 => by rfl
    | k + 1 =>
      congrArg (· + 1) (plusR_zero_left k)
stop book declaration


expect error {{{ appendRsubst }}}
  def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
    | 0, k, .nil, ys => plusR_zero_left k ▸ (_ : Vect α k)
    | n + 1, k, .cons x xs, ys => _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
k : Nat
ys : Vect α k
⊢ Vect α k"
end expect

expect error {{{ appendR5 }}}
  def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
    | 0, k, .nil, ys => plusR_zero_left k ▸ ys
    | n + 1, k, .cons x xs, ys => _
message
"don't know how to synthesize placeholder
context:
α : Type u_1
n k : Nat
x : α
xs : Vect α n
ys : Vect α k
⊢ Vect α (Nat.plusR (n + 1) k)"
end expect


expect error {{{ plusR_succ_left_0 }}}
  def plusR_succ_left (n : Nat) : (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
    | 0 => by rfl
    | k + 1 => _
message
"don't know how to synthesize placeholder
context:
n k : Nat
⊢ Nat.plusR (n + 1) (k + 1) = Nat.plusR n (k + 1) + 1"
end expect



expect error {{{ plusR_succ_left_2 }}}
  def plusR_succ_left (n : Nat) : (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
    | 0 => by rfl
    | k + 1 => _
message
"don't know how to synthesize placeholder
context:
n k : Nat
⊢ Nat.plusR (n + 1) (k + 1) = Nat.plusR n (k + 1) + 1"
end expect


book declaration {{{ plusR_succ_left }}}
  def plusR_succ_left (n : Nat) : (k : Nat) → Nat.plusR (n + 1) k = Nat.plusR n k + 1
    | 0 => by rfl
    | k + 1 => congrArg (· + 1) (plusR_succ_left n k)
stop book declaration


book declaration {{{ appendR }}}
  def appendR : (n k : Nat) → Vect α n → Vect α k → Vect α (n.plusR k)
    | 0, k, .nil, ys => plusR_zero_left k ▸ ys
    | n + 1, k, .cons x xs, ys => plusR_succ_left n k ▸ .cons x (appendR n k xs ys)
stop book declaration

namespace Impl
book declaration {{{ appendRImpl }}}
  def appendR : Vect α n → Vect α k → Vect α (n.plusR k)
    | .nil, ys => plusR_zero_left _ ▸ ys
    | .cons x xs, ys => plusR_succ_left _ _ ▸ .cons x (appendR xs ys)
stop book declaration
end Impl

def plusRAdd (n : Nat) : (k : Nat) → n.plusR k = n + k
  | 0 => by rfl
  | k + 1 =>  congrArg (· + 1) (plusRAdd n k)


namespace Eta
axiom α : Type
axiom β : Type
axiom f : α → β
example : f = fun x => f x := Eq.refl f
end Eta
