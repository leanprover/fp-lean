import Examples.Support


expect error {{{ divTermination }}}
  def div (n k : Nat) (ok : k > 0) : Nat :=
    if n < k then
      0
    else
      1 + div (n - k) k ok
message
"fail to show termination for
  div
with errors
argument #1 was not used for structural recursion
  failed to eliminate recursive application
    div (n - k) k ok

argument #2 was not used for structural recursion
  failed to eliminate recursive application
    div (n - k) k ok

argument #3 was not used for structural recursion
  application type mismatch
    @Nat.le.brecOn (Nat.succ 0) fun k ok => Nat → Nat
  argument
    fun k ok => Nat → Nat
  has type
    (k : Nat) → k > 0 → Type : Type 1
  but is expected to have type
    (a : Nat) → Nat.le (Nat.succ 0) a → Prop : Type

structural recursion cannot be used

failed to prove termination, use `termination_by` to specify a well-founded relation"
end expect


expect error {{{ divRecursiveNeedsProof }}}
  def div (n k : Nat) (ok : k > 0) : Nat :=
    if h : n < k then
      0
    else
      1 + div (n - k) k ok
  termination_by div n k ok => n
message
"failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
n k : Nat
ok : k > 0
h : ¬n < k
⊢ n - k < n"
end expect

bookExample type {{{ NatSubLt }}}
  @Nat.sub_lt
  ===>
  ∀ {n k : Nat}, 0 < n → 0 < k → n - k < n
end bookExample



book declaration {{{ div }}}
  def div (n k : Nat) (ok : k > 0) : Nat :=
    if h : n < k then
      0
    else
      have : 0 < n := by
        cases n with
        | zero => contradiction
        | succ n' => simp_arith
      have : n - k < n := by
        apply Nat.sub_lt <;> assumption
      1 + div (n - k) k ok
  termination_by div n k ok => n
stop book declaration

#eval div 13 2 (by simp)
