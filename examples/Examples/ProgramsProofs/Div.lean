import Examples.Support


expect error {{{ divTermination }}}
  def div (n k : Nat) : Nat :=
    if n < k then
      0
    else
      1 + div (n - k) k
message
"fail to show termination for
  div
with errors
failed to infer structural recursion:
Cannot use parameter n:
  failed to eliminate recursive application
    div (n - k) k
Cannot use parameter k:
  failed to eliminate recursive application
    div (n - k) k


Could not find a decreasing measure.
The basic measures relate at each recursive call as follows:
(<, ≤, =: relation proved, ? all proofs failed, _: no proof attempted)
           n k
1) 9:10-23 ≤ =
Please use `termination_by` to specify a decreasing measure."
end expect

discarding
book declaration {{{ divRecursiveNeedsProof }}}
  def div (n k : Nat) (ok : k ≠ 0) : Nat :=
    if h : n < k then
      0
    else
      1 + div (n - k) k ok
stop book declaration
stop discarding

book declaration {{{ divRecursiveWithProof }}}
  def div (n k : Nat) (ok : k ≠ 0) : Nat :=
    if h : n < k then
      0
    else
      1 + div (n - k) k ok
  termination_by n
stop book declaration


bookExample type {{{ NatSubLt }}}
  @Nat.sub_lt
  ===>
  ∀ {n k : Nat}, 0 < n → 0 < k → n - k < n
end bookExample


#eval div 13 2 (by simp)
