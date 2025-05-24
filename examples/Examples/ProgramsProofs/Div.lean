import ExampleSupport

discarding
/--
error: fail to show termination for
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
1) 30:8-21 ≤ =
Please use `termination_by` to specify a decreasing measure.
-/
#check_msgs in
-- ANCHOR: divTermination
def div (n k : Nat) : Nat :=
  if n < k then
    0
  else
    1 + div (n - k) k
-- ANCHOR_END: divTermination
stop discarding

discarding
-- ANCHOR: divRecursiveNeedsProof
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
-- ANCHOR_END: divRecursiveNeedsProof
stop discarding

-- ANCHOR: divRecursiveWithProof
def div (n k : Nat) (ok : k ≠ 0) : Nat :=
  if h : n < k then
    0
  else
    1 + div (n - k) k ok
termination_by n
-- ANCHOR_END: divRecursiveWithProof


-- ANCHOR: NatSubLt
example : ∀ {n k : Nat}, 0 < n → 0 < k → n - k < n := @Nat.sub_lt
-- ANCHOR_END: NatSubLt


#eval div 13 2 (by simp)
