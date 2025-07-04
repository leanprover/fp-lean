import ExampleSupport

discarding
/--
error: fail to show termination for
  div
with errors
failed to infer structural recursion:
Not considering parameter k of div:
  it is unchanged in the recursive calls
Cannot use parameter k:
  failed to eliminate recursive application
    div (n - k) k


failed to prove termination, possible solutions:
  - Use `have`-expressions to prove the remaining goals
  - Use `termination_by` to specify a different well-founded relation
  - Use `decreasing_by` to specify your own tactic for discharging this kind of goal
k n : Nat
h✝ : ¬n < k
⊢ n - k < n
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
