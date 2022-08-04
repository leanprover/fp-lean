-- Example solution to the "even numbers" exercise, adapted from Chris Lovett's solution

namespace Even
inductive Even : Type where
  | zero : Even
  | plusTwo : Even → Even

def Even.plus : Even → Even → Even
  | Even.zero, k => k
  | Even.plusTwo n, k => Even.plusTwo (n.plus k)

instance : Add Even where
  add := Even.plus

def eight : Even :=
  Even.plusTwo (Even.plusTwo (Even.plusTwo (Even.plusTwo Even.zero)))

def two : Even :=
  Even.plusTwo Even.zero

def Even.toNat : Even → Nat
  | Even.zero => 0
  | Even.plusTwo n => n.toNat + 2

instance : ToString Even where
  toString x := toString (x.toNat)

#eval eight + two   -- 10

#eval s!"There are {eight}"

def Even.mul : Even → Even → Even
  | Even.zero, k => Even.zero
  | Even.plusTwo Even.zero, k => k + k
  | Even.plusTwo n, k => n.mul k + k + k

instance : Mul Even where
  mul := Even.mul

#eval eight * two  -- 16

instance : OfNat Even Nat.zero where
  ofNat := Even.zero

instance [OfNat Even n] : OfNat Even (Nat.succ (Nat.succ n)) where
  ofNat := Even.plusTwo (OfNat.ofNat n)

#eval (8 : Even) * 2 -- 16
end Even
