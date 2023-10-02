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

instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := Even.plusTwo (OfNat.ofNat n)

#eval (2 : Even)

#eval (8 : Even) * 2 -- 16
end Even

namespace Old

inductive GEven : Nat → Type where
  | zero : (m : Nat) → GEven m
  | succ2 : {m : Nat} → GEven m → GEven m

example : GEven 1 := .zero 1

end Old

namespace New

inductive GEven (basis : Nat) : Nat → Type where
  | base : basis % 2 = 0 → GEven basis basis
  | plusTwo : GEven basis n → GEven basis (n + 2)



theorem geven_is_even (n : Nat) (even : GEven basis n) : n % 2 = 0 := by
  induction even
  case base => simp [*]
  case plusTwo _ ih =>
    have step (n : Nat) : (n + 2) % 2 = n % 2 := by
      have : (n + 2) % 2 = if 0 < 2 ∧ 2 ≤ n + 2 then (n + 2 - 2) % 2 else n + 2 := Nat.mod_eq (n + 2) 2
      have : 2 ≤ n + 2 := by simp_arith
      simp [*, Nat.add_sub_self_right n 2]
    simp [*]

theorem geven_is_ge (n : Nat) (even : GEven basis n) : n ≥ basis := by
  simp_arith
  induction even
  case base => simp
  case plusTwo _ ih =>
    constructor; constructor; assumption

end New

namespace Other

inductive Even : Type where
  | times2 : Nat → Even
deriving Repr

def Even.add : Even → Even → Even
  | times2 a, times2 b => times2 (a + b)

instance : Add Even where
  add := Even.add

instance : OfNat Even .zero where
  ofNat := Even.times2 0

instance [OfNat Even n] : OfNat Even (n + 2) where
  ofNat := OfNat.ofNat n + .times2 1

#eval (0 : Even)

#eval (22 : Even)

end Other
