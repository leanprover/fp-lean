import ExampleSupport

import Examples.Intro

-- ANCHOR: woodlandCritters
def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]
-- ANCHOR_END: woodlandCritters


-- ANCHOR: animals
def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]
-- ANCHOR_END: animals

/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ 3 < woodlandCritters.length
-/
#check_msgs in
--- ANCHOR: outOfBounds
def oops := woodlandCritters[3]
--- ANCHOR_END: outOfBounds

-- ANCHOR: onePlusOneIsTwo
def onePlusOneIsTwo : 1 + 1 = 2 := rfl
-- ANCHOR_END: onePlusOneIsTwo

/--
error: Type mismatch
  rfl
has type
  ?m.16 = ?m.16
but is expected to have type
  1 + 1 = 15
---
error: Not a definitional equality: the left-hand side
  1 + 1
is not definitionally equal to the right-hand side
  15
-/
#check_msgs in
-- ANCHOR: onePlusOneIsFifteen
def onePlusOneIsFifteen : 1 + 1 = 15 := rfl
-- ANCHOR_END: onePlusOneIsFifteen



namespace Foo
-- ANCHOR: onePlusOneIsTwoProp
def OnePlusOneIsTwo : Prop := 1 + 1 = 2

theorem onePlusOneIsTwo : OnePlusOneIsTwo := rfl
-- ANCHOR_END: onePlusOneIsTwoProp

discarding
/-- error: `simp` made no progress -/
#check_msgs in
-- ANCHOR: onePlusOneIsStillTwo
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by simp
-- ANCHOR_END: onePlusOneIsStillTwo
stop discarding

/--
error: failed to synthesize
  Decidable OnePlusOneIsTwo

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: onePlusOneIsStillTwo2
theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by decide
-- ANCHOR_END: onePlusOneIsStillTwo2

end Foo

-- ANCHOR: implication
example {A B : Prop} := A → B
-- ANCHOR_END: implication

namespace Foo2
-- ANCHOR: onePlusOneIsTwoTactics
theorem onePlusOneIsTwo : 1 + 1 = 2 := by
  decide
-- ANCHOR_END: onePlusOneIsTwoTactics
end Foo2

theorem oneLessThanFive : 1 < 5 := by simp

def second (xs : List α) (ok : xs.length ≥ 3) : α :=
  xs[ 2 ]

example : String := second ["a", "b", "c", "d"] (by simp)

-- ANCHOR: connectiveTable
section
variable {A B : Prop}
example : True := (True.intro : True)
example : Prop := False
example := A ∧ B
example : A → B → A ∧ B := (And.intro : A → B → A ∧ B)
example := (Or.inl : A → A ∨ B)
example := (Or.inr : B → A ∨ B)
example := ¬A
end
-- ANCHOR_END: connectiveTable

-- ANCHOR: connectives
theorem onePlusOneOrLessThan : 1 + 1 = 2 ∨ 3 < 5 := by simp
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by simp
theorem trueIsTrue : True := by simp
theorem trueOrFalse : True ∨ False := by simp
theorem falseImpliesTrue : False → True := by simp
-- ANCHOR_END: connectives

namespace Decide
-- ANCHOR: connectivesD
theorem onePlusOneOrLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by decide
theorem trueIsTrue : True := by decide
theorem trueOrFalse : True ∨ False := by decide
theorem falseImpliesTrue : False → True := by decide
-- ANCHOR_END: connectivesD
end Decide

def fooo : True ∧ True := And.intro True.intro True.intro
def bar : True ∨ False := Or.inl True.intro

namespace Connectives
variable {A B : Prop}

-- ANCHOR: SomeNats
example : List Nat := [0, 1, 2, 3, 4, 5]
-- ANCHOR_END: SomeNats

bookExample type {{{ TrueProp }}}
  True
  ===>
  Prop
end bookExample

bookExample type {{{ TrueIntro }}}
  True.intro
  ===>
  True
end bookExample

-- ANCHOR: AndProp
example : Prop :=  A ∧ B
-- ANCHOR_END: AndProp

-- ANCHOR: AndIntro
example : A → B → A ∧ B :=  And.intro
-- ANCHOR_END: AndIntro


-- ANCHOR: AndIntroEx
example : 1 + 1 = 2 ∧ "Str".append "ing" = "String" :=  And.intro rfl rfl
-- ANCHOR_END: AndIntroEx


-- ANCHOR: AndIntroExTac
theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  decide
-- ANCHOR_END: AndIntroExTac

-- ANCHOR: OrProp
example : Prop :=  A ∨ B
-- ANCHOR_END: OrProp

-- ANCHOR: OrIntro1
example :  A → A ∨ B :=  Or.inl
-- ANCHOR_END: OrIntro1

-- ANCHOR: OrIntro2
example : B → A ∨ B :=  Or.inr
-- ANCHOR_END: OrIntro2


-- ANCHOR: impliesDef
example : (A → B) = (¬ A ∨ B) := by
  simp only [eq_iff_iff]
  constructor
  . intro h
    by_cases A
    . apply Or.inr; simp_all
    . apply Or.inl; simp_all
  . intro h a
    cases h <;> simp_all
-- ANCHOR_END: impliesDef

bookExample type {{{ OrIntroEx }}}
  Or.inr rfl
  ===>
  1 + 1 = 90 ∨ "Str".append "ing" = "String"
end bookExample


-- ANCHOR: OrIntroExTac
  theorem addOrAppend : 1 + 1 = 90 ∨ "Str".append "ing" = "String" := by decide
-- ANCHOR_END: OrIntroExTac

set_option linter.unusedVariables false in
-- ANCHOR: andImpliesOr
theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a b => Or.inl a
-- ANCHOR_END: andImpliesOr


bookExample type {{{ FalseProp }}}
  False
  ===>
  Prop
end bookExample


end Connectives


discarding
/--
error: failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is performed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.5228
xs : List α
⊢ 2 < xs.length
-/
#check_msgs in
-- ANCHOR: thirdErr
def third (xs : List α) : α := xs[2]
-- ANCHOR_END: thirdErr

stop discarding

-- ANCHOR: third
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
-- ANCHOR_END: third

example := 3 < woodlandCritters.length

example := 3 < List.length woodlandCritters

example := Nat → List String

example := Type

example := List (Nat × String × (Int → Float))

example := Prop

/-- info: "snail" -/
#check_msgs in
-- ANCHOR: thirdCritters
#eval third woodlandCritters (by decide)
-- ANCHOR_END: thirdCritters

/--
error: Tactic `decide` proved that the proposition
  ["rabbit"].length > 2
is false
-/
#check_msgs in
-- ANCHOR: thirdRabbitErr
#eval third ["rabbit"] (by decide)
-- ANCHOR_END: thirdRabbitErr

-- ANCHOR: thirdOption
def thirdOption (xs : List α) : Option α := xs[2]?
-- ANCHOR_END: thirdOption

---ANCHOR: OptionNames
section
variable (α : Type) (x : α)
example : Option α := none
example : Option α := some x
end
---ANCHOR_END: OptionNames

/-- info: some "snail" -/
#check_msgs in
-- ANCHOR: thirdOptionCritters
#eval thirdOption woodlandCritters
-- ANCHOR_END: thirdOptionCritters

/-- info: none -/
#check_msgs in
-- ANCHOR: thirdOptionTwo
#eval thirdOption ["only", "two"]
-- ANCHOR_END: thirdOptionTwo

/-- info: "deer" -/
#check_msgs in
-- ANCHOR: crittersBang
#eval woodlandCritters[1]!
-- ANCHOR_END: crittersBang


/--
error: failed to synthesize
  Inhabited α

Hint: Additional diagnostic information may be available using the `set_option diagnostics true` command.
-/
#check_msgs in
-- ANCHOR: unsafeThird
def unsafeThird (xs : List α) : α := xs[2]!
-- ANCHOR_END: unsafeThird

/--
error: Function expected at
  woodlandCritters
but this term has type
  List String

Note: Expected a function because this term is being applied to the argument
  [1]
-/
#check_msgs in
-- ANCHOR: extraSpace
#eval woodlandCritters [1]
-- ANCHOR_END: extraSpace


--ANCHOR: exercises
example : 2 + 3 = 5 := rfl
example : 15 - 8 = 7 := rfl
example : "Hello, ".append "world" = "Hello, world" := rfl
example : "Hello, ".append "world" = "Hello, world" := by decide
example : Prop := 5 < 18
--ANCHOR_END: exercises
