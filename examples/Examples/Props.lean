import Examples.Support

import Examples.Intro

book declaration {{{ woodlandCritters }}}
  def woodlandCritters : List String :=
    ["hedgehog", "deer", "snail"]
stop book declaration


book declaration {{{ animals }}}
  def hedgehog := woodlandCritters[0]
  def deer := woodlandCritters[1]
  def snail := woodlandCritters[2]
stop book declaration

expect error {{{ outOfBounds }}}
  def oops := woodlandCritters[3]
message
"failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is perfomed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
⊢ 3 < List.length woodlandCritters"
end expect

book declaration {{{ onePlusOneIsTwo }}}
  def onePlusOneIsTwo : 1 + 1 = 2 := rfl
stop book declaration

expect error {{{ onePlusOneIsFifteen }}}
  def onePlusOneIsFifteen : 1 + 1 = 15 := rfl
message
"type mismatch
  rfl
has type
  1 + 1 = 1 + 1 : Prop
but is expected to have type
  1 + 1 = 15 : Prop"
end expect


namespace Foo
book declaration {{{ onePlusOneIsTwoProp }}}
  def OnePlusOneIsTwo : Prop := 1 + 1 = 2

  theorem onePlusOneIsTwo : OnePlusOneIsTwo := rfl
stop book declaration
end Foo


namespace Foo2
book declaration {{{ onePlusOneIsTwoTactics }}}
  theorem onePlusOneIsTwo : 1 + 1 = 2 := by
    simp
stop book declaration
end Foo2

theorem oneLessThanFive : 1 < 5 := by simp

def second (xs : List α) (ok : xs.length ≥ 3) : α :=
  xs[ 2 ]

example : String := second ["a", "b", "c", "d"] (by simp)

book declaration {{{ connectives }}}
  theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by simp
  theorem notTwoEqualFive : ¬(1 + 1 = 5) := by simp
  theorem trueIsTrue : True := True.intro
  theorem trueOrFalse : True ∨ False := by simp
  theorem falseImpliesTrue : False → True := by simp
stop book declaration

def foo : True ∧ True := And.intro True.intro True.intro
def bar : True ∨ False := Or.inl True.intro

namespace Connectives
inductive A : Prop where | intro
inductive B : Prop where | intro

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

bookExample type {{{ AndProp }}}
  A ∧ B
  ===>
  Prop
end bookExample

bookExample type {{{ AndIntro }}}
  And.intro
  ===>
  A → B → A ∧ B
end bookExample

bookExample type {{{ AndIntroEx }}}
  And.intro rfl rfl
  ===>
  1 + 1 = 2 ∧ "Str".append "ing" = "String"
end bookExample


book declaration {{{ AndIntroExTac }}}
  theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by simp
stop book declaration

bookExample type {{{ OrProp }}}
  A ∨ B
  ===>
  Prop
end bookExample

bookExample type {{{ OrIntro1 }}}
  Or.inl
  ===>
  A → A ∨ B
end bookExample

bookExample type {{{ OrIntro2 }}}
  Or.inr
  ===>
  B → A ∨ B
end bookExample

bookExample type {{{ OrIntroEx }}}
  Or.inr rfl
  ===>
  1 + 1 = 90 ∨ "Str".append "ing" = "String"
end bookExample


book declaration {{{ OrIntroExTac }}}
  theorem addOrAppend : 1 + 1 = 90 ∨ "Str".append "ing" = "String" := by simp
stop book declaration


book declaration {{{ andImpliesOr }}}
  theorem andImpliesOr : A ∧ B → A ∨ B :=
    fun andEvidence =>
      match andEvidence with
      | And.intro a b => Or.inl a
stop book declaration

bookExample type {{{ FalseProp }}}
  False
  ===>
  Prop
end bookExample


end Connectives




expect error {{{ thirdErr }}}
  def third (xs : List α) : α := xs[2]
message
"failed to prove index is valid, possible solutions:
  - Use `have`-expressions to prove the index is valid
  - Use `a[i]!` notation instead, runtime check is perfomed, and 'Panic' error message is produced if index is not valid
  - Use `a[i]?` notation instead, result is an `Option` type
  - Use `a[i]'h` notation instead, where `h` is a proof that index is valid
α : Type ?u.3908
xs : List α
⊢ 2 < List.length xs"
end expect

book declaration {{{ third }}}
  def third (xs : List α) (ok : xs.length > 2) : α := xs[2]
stop book declaration

expect info {{{ thirdCritters }}}
  #eval third woodlandCritters (by simp)
message
  "\"snail\""
end expect

book declaration {{{ thirdOption }}}
  def thirdOption (xs : List α) : Option α := xs[2]?
stop book declaration


expect info {{{ thirdOptionCritters }}}
  #eval thirdOption woodlandCritters
message
  "some \"snail\""
end expect


expect info {{{ thirdOptionTwo }}}
  #eval thirdOption ["only", "two"]
message
  "none"
end expect


expect info {{{ crittersBang }}}
  #eval woodlandCritters[1]!
message
  "\"deer\""
end expect


expect error {{{ unsafeThird }}}
  def unsafeThird (xs : List α) : α := xs[2]!
message
"failed to synthesize instance
  Inhabited α"
end expect

expect error {{{ extraSpace }}}
  #eval woodlandCritters [1]
message
"function expected at
  woodlandCritters
term has type
  List String"
end expect

