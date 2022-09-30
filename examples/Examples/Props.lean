import Examples.Support


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

def third (xs : List α) (ok : xs.length ≥ 3) : α :=
  xs[2]
