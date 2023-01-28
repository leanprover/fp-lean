import Examples.Support

import Examples.MonadTransformers.Defs
import Examples.Monads.Many
import Examples.FunctorApplicativeMonad

namespace StEx
namespace FancyDo

book declaration {{{ countLettersNoElse }}}
  def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
    let rec loop (chars : List Char) := do
      match chars with
      | [] => pure ⟨⟩
      | c :: cs =>
        if c.isAlpha then
          if vowels.contains c then
            modify fun st => {st with vowels := st.vowels + 1}
          else if consonants.contains c then
            modify fun st => {st with consonants := st.consonants + 1}
        else throw (.notALetter c)
        loop cs
    loop str.toList
stop book declaration

end FancyDo
end StEx

namespace ThenDoUnless


book declaration {{{ count }}}
def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ⟨⟩
  | x :: xs => do
    if ← p x then
      modify (· + 1)
    count p xs
stop book declaration


book declaration {{{ countNot }}}
def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ⟨⟩
  | x :: xs => do
    unless ← p x do
      modify (· + 1)
    countNot p xs
stop book declaration

end ThenDoUnless



namespace EarlyReturn

namespace Non

book declaration {{{ findHuhSimple }}}
  def List.find? (p : α → Bool) : List α → Option α
    | [] => none
    | x :: xs =>
      if p x then
        some x
      else
        find? p xs
stop book declaration
end Non


book declaration {{{ findHuhFancy }}}
  def List.find? (p : α → Bool) : List α → Option α
    | [] => failure
    | x :: xs => do
      if p x then return x
      find? p xs
stop book declaration


book declaration {{{ runCatch }}}
  def runCatch [Monad m] (action : ExceptT α m α) : m α := do
    match ← action with
    | Except.ok x => pure x
    | Except.error x => pure x
stop book declaration


namespace Desugared
book declaration {{{ desugaredFindHuh }}}
  def List.find? (p : α → Bool) : List α → Option α
    | [] => failure
    | x :: xs =>
      runCatch do
        if p x then throw x else pure ()
        monadLift (find? p xs)
stop book declaration
end Desugared

def List.lookup [BEq k] (key : k) : List (k × α) → Option α
  | [] => failure
  | x :: xs => do
    if x.fst == key then return x.snd
    lookup key xs



book declaration {{{ greet }}}
  def greet (name : String) : String :=
    "Hello, " ++ Id.run do return name
stop book declaration

bookExample {{{ greetDavid }}}
  greet "David"
  ===>
  "Hello, David"
end bookExample


end EarlyReturn





book declaration {{{ ManyForM }}}
  def Many.forM [Monad m] : Many α → (α → m PUnit) → m PUnit
    | Many.none, _ => pure ()
    | Many.more first rest, action => do
      action first
      forM (rest ⟨⟩) action

  instance : ForM m (Many α) α where
    forM := Many.forM
stop book declaration


namespace Loops

namespace Fake


book declaration {{{ ForM }}}
  class ForM (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where
    forM [Monad m] : γ → (α → m PUnit) → m PUnit
stop book declaration



book declaration {{{ ListForM }}}
  def List.forM [Monad m] : List α → (α → m PUnit) → m PUnit
    | [], _ => pure ()
    | x :: xs, action => do
      action x
      forM xs action

  instance : ForM m (List α) α where
    forM := List.forM
stop book declaration


end Fake


book declaration {{{ AllLessThan }}}
  structure AllLessThan where
    num : Nat
stop book declaration


book declaration {{{ AllLessThanForM }}}
  def AllLessThan.forM [Monad m] (coll : AllLessThan) (action : Nat → m Unit) : m Unit :=
    let rec countdown : Nat → m Unit
      | 0 => pure ()
      | n + 1 => do
        action n
        countdown n
    countdown coll.num

  instance : ForM m AllLessThan Nat where
    forM := AllLessThan.forM
stop book declaration


expect info {{{ AllLessThanForMRun }}}
  #eval forM { num := 5 : AllLessThan } IO.println
message
"4
3
2
1
0"
end expect


book declaration {{{ ForInIOAllLessThan }}}
  instance : ForIn m AllLessThan Nat where
    forIn := ForM.forIn
stop book declaration

namespace Transformed

book declaration {{{ OptionTExec }}}
  def OptionT.exec [Applicative m] (action : OptionT m α) : m Unit :=
    action *> pure ()
stop book declaration


book declaration {{{ OptionTcountToThree }}}
  def countToThree (n : Nat) : IO Unit :=
    let nums : AllLessThan := ⟨n⟩
    OptionT.exec (forM nums fun i => do
      if i < 3 then failure else IO.println i)
stop book declaration


expect info {{{ optionTCountSeven }}}
  #eval countToThree 7
message
"6
5
4
3"
end expect
end Transformed


book declaration {{{ countToThree }}}
  def countToThree (n : Nat) : IO Unit := do
    let nums : AllLessThan := ⟨n⟩
    for i in nums do
      if i < 3 then break
      IO.println i
stop book declaration


expect info {{{ countSevenFor }}}
  #eval countToThree 7
message
"6
5
4
3"
end expect



book declaration {{{ parallelLoop }}}
def parallelLoop := do
  for x in ["currant", "gooseberry", "rowan"], y in [4, 5, 6, 7] do
    IO.println (x, y)
stop book declaration


expect info {{{ parallelLoopOut }}}
  #eval parallelLoop
message
"(currant, 4)
(gooseberry, 5)
(rowan, 6)"
end expect

book declaration {{{ findHuh }}}
  def List.find? (p : α → Bool) (xs : List α) : Option α := do
    for x in xs do
      if p x then return x
    failure
stop book declaration

namespace Cont
book declaration {{{ findHuhCont }}}
  def List.find? (p : α → Bool) (xs : List α) : Option α := do
    for x in xs do
      if not (p x) then continue
      return x
    failure
stop book declaration
end Cont

example : List.find? p xs = Cont.List.find? p xs := by
  induction xs <;> simp [List.find?, Cont.List.find?, bind]


book declaration {{{ ListCount }}}
  def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
    let mut found := 0
    for x in xs do
      if p x then found := found + 1
    return found
stop book declaration

end Loops

namespace Mut


book declaration {{{ two }}}
  def two : Nat := Id.run do
    let mut x := 0
    x := x + 1
    x := x + 1
    return x
stop book declaration

example : two = 2 := by rfl

namespace St

book declaration {{{ twoStateT }}}
  def two : Nat :=
    let block : StateT Nat Id Nat := do
      modify (· + 1)
      modify (· + 1)
      return (← get)
    let (result, _finalState) := block 0
    result
stop book declaration

example : two = 2 := by rfl

end St

book declaration {{{ three }}}
  def three : Nat := Id.run do
    let mut x := 0
    for _ in [1, 2, 3] do
      x := x + 1
    return x
stop book declaration

example : three = 3 := by rfl

book declaration {{{ six }}}
  def six : Nat := Id.run do
    let mut x := 0
    for y in [1, 2, 3] do
      x := x + y
    return x
stop book declaration

example : six = 6 := by rfl


expect error {{{ nonLocalMut }}}
  def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
    let mut found := 0
    let rec go : List α → Id Unit
      | [] => pure ()
      | y :: ys => do
        if p y then found := found + 1
        go ys
    return found
message
"`found` cannot be mutated, only variables declared using `let mut` can be mutated. If you did not intent to mutate but define `found`, consider using `let found` instead"
end expect

end Mut


similar datatypes ForM Loops.Fake.ForM

namespace Ranges

deriving instance Repr for Std.Range

--NB in this section, using the typical bookExample macro fails
--because `stop` has become a reserved word due to another macro.
-- These tests are here in support of a table.

def rangeToList (r : Std.Range) : List Nat := Id.run do
  let mut out : List Nat := []
  for i in r do
    out := out ++ [i]
  pure out

expect info {{{ rangeStop }}}
  #eval [:10]
message
"{ start := 0, stop := 10, step := 1 }"
end expect

bookExample {{{ rangeStopContents }}}
  rangeToList [:10]
  ===>
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]
end bookExample


expect info {{{ rangeStartStop }}}
  #eval [2:10]
message
"{ start := 2, stop := 10, step := 1 }
"
end expect

bookExample {{{ rangeStartStopContents }}}
  rangeToList [2:10]
  ===>
  [2, 3, 4, 5, 6, 7, 8, 9]
end bookExample

expect info {{{ rangeStopStep }}}
  #eval [:10:3]
message
"{ start := 0, stop := 10, step := 3 }"
end expect

bookExample {{{ rangeStopStepContents }}}
  rangeToList [:10:3]
  ===>
  [0, 3, 6, 9]
end bookExample

expect info {{{ rangeStartStopStep }}}
  #eval [2:10:3]
message
"{ start := 2, stop := 10, step := 3 }
"
end expect

bookExample {{{ rangeStartStopStepContents }}}
  rangeToList [2:10:3]
  ===>
  [2, 5, 8]
end bookExample


book declaration {{{ fourToEight }}}
def fourToEight : IO Unit := do
  for i in [4:9:2] do
    IO.println i
stop book declaration

expect info {{{ fourToEightOut }}}
  #eval fourToEight
message
"4
6
8"
end expect

end Ranges

namespace SameDo


book declaration {{{ sameBlock }}}
  example : Id Unit := do
    let mut x := 0
    x := x + 1
stop book declaration


book declaration {{{ collapsedBlock }}}
  example : Id Unit := do
    let mut x := 0
    do x := x + 1
stop book declaration


expect error {{{ letBodyNotBlock }}}
  example : Id Unit := do
    let mut x := 0
    let other := do
      x := x + 1
    other
message
"`x` cannot be mutated, only variables declared using `let mut` can be mutated. If you did not intent to mutate but define `x`, consider using `let x` instead"
end expect



book declaration {{{ letBodyArrBlock }}}
  example : Id Unit := do
    let mut x := 0
    let other ← do
      x := x + 1
    pure other
stop book declaration


expect error {{{ funArgNotBlock }}}
  example : Id Unit := do
    let mut x := 0
    let addFour (y : Id Nat) := Id.run y + 4
    addFour do
      x := 5
message
"`x` cannot be mutated, only variables declared using `let mut` can be mutated. If you did not intent to mutate but define `x`, consider using `let x` instead"
end expect


book declaration {{{ ifDoSame }}}
  example : Id Unit := do
    let mut x := 0
    if x > 2 then
      x := x + 1
stop book declaration


book declaration {{{ ifDoDoSame }}}
  example : Id Unit := do
    let mut x := 0
    if x > 2 then do
      x := x + 1
stop book declaration


book declaration {{{ matchDoSame }}}
  example : Id Unit := do
    let mut x := 0
    match true with
    | true => x := x + 1
    | false => x := 17
stop book declaration

book declaration {{{ matchDoDoSame }}}
  example : Id Unit := do
    let mut x := 0
    match true with
    | true => do
      x := x + 1
    | false => do
      x := 17
stop book declaration



book declaration {{{ doForSame }}}
  example : Id Unit := do
    let mut x := 0
    for y in [1:5] do
     x := x + y
stop book declaration


book declaration {{{ doUnlessSame }}}
  example : Id Unit := do
    let mut x := 0
    unless 1 < 5 do
      x := x + 1
stop book declaration

end SameDo
