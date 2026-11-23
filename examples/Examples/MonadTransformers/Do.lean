import ExampleSupport

import Examples.MonadTransformers.Defs
import Examples.Monads.Many
import Examples.FunctorApplicativeMonad

set_option linter.unusedVariables false

namespace StEx
namespace FancyDo

-- ANCHOR: names

example := IO.FS.Stream.getLine

example := (0 : Nat)

section

example := Std.Rio Nat

example := Std.Rco Nat

example := Std.Roo Nat

example := Std.Roi Nat

example := Std.Rci Nat

example := Std.Rii Nat

example := Std.Ric Nat

example := Std.Roc Nat

example := Std.Rcc Nat

end

-- ANCHOR_END: names


-- ANCHOR: countLettersNoElse
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
      else throw (.notALetter c)
      loop cs
  loop str.toList
-- ANCHOR_END: countLettersNoElse

end FancyDo
end StEx

namespace ThenDoUnless


-- ANCHOR: count
def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    if ← p x then
      modify (· + 1)
    count p xs
-- ANCHOR_END: count


-- ANCHOR: countNot
def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    unless ← p x do
      modify (· + 1)
    countNot p xs
-- ANCHOR_END: countNot

end ThenDoUnless



namespace EarlyReturn

namespace Non

-- ANCHOR: findHuhSimple
def List.find? (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    if p x then
      some x
    else
      find? p xs
-- ANCHOR_END: findHuhSimple
end Non


-- ANCHOR: findHuhFancy
def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs => do
    if p x then return x
    find? p xs
-- ANCHOR_END: findHuhFancy


-- ANCHOR: runCatch
def runCatch [Monad m] (action : ExceptT α m α) : m α := do
  match ← action with
  | Except.ok x => pure x
  | Except.error x => pure x
-- ANCHOR_END: runCatch


namespace Desugared
-- ANCHOR: desugaredFindHuh
def List.find? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs =>
    runCatch do
      if p x then throw x else pure ()
      monadLift (find? p xs)
-- ANCHOR_END: desugaredFindHuh
end Desugared

def List.lookup [BEq k] (key : k) : List (k × α) → Option α
  | [] => failure
  | x :: xs => do
    if x.fst == key then return x.snd
    lookup key xs



-- ANCHOR: greet
def greet (name : String) : String :=
  "Hello, " ++ Id.run do return name
-- ANCHOR_END: greet

-- ANCHOR: greetDavid
example : (
greet "David"
) = (
"Hello, David"
) := rfl
-- ANCHOR_END: greetDavid


end EarlyReturn





-- ANCHOR: ManyForM
def Many.forM [Monad m] : Many α → (α → m PUnit) → m PUnit
  | Many.none, _ => pure ()
  | Many.more first rest, action => do
    action first
    forM (rest ()) action

instance [Monad m] : ForM m (Many α) α where
  forM := Many.forM
-- ANCHOR_END: ManyForM


namespace Loops

namespace Fake


-- ANCHOR: ForM
class ForM (m : Type u → Type v) (γ : Type w₁)
    (α : outParam (Type w₂)) where
  forM (coll : γ) (f : α → m PUnit) : m PUnit
-- ANCHOR_END: ForM



-- ANCHOR: ListForM
def List.forM [Monad m] : List α → (α → m PUnit) → m PUnit
  | [], _ => pure ()
  | x :: xs, action => do
    action x
    forM xs action

instance [Monad m] : ForM m (List α) α where
  forM := List.forM
-- ANCHOR_END: ListForM

  open StEx (vowels consonants Err LetterCounts)


-- ANCHOR: countLettersForM
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  forM str.toList fun c => do
    if c.isAlpha then
      if vowels.contains c then
        modify fun st => {st with vowels := st.vowels + 1}
      else if consonants.contains c then
        modify fun st => {st with consonants := st.consonants + 1}
    else throw (.notALetter c)
-- ANCHOR_END: countLettersForM



end Fake


-- ANCHOR: AllLessThan
structure AllLessThan where
  num : Nat
-- ANCHOR_END: AllLessThan


-- ANCHOR: AllLessThanForM
def AllLessThan.forM [Monad m]
    (coll : AllLessThan) (action : Nat → m Unit) :
    m Unit :=
  let rec countdown : Nat → m Unit
    | 0 => pure ()
    | n + 1 => do
      action n
      countdown n
  countdown coll.num

instance [Monad m] : ForM m AllLessThan Nat where
  forM := AllLessThan.forM
-- ANCHOR_END: AllLessThanForM


/-- info:
4
3
2
1
0
-/
#check_msgs in
-- ANCHOR: AllLessThanForMRun
#eval forM { num := 5 : AllLessThan } IO.println
-- ANCHOR_END: AllLessThanForMRun


-- ANCHOR: ForInIOAllLessThan
instance [Monad m] : ForIn m AllLessThan Nat where
  forIn := ForM.forIn
-- ANCHOR_END: ForInIOAllLessThan

namespace Transformed

-- ANCHOR: OptionTExec
def OptionT.exec [Applicative m] (action : OptionT m α) : m Unit :=
  action *> pure ()
-- ANCHOR_END: OptionTExec


-- ANCHOR: OptionTcountToThree
def countToThree (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n⟩
  OptionT.exec (forM nums fun i => do
    if i < 3 then failure else IO.println i)
-- ANCHOR_END: OptionTcountToThree


/-- info:
6
5
4
3
-/
#check_msgs in
-- ANCHOR: optionTCountSeven
#eval countToThree 7
-- ANCHOR_END: optionTCountSeven
end Transformed


-- ANCHOR: countToThree
def countToThree (n : Nat) : IO Unit := do
  let nums : AllLessThan := ⟨n⟩
  for i in nums do
    if i < 3 then break
    IO.println i
-- ANCHOR_END: countToThree


/-- info:
6
5
4
3
-/
#check_msgs in
-- ANCHOR: countSevenFor
#eval countToThree 7
-- ANCHOR_END: countSevenFor



-- ANCHOR: parallelLoop
def parallelLoop := do
  for x in ["currant", "gooseberry", "rowan"], y in 'a'...'e' do
    IO.println (x, y)
-- ANCHOR_END: parallelLoop


/--
info: (currant, a)
(gooseberry, b)
(rowan, c)
-/
#check_msgs in
-- ANCHOR: parallelLoopOut
#eval parallelLoop
-- ANCHOR_END: parallelLoopOut

-- ANCHOR: findHuh
def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if p x then return x
  failure
-- ANCHOR_END: findHuh

namespace Cont
-- ANCHOR: findHuhCont
def List.find? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if not (p x) then continue
    return x
  failure
-- ANCHOR_END: findHuhCont
end Cont

example : List.find? p xs = Cont.List.find? p xs := by
  induction xs <;> simp [List.find?, Cont.List.find?, bind]


-- ANCHOR: ListCount
def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  for x in xs do
    if p x then found := found + 1
  return found
-- ANCHOR_END: ListCount

end Loops

namespace Mut


-- ANCHOR: two
def two : Nat := Id.run do
  let mut x := 0
  x := x + 1
  x := x + 1
  return x
-- ANCHOR_END: two

--ANCHOR: two_spec
example : two = 2 := by rfl
--ANCHOR_END: two_spec

namespace St

-- ANCHOR: twoStateT
def two : Nat :=
  let block : StateT Nat Id Nat := do
    modify (· + 1)
    modify (· + 1)
    return (← get)
  let (result, _finalState) := block 0
  result
-- ANCHOR_END: twoStateT

example : two = 2 := by rfl

end St

-- ANCHOR: three
def three : Nat := Id.run do
  let mut x := 0
  for _ in [1, 2, 3] do
    x := x + 1
  return x
-- ANCHOR_END: three

example : three = 3 := by rfl

-- ANCHOR: six
def six : Nat := Id.run do
  let mut x := 0
  for y in [1, 2, 3] do
    x := x + y
  return x
-- ANCHOR_END: six

example : six = 6 := by rfl


/--
error:
Variable `found` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `found`, consider using `let found` instead
-/
#check_msgs in
-- ANCHOR: nonLocalMut
def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  let rec go : List α → Id Unit
    | [] => pure ()
    | y :: ys => do
      if p y then found := found + 1
      go ys
  return found
-- ANCHOR_END: nonLocalMut

end Mut


similar datatypes ForM Loops.Fake.ForM

namespace Ranges

--NB in this section, using the typical bookExample macro fails
--because `stop` has become a reserved word due to another macro.
-- These tests are here in support of a table.

--- ANCHOR: ranges
#check *...10

#check *...5

#guard (*...5).toList == [0, 1, 2, 3, 4]

#check 3...*

#check (3...10 : Std.Rco Nat)

#check (3...=10 : Std.Rcc Nat)

#check 3...10

#check (3<...10 : Std.Roo Nat)

#check (3<...=10 : Std.Roc Nat)

#check 3...=10

#check 3<...10

#check 3...*

#check 10...3

#guard (10...3).size == 0

#check (3<...10)

#check 2
---ANCHOR_END: ranges

-- ANCHOR: fourToEight
def fourToEight : IO Unit := do
  for i in 2...5 do
    IO.println (i * 2)
-- ANCHOR_END: fourToEight

/-- info:
4
6
8
-/
#check_msgs in
-- ANCHOR: fourToEightOut
#eval fourToEight
-- ANCHOR_END: fourToEightOut

/--
info: l
m
n
o
p
-/
#check_msgs in
-- ANCHOR: showLetters
#eval do
  for letter in 'l'...='p' do
    IO.println letter
-- ANCHOR_END: showLetters

end Ranges

discarding
-- ANCHOR: printArray
def printArray [ToString α] (xs : Array α) : IO Unit := do
  for h : i in 0...xs.size do
    IO.println s!"{i}:\t{xs[i]}"
-- ANCHOR_END: printArray
stop discarding

-- ANCHOR: printArrayEv
def printArray [ToString α] (xs : Array α) : IO Unit := do
  for h : i in 0...xs.size do
    let h' := (h : i ∈ 0...xs.size)
    have : i < xs.size := by get_elem_tactic
    IO.println s!"{i}:\t{xs[i]}"
-- ANCHOR_END: printArrayEv

namespace SameDo

set_option linter.unusedVariables false

-- ANCHOR: sameBlock
example : Id Unit := do
  let mut x := 0
  x := x + 1
-- ANCHOR_END: sameBlock


-- ANCHOR: collapsedBlock
example : Id Unit := do
  let mut x := 0
  do x := x + 1
-- ANCHOR_END: collapsedBlock


/--
error: Variable `x` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `x`, consider using `let x` instead
-/
#check_msgs in
-- ANCHOR: letBodyNotBlock
example : Id Unit := do
  let mut x := 0
  let other := do
    x := x + 1
  other
-- ANCHOR_END: letBodyNotBlock



-- ANCHOR: letBodyArrBlock
example : Id Unit := do
  let mut x := 0
  let other ← do
    x := x + 1
  pure other
-- ANCHOR_END: letBodyArrBlock


/--
error: Variable `x` cannot be mutated. Only variables declared using `let mut` can be mutated.
      If you did not intend to mutate but define `x`, consider using `let x` instead
-/
#check_msgs in
-- ANCHOR: funArgNotBlock
example : Id Unit := do
  let mut x := 0
  let addFour (y : Id Nat) := Id.run y + 4
  addFour do
    x := 5
-- ANCHOR_END: funArgNotBlock


-- ANCHOR: ifDoSame
example : Id Unit := do
  let mut x := 0
  if x > 2 then
    x := x + 1
-- ANCHOR_END: ifDoSame


-- ANCHOR: ifDoDoSame
example : Id Unit := do
  let mut x := 0
  if x > 2 then do
    x := x + 1
-- ANCHOR_END: ifDoDoSame


-- ANCHOR: matchDoSame
example : Id Unit := do
  let mut x := 0
  match true with
  | true => x := x + 1
  | false => x := 17
-- ANCHOR_END: matchDoSame

-- ANCHOR: matchDoDoSame
example : Id Unit := do
  let mut x := 0
  match true with
  | true => do
    x := x + 1
  | false => do
    x := 17
-- ANCHOR_END: matchDoDoSame



-- ANCHOR: doForSame
example : Id Unit := do
  let mut x := 0
  for y in 1...5 do
   x := x + y
-- ANCHOR_END: doForSame


-- ANCHOR: doUnlessSame
example : Id Unit := do
  let mut x := 0
  unless 1 < 5 do
    x := x + 1
-- ANCHOR_END: doUnlessSame

end SameDo
