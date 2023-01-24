import Examples.Support

import Examples.MonadTransformers.Defs
import Examples.Monads.Many

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

  def List.find? (p : α → Bool) (xs : List α) : Option α := do
    for x in xs do
      if p x then return x
    failure

  def List.count (p : α → Bool) (xs : List α) : Nat := Id.run do
    let mut found := 0
    for x in xs do
      if p x then found := found + 1
    return found

end Loops


similar datatypes ForM Loops.Fake.ForM
