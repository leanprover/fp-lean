import ExampleSupport
import Examples.Monads
import Examples.Monads.Class

set_option linter.unusedVariables false

-- ANCHOR: names
example := @HAdd.hAdd
example := IO
example := Unit
section
open List
example := @map
end
-- ANCHOR_END: names

section
variable {m : Type → Type} [Monad m] {E : m α} {E₁ : m β} {E₂ : m γ}
variable {Es : m Unit} {Stmt Stmt₁ : m Unit} {Eₙ : m ζ}



local syntax "…" : term
macro_rules
  | `(…) => `(Es)

example :
(
-- ANCHOR: doSugar1a
do E
-- ANCHOR_END: doSugar1a
)
=
-- ANCHOR: doSugar1b
E
-- ANCHOR_END: doSugar1b
:= rfl



example :
(
-- ANCHOR: doSugar2a
 do let x ← E₁
    Stmt
    …
    Eₙ
-- ANCHOR_END: doSugar2a
) =
(
-- ANCHOR: doSugar2b
E₁ >>= fun x =>
  do Stmt
     …
     Eₙ
-- ANCHOR_END: doSugar2b
)
:= rfl





example :
 (
-- ANCHOR: doSugar4a
do let x := E₁
   Stmt
   …
   Eₙ
-- ANCHOR_END: doSugar4a
) =
 (
-- ANCHOR: doSugar4b
let x := E₁
do Stmt
   …
   Eₙ
-- ANCHOR_END: doSugar4b
)
:= rfl


variable {E₁ : m Unit}

example :
 (
-- ANCHOR: doSugar3a
  do E₁
     Stmt
     …
     Eₙ
-- ANCHOR_END: doSugar3a
) =
(
-- ANCHOR: doSugar3b
E₁ >>= fun () =>
  do Stmt
     …
     Eₙ
-- ANCHOR_END: doSugar3b
)
:= rfl

end

namespace WithDo
variable {α β : Type} {m : Type → Type}
-- ANCHOR: firstThirdFifthSeventhDo
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
    (xs : List α) : m (α × α × α × α) := do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)
-- ANCHOR_END: firstThirdFifthSeventhDo


-- ANCHOR: mapM
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    let hd ← f x
    let tl ← mapM f xs
    pure (hd :: tl)
-- ANCHOR_END: mapM
end WithDo

section
variable {α β : Type} {m : Type → Type}
-- ANCHOR: mapMNested
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    pure ((← f x) :: (← mapM f xs))
-- ANCHOR_END: mapMNested
end

namespace Numbering

open Monads.State
instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

-- ANCHOR: numberDo
def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      let numberedLeft ← helper left
      let n ← get
      set (n + 1)
      let numberedRight ← helper right
      ok (BinTree.branch numberedLeft (n, x) numberedRight)
  (helper t 0).snd
-- ANCHOR_END: numberDo

namespace Short


-- ANCHOR: numberDoShort
def increment : State Nat Nat := do
  let n ← get
  set (n + 1)
  pure n

def number (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch left x right => do
      pure
        (BinTree.branch
          (← helper left)
          ((← increment), x)
          (← helper right))
  (helper t 0).snd
-- ANCHOR_END: numberDoShort
end Short

end Numbering
