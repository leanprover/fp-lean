import Examples.Support
import Examples.Monads
import Examples.Monads.Class

set_option linter.unusedVariables false



namespace Sugar
axiom E : Option Int
axiom E1 : Option Unit
axiom E2 : Option Unit
axiom Es : Option Unit
axiom Stmt : Option Unit
axiom En : Option Int

syntax "..." : term
macro_rules
  | `(...) => `(Es)

bookExample {{{ doSugar1 }}}
  do E
  ===>
  E
end bookExample

bookExample {{{ doSugar2 }}}
  do let x ← E1
     Stmt
     ...
     En
  ===>
  E1 >>= fun x =>
  do Stmt
     ...
     En
end bookExample

bookExample {{{ doSugar3 }}}
  do E1
     Stmt
     ...
     En
  ===>
  E1 >>= fun ⟨⟩ =>
  do Stmt
     ...
     En
end bookExample

bookExample {{{ doSugar4 }}}
  do let x := E1
     Stmt
     ...
     En
  ===>
  let x := E1
  do Stmt
     ...
     En
end bookExample


end Sugar

namespace WithDo
book declaration {{{ firstThirdFifthSeventhDo }}}
  def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α) := do
    let first ← lookup xs 0
    let third ← lookup xs 2
    let fifth ← lookup xs 4
    let seventh ← lookup xs 6
    pure (first, third, fifth, seventh)
stop book declaration


book declaration {{{ mapM }}}
  def mapM [Monad m] (f : α → m β) : List α → m (List β)
    | [] => pure []
    | x :: xs => do
      let hd ← f x
      let tl ← mapM f xs
      pure (hd :: tl)
stop book declaration
end WithDo

book declaration {{{ mapMNested }}}
  def mapM [Monad m] (f : α → m β) : List α → m (List β)
    | [] => pure []
    | x :: xs => do
      pure ((← f x) :: (← mapM f xs))
stop book declaration


namespace Numbering

open Monads.State
instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'

book declaration {{{ numberDo }}}
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
stop book declaration

namespace Short


book declaration {{{ numberDoShort }}}
  def increment : State Nat Nat := do
    let n ← get
    set (n + 1)
    pure n

  def number (t : BinTree α) : BinTree (Nat × α) :=
    let rec helper : BinTree α → State Nat (BinTree (Nat × α))
      | BinTree.leaf => pure BinTree.leaf
      | BinTree.branch left x right => do
        pure (BinTree.branch (← helper left) ((← increment), x) (← helper right))
    (helper t 0).snd
stop book declaration
end Short

end Numbering
