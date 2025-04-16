import Examples.Support

namespace F


book declaration {{{ HonestFunctor }}}
  class Functor (f : Type u → Type v) : Type (max (u+1) v) where
    map : {α β : Type u} → (α → β) → f α → f β
    mapConst : {α β : Type u} → α → f β → f α :=
      Function.comp map (Function.const _)
stop book declaration

namespace EEE
axiom α : Type
axiom f : Type → Type
axiom β : Type
@[instance] axiom inst : Functor f

open Functor in
bookExample : α → f β → f α {{{ unfoldCompConst }}}
  (Function.comp map (Function.const _) : α → f β → f α)
  ===>
  fun (x : α) (y : f β) => map (fun _ => x) y
end bookExample
end EEE

end F


book declaration {{{ simpleConst }}}
  def simpleConst  (x : α) (_ : β) : α := x
stop book declaration

#check simpleConst


expect info {{{ mapConst }}}
  #eval [1, 2, 3].map (simpleConst "same")
message
"[\"same\", \"same\", \"same\"]"
end expect

namespace F

expect info {{{ FunctionConstType }}}
  #check Function.const
message
"Function.const.{u, v} {α : Sort u} (β : Sort v) (a : α) : β → α"
end expect
end F

namespace F1


book declaration {{{ FunctorSimplified }}}
  class Functor (f : Type u → Type v) : Type (max (u+1) v) where
    map : {α β : Type u} → (α → β) → f α → f β
stop book declaration
end F1


namespace F2


book declaration {{{ FunctorDatatype }}}
  inductive Functor (f : Type u → Type v) : Type (max (u+1) v) where
    | mk : ({α β : Type u} → (α → β) → f α → f β) → Functor f
stop book declaration
end F2

namespace A


book declaration {{{ Pure }}}
  class Pure (f : Type u → Type v) : Type (max (u+1) v) where
    pure {α : Type u} : α → f α
stop book declaration


book declaration {{{ Seq }}}
  class Seq (f : Type u → Type v) : Type (max (u+1) v) where
    seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
stop book declaration


book declaration {{{ SeqLeft }}}
  class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
    seqLeft : {α β : Type u} → f α → (Unit → f β) → f α
stop book declaration


book declaration {{{ SeqRight }}}
  class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
    seqRight : {α β : Type u} → f α → (Unit → f β) → f β
stop book declaration



book declaration {{{ Applicative }}}
  class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
    map      := fun x y => Seq.seq (pure x) fun _ => y
    seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
    seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
stop book declaration


namespace EEE
axiom α : Type
axiom f : Type → Type
axiom β : Type
@[instance] axiom inst : Applicative f

bookExample : f α → (Unit → f β) → f α {{{ unfoldMapConstSeqLeft }}}
  fun a b => Seq.seq (Functor.map (Function.const _) a) b
  ===>
  fun a b => Seq.seq ((fun x _ => x) <$> a) b
end bookExample

bookExample : List (α → Nat) {{{ mapConstList }}}
  (fun x _ => x) <$> [1, 2, 3]
  ===>
  [fun _ => 1, fun _ => 2, fun _ => 3]
end bookExample

bookExample : Option (α → String) {{{ mapConstOption }}}
  (fun x _ => x) <$> some "hello"
  ===>
  some (fun _ => "hello")
end bookExample

evaluation steps : f α → (Unit → f β) → f β {{{ unfoldMapConstSeqRight }}}
  fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
  ===>
  fun a b => Seq.seq ((fun _ => id) <$> a) b
  ===>
  fun a b => Seq.seq ((fun _ => fun x => x) <$> a) b
  ===>
  fun a b => Seq.seq ((fun _ x => x) <$> a) b
end evaluation steps



bookExample : List (β → β) {{{ mapConstIdList }}}
  (fun _ x => x) <$> [1, 2, 3]
  ===>
  [fun x => x, fun x => x, fun x => x]
end bookExample

bookExample : Option (β → β) {{{ mapConstIdOption }}}
  (fun _ x => x) <$> some "hello"
  ===>
  some (fun x => x)
end bookExample

end EEE

end A

namespace SeqLeftSugar

axiom f : Type → Type
axiom α : Type
axiom β : Type
@[instance] axiom inst : SeqLeft f
axiom E1 : f α
axiom E2 : f β

bookExample {{{ seqLeftSugar }}}
  E1 <* E2
  ===>
  SeqLeft.seqLeft E1 (fun () => E2)
end bookExample

bookExample type {{{ seqLeftType }}}
  SeqLeft.seqLeft
  <===
  f α → (Unit → f β) → f α
end bookExample

end SeqLeftSugar


similar datatypes Applicative A.Applicative
similar datatypes SeqLeft A.SeqLeft
similar datatypes Seq A.Seq
similar datatypes SeqRight A.SeqRight
similar datatypes Pure A.Pure

namespace M


book declaration {{{ Bind }}}
  class Bind (m : Type u → Type v) where
    bind : {α β : Type u} → m α → (α → m β) → m β
stop book declaration


book declaration {{{ Monad }}}
  -- TODO: Structure type annotation syntax change - check text
  class Monad (m : Type u → Type v) : Type (max (u+1) v) extends Applicative m, Bind m  where
    map      f x := bind x (Function.comp pure f)
    seq      f x := bind f fun y => Functor.map y (x ())
    seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
    seqRight x y := bind x fun _ => y ()
stop book declaration

end M

similar datatypes Bind M.Bind
similar datatypes Monad M.Monad
