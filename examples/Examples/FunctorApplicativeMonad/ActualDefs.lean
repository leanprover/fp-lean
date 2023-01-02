import Examples.Support

namespace F


book declaration {{{ HonestFunctor }}}
  class Functor (f : Type u → Type v) : Type (max (u+1) v) where
    map : {α β : Type u} → (α → β) → f α → f β
    mapConst : {α β : Type u} → α → f β → f α := Function.comp map (Function.const _)
stop book declaration


expect info {{{ FunctionConstType }}}
  #check @Function.const
message
"@Function.const : {α : Sort u_1} → (β : Sort u_2) → α → β → α"
end expect
end F

namespace F1

class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β

end F1


namespace F2

inductive Functor (f : Type u → Type v) : Type (max (u+1) v) where
  | mk : ({α β : Type u} → (α → β) → f α → f β) → Functor f

end F2

namespace A

class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β

class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α

class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β


class Pure (f : Type u → Type v) where
  pure {α : Type u} : α → f α

class Applicative (f : Type u → Type v) extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b

end A

namespace M

class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β

class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u+1) v) where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()

end M
