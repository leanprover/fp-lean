import ExampleSupport

namespace F


-- ANCHOR: HonestFunctor
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
  mapConst : {α β : Type u} → α → f β → f α :=
    Function.comp map (Function.const _)
-- ANCHOR_END: HonestFunctor

namespace EEE
variable {α : Type}
variable {f : Type → Type}
variable {β : Type}
variable [inst : Functor f]

open Functor in
-- ANCHOR: unfoldCompConst
example : ((Function.comp map (Function.const _) : α → f β → f α) : (α → f β → f α)) = (fun (x : α) (y : f β) => map (fun _ => x) y : (α → f β → f α)) := rfl
-- ANCHOR_END: unfoldCompConst
end EEE

end F


-- ANCHOR: simpleConst
def simpleConst  (x : α) (_ : β) : α := x
-- ANCHOR_END: simpleConst

#check simpleConst


/-- info:
["same", "same", "same"]
-/
#check_msgs in
-- ANCHOR: mapConst
#eval [1, 2, 3].map (simpleConst "same")
-- ANCHOR_END: mapConst

namespace F

/-- info:
Function.const.{u, v} {α : Sort u} (β : Sort v) (a : α) : β → α
-/
#check_msgs in
-- ANCHOR: FunctionConstType
#check Function.const
-- ANCHOR_END: FunctionConstType
end F

namespace F1


-- ANCHOR: FunctorSimplified
class Functor (f : Type u → Type v) : Type (max (u+1) v) where
  map : {α β : Type u} → (α → β) → f α → f β
-- ANCHOR_END: FunctorSimplified
end F1


namespace F2


-- ANCHOR: FunctorDatatype
inductive Functor (f : Type u → Type v) : Type (max (u+1) v) where
  | mk : ({α β : Type u} → (α → β) → f α → f β) → Functor f
-- ANCHOR_END: FunctorDatatype
end F2

namespace A


-- ANCHOR: Pure
class Pure (f : Type u → Type v) : Type (max (u+1) v) where
  pure {α : Type u} : α → f α
-- ANCHOR_END: Pure


-- ANCHOR: Seq
class Seq (f : Type u → Type v) : Type (max (u+1) v) where
  seq : {α β : Type u} → f (α → β) → (Unit → f α) → f β
-- ANCHOR_END: Seq


-- ANCHOR: SeqLeft
class SeqLeft (f : Type u → Type v) : Type (max (u+1) v) where
  seqLeft : {α β : Type u} → f α → (Unit → f β) → f α
-- ANCHOR_END: SeqLeft


-- ANCHOR: SeqRight
class SeqRight (f : Type u → Type v) : Type (max (u+1) v) where
  seqRight : {α β : Type u} → f α → (Unit → f β) → f β
-- ANCHOR_END: SeqRight


-- ANCHOR: Applicative
class Applicative (f : Type u → Type v)
    extends Functor f, Pure f, Seq f, SeqLeft f, SeqRight f where
  map      := fun x y => Seq.seq (pure x) fun _ => y
  seqLeft  := fun a b => Seq.seq (Functor.map (Function.const _) a) b
  seqRight := fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
-- ANCHOR_END: Applicative


namespace EEE
variable {α : Type}
variable {f : Type → Type}
variable {β : Type}
variable [inst : Applicative f]

-- ANCHOR: unfoldMapConstSeqLeft
example : (fun a b => Seq.seq (Functor.map (Function.const _) a) b : (f α → (Unit → f β) → f α)) = (fun a b => Seq.seq ((fun x _ => x) <$> a) b : (f α → (Unit → f β) → f α)) := rfl
-- ANCHOR_END: unfoldMapConstSeqLeft

-- ANCHOR: mapConstList
example : ((fun x _ => x) <$> [1, 2, 3] : (List (α → Nat))) = ([fun _ => 1, fun _ => 2, fun _ => 3] : (List (α → Nat))) := rfl
-- ANCHOR_END: mapConstList

-- ANCHOR: mapConstOption
example : ((fun x _ => x) <$> some "hello" : (Option (α → String))) = (some (fun _ => "hello") : (Option (α → String))) := rfl
-- ANCHOR_END: mapConstOption

evaluation steps : f α → (Unit → f β) → f β {{{ unfoldMapConstSeqRight }}}
-- ANCHOR: unfoldMapConstSeqRight
fun a b => Seq.seq (Functor.map (Function.const _ id) a) b
===>
fun a b => Seq.seq ((fun _ => id) <$> a) b
===>
fun a b => Seq.seq ((fun _ => fun x => x) <$> a) b
===>
fun a b => Seq.seq ((fun _ x => x) <$> a) b
-- ANCHOR_END: unfoldMapConstSeqRight
end evaluation steps



-- ANCHOR: mapConstIdList
example : ((fun _ x => x) <$> [1, 2, 3] : (List (β → β))) = ([fun x => x, fun x => x, fun x => x] : (List (β → β))) := rfl
-- ANCHOR_END: mapConstIdList

-- ANCHOR: mapConstIdOption
example : ((fun _ x => x) <$> some "hello" : (Option (β → β))) = (some (fun x => x) : (Option (β → β))) := rfl
-- ANCHOR_END: mapConstIdOption

end EEE

end A

namespace SeqLeftSugar

variable {f : Type → Type}
variable {α : Type}
variable {β : Type}
variable [inst : SeqLeft f]
variable {E1 : f α}
variable {E2 : f β}

-- ANCHOR: seqLeftSugar
example : E1 <* E2 = SeqLeft.seqLeft E1 (fun () => E2) := rfl
-- ANCHOR_END: seqLeftSugar

-- ANCHOR: seqLeftType
example : f α → (Unit → f β) → f α := SeqLeft.seqLeft
-- ANCHOR_END: seqLeftType

end SeqLeftSugar


similar datatypes Applicative A.Applicative
similar datatypes SeqLeft A.SeqLeft
similar datatypes Seq A.Seq
similar datatypes SeqRight A.SeqRight
similar datatypes Pure A.Pure

namespace M


-- ANCHOR: Bind
class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m α → (α → m β) → m β
-- ANCHOR_END: Bind


-- ANCHOR: Monad
class Monad (m : Type u → Type v) : Type (max (u+1) v)
    extends Applicative m, Bind m where
  map      f x := bind x (Function.comp pure f)
  seq      f x := bind f fun y => Functor.map y (x ())
  seqLeft  x y := bind x fun a => bind (y ()) (fun _ => pure a)
  seqRight x y := bind x fun _ => y ()
-- ANCHOR_END: Monad

end M

similar datatypes Bind M.Bind
similar datatypes Monad M.Monad

-- ANCHOR: extras
example := Prop
example := Type
example := Type 1
example := Type 2
example : List Nat := [0, 17]
example := @List.map
-- ANCHOR_END: extras
