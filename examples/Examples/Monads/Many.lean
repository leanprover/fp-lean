import ExampleSupport

-- ANCHOR: Many
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α
-- ANCHOR_END: Many


-- ANCHOR: one
def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)
-- ANCHOR_END: one


-- ANCHOR: union
def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)
-- ANCHOR_END: union



-- ANCHOR: fromList
def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)
-- ANCHOR_END: fromList


-- ANCHOR: take
def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n

def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll
-- ANCHOR_END: take


-- ANCHOR: bind
def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)
-- ANCHOR_END: bind

namespace Agh

axiom v : Nat
axiom f : Nat → Many String

evaluation steps {{{ bindLeft }}}
-- ANCHOR: bindLeft
Many.bind (Many.one v) f
===>
Many.bind (Many.more v (fun () => Many.none)) f
===>
(f v).union (Many.bind Many.none f)
===>
(f v).union Many.none
-- ANCHOR_END: bindLeft
end evaluation steps

end Agh

section

local syntax "…" : term
variable {α β γ : Type}
variable {f : α → Many β} {v : Many α}
variable {v₁ : α} {v₂ : α} {v₃ : α} {vₙ : α}  {«…» : α}
macro_rules
  | `(term|…) => `(«…»)

local instance : Union (Many α) where
  union := .union

local instance : Insert α (Many α) where
  insert x xs := .more x (fun () => xs)

local instance : Singleton α (Many α) where
  singleton x := .one x

-- ANCHOR: vSet
example : Many α := {v₁, v₂, v₃, …, vₙ}
-- ANCHOR_END: vSet

variable {«…» : Many α}
macro_rules
  | `(term|…) => `(«…»)

-- ANCHOR: bindOne
example : Many.bind v Many.one = v := by
  induction v
  . simp [Many.bind, Many.one]
  . simp [Many.bind, Many.one, *, Many.union]
-- ANCHOR_END: bindOne

-- ANCHOR: bindAssoc
example {g : β → Many γ} := Many.bind (Many.bind v f) g = Many.bind v (fun x => Many.bind (f x) g)
-- ANCHOR_END: bindAssoc

-- ANCHOR: vSets
example : Many α := {v₁} ∪ {v₂} ∪ {v₃} ∪ … ∪ {vₙ}
-- ANCHOR_END: vSets


variable {«…» : Many β}
macro_rules
  | `(term|…) => `(«…»)



evaluation steps -check {{{ bindUnion }}}
-- ANCHOR: bindUnion
Many.bind v f
===>
f v₁ ∪ f v₂ ∪ f v₃ ∪ … ∪ f vₙ
-- ANCHOR_END: bindUnion
end evaluation steps

variable {g : β → Many γ} {«…» : Many γ}

macro_rules
  | `(term|…) => `(«…»)

evaluation steps -check {{{ bindBindLeft }}}
--- ANCHOR: bindBindLeft
Many.bind (Many.bind v f) g
===>
Many.bind (f v₁) g ∪
Many.bind (f v₂) g ∪
Many.bind (f v₃) g ∪
… ∪
Many.bind (f vₙ) g
--- ANCHOR_END: bindBindLeft
end evaluation steps

evaluation steps -check {{{ bindBindRight }}}
-- ANCHOR: bindBindRight
Many.bind v (fun x => Many.bind (f x) g)
===>
(fun x => Many.bind (f x) g) v₁ ∪
(fun x => Many.bind (f x) g) v₂ ∪
(fun x => Many.bind (f x) g) v₃ ∪
… ∪
(fun x => Many.bind (f x) g) vₙ
===>
Many.bind (f v₁) g ∪
Many.bind (f v₂) g ∪
Many.bind (f v₃) g ∪
… ∪
Many.bind (f vₙ) g
-- ANCHOR_END: bindBindRight
end evaluation steps
end

-- ANCHOR: MonadMany
instance : Monad Many where
  pure := Many.one
  bind := Many.bind
-- ANCHOR_END: MonadMany

instance : Alternative Many where
  failure := .none
  orElse xs ys := Many.union xs (ys ())


def Many.range (n k : Nat) : Many Nat :=
  if n < k then Many.more n (fun _ => range (n + 1) k) else Many.none

@[simp]
theorem Many.union_none_right_id : Many.union xs Many.none = xs := by
  induction xs <;> simp [union]
  case more x xs ih =>
    funext _
    apply ih

theorem Many.union_assoc : Many.union xs (Many.union ys zs) = Many.union (Many.union xs ys) zs := by
  induction xs <;> simp [union]
  case more x xs ih =>
    funext _
    apply ih

@[simp]
theorem Many_bind_pure (ys : Many α) : ys >>= pure = ys := by
  induction ys with
  | none => simp [bind, Many.bind]
  | more y ys ih =>
    specialize ih ()
    simp [bind, Many.bind, pure, Many.union] at ih
    simp [bind, Many.bind, pure, Many.union, ih, Many.one]

@[simp]
theorem Many_bind_one (ys : Many α) : ys.bind Many.one = ys := by
  induction ys with
  | none => simp [bind, Many.bind]
  | more y ys ih =>
    specialize ih ()
    simp only at ih
    simp [bind, Many.bind, pure, Many.union, ih, Many.one]

@[simp]
theorem Many_one_bind : (Many.one x).bind f = f x := by
  simp [Many.one, Many.bind]

@[simp]
theorem Many_none_bind : Many.none.bind f = Many.none := by
  rfl

instance : LawfulMonad Many where
  map_const := by
    simp [Functor.map, Functor.mapConst]
  id_map xs := by
    induction xs <;> simp [Functor.map, Many.bind, Function.comp, Many.union]
    case more x xs ih =>
      specialize ih ()
      simp [Functor.map] at ih
      simp [ih, Many.one, Many.union]
  seqLeft_eq xs ys := by
    induction xs <;> simp [SeqLeft.seqLeft, Seq.seq, Many.bind, Function.const, Functor.map, Many.union, Function.comp]
    case more x xs ih =>
      specialize ih ()
      simp only [SeqLeft.seqLeft, Seq.seq, Functor.map] at ih
      simp only [ih]
      apply congrArg
      simp [Many.union, Many_bind_pure, *]

  seqRight_eq xs ys := by
      induction xs with
      | none =>
        simp [SeqRight.seqRight, Many.bind, Seq.seq, Functor.map]
      | more x xs ih =>
        simp [SeqRight.seqRight, Many.bind]
        simp [SeqRight.seqRight, Many.bind] at ih
        rw [ih]
        simp [Seq.seq, Function.const, Functor.map, Many.bind, Function.comp, Many.one, Many.union]

  pure_seq g xs := by
    simp [Functor.map, Seq.seq, pure]

  bind_pure_comp f xs := by
    rfl
  bind_map f xs := by
    simp [bind, Many.bind, pure, Functor.map, Function.comp, Seq.seq]
  pure_bind x f := by
    simp [bind, Many.bind, pure, Functor.map, Function.comp, Seq.seq]
  bind_assoc xs f g := by
    induction xs
    case none => simp [bind, Many.bind, Many.union]
    case more x xs ih =>
      specialize ih ()
      simp only [bind] at ih
      simp only [bind, Many.bind]
      generalize f x = fx
      induction fx with
      | none =>
        simp [Many.union, *]
      | more y ys ih2 =>
        simp only [Many.union, Many.bind, ih2]
        generalize g y = gy
        cases gy with simp [Many.union]
        | more z zs =>
          rw [Many.union_assoc]


-- ANCHOR: addsTo
def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] =>
    if goal == 0 then
      pure []
    else
      Many.none
  | x :: xs =>
    if x > goal then
      addsTo goal xs
    else
      (addsTo goal xs).union
        (addsTo (goal - x) xs >>= fun answer =>
         pure (x :: answer))
-- ANCHOR_END: addsTo

-- ANCHOR: printList
def printList [ToString α] : List α → IO Unit
  | [] => pure ()
  | x :: xs => do
    IO.println x
    printList xs
-- ANCHOR_END: printList

/-- info:
[7, 8]
[6, 9]
[5, 10]
[4, 5, 6]
[3, 5, 7]
[3, 4, 8]
[2, 6, 7]
[2, 5, 8]
[2, 4, 9]
[2, 3, 10]
[2, 3, 4, 6]
[1, 6, 8]
[1, 5, 9]
[1, 4, 10]
[1, 3, 5, 6]
[1, 3, 4, 7]
[1, 2, 5, 7]
[1, 2, 4, 8]
[1, 2, 3, 9]
[1, 2, 3, 4, 5]
-/
#check_msgs in
-- ANCHOR: addsToFifteen
#eval printList (addsTo 15 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).takeAll
-- ANCHOR_END: addsToFifteen
