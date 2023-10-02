import Examples.Support

book declaration {{{ Many }}}
  inductive Many (α : Type) where
    | none : Many α
    | more : α → (Unit → Many α) → Many α
stop book declaration


book declaration {{{ one }}}
  def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)
stop book declaration


book declaration {{{ union }}}
  def Many.union : Many α → Many α → Many α
    | Many.none, ys => ys
    | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)
stop book declaration



book declaration {{{ fromList }}}
  def Many.fromList : List α → Many α
    | [] => Many.none
    | x :: xs => Many.more x (fun () => fromList xs)
stop book declaration


book declaration {{{ take }}}
  def Many.take : Nat → Many α → List α
    | 0, _ => []
    | _ + 1, Many.none => []
    | n + 1, Many.more x xs => x :: (xs ()).take n

  def Many.takeAll : Many α → List α
    | Many.none => []
    | Many.more x xs => x :: (xs ()).takeAll
stop book declaration


book declaration {{{ bind }}}
  def Many.bind : Many α → (α → Many β) → Many β
    | Many.none, _ =>
      Many.none
    | Many.more x xs, f =>
      (f x).union (bind (xs ()) f)
stop book declaration

namespace Agh

axiom v : Nat
axiom f : Nat → Many String

evaluation steps {{{ bindLeft }}}
  Many.bind (Many.one v) f
  ===>
  Many.bind (Many.more v (fun () => Many.none)) f
  ===>
  (f v).union (Many.bind Many.none f)
  ===>
  (f v).union Many.none
end evaluation steps

end Agh


book declaration {{{ MonadMany }}}
  instance : Monad Many where
    pure := Many.one
    bind := Many.bind
stop book declaration

instance : Alternative Many where
  failure := .none
  orElse xs ys := Many.union xs (ys ())


def Many.range (n k : Nat) : Many Nat :=
  if n < k then Many.more n (fun _ => range (n + 1) k) else Many.none
  termination_by range n k => k - n



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
theorem Many_bind_pure (ys : Many α) : ys >>= pure = ys := by
  induction ys with
  | none => simp [bind, Many.bind]
  | more y ys ih =>
    simp [bind, Many.bind, pure, Many.union]
    simp [bind, Many.bind, pure, Many.union] at ih
    funext _
    apply ih


instance : LawfulMonad Many where
  map_const := by
    simp [Functor.map, Functor.mapConst]
  id_map xs := by
    induction xs <;> simp [Functor.map, Many.bind, Function.comp, Many.union]
    case more x xs ih =>
      simp [Functor.map] at ih
      funext _
      apply ih
  seqLeft_eq xs ys := by
    induction xs <;> simp [SeqLeft.seqLeft, Seq.seq, Many.bind, Function.const, Functor.map, Many.union, Function.comp]
    case more x xs ih =>
      simp [SeqLeft.seqLeft, Seq.seq, Function.const, Functor.map, Function.comp] at ih
      rw [ih ()]
  seqRight_eq xs ys := by
      induction xs with
      | none => simp [SeqRight.seqRight, Many.bind, Seq.seq]
      | more x xs ih =>
        simp [SeqRight.seqRight, Many.bind]
        simp [SeqRight.seqRight, Many.bind] at ih
        rw [ih]
        simp [Seq.seq, Function.const, Functor.map, Many.bind, Function.comp]
        conv =>
          rhs
          congr
          . apply Many_bind_pure
          . rfl
  pure_seq g xs := by
    induction xs <;> simp [pure, Seq.seq, Many.bind, Many.union, Function.comp, Functor.map]
    case more x xs ih =>
      funext _
      simp [pure, Seq.seq, Many.bind, Many.union, Function.comp, Functor.map] at ih
      apply ih
  bind_pure_comp f xs := by
    simp [bind, Many.bind, pure, Functor.map, Function.comp]
  bind_map f xs := by
    simp [bind, Many.bind, pure, Functor.map, Function.comp, Seq.seq]
  pure_bind x f := by
    simp [bind, Many.bind, pure, Functor.map, Function.comp, Seq.seq]
    apply Many.union_none_right_id
  bind_assoc xs f g := by
    induction xs
    case none => simp [bind, Many.bind, Many.union]
    case more x xs ih =>
      simp [bind, Many.bind]
      simp [bind, Many.bind] at ih
      generalize f x = fx
      induction fx with
      | none => simp [Many.union, *]
      | more y ys ih2 =>
        simp [Many.union, Many.bind, *]
        generalize g y = gy
        cases gy with
        | none => simp [Many.union]
        | more z zs =>
          simp [Many.union]
          funext _
          rw [Many.union_assoc]


book declaration {{{ addsTo }}}
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
stop book declaration


expect info {{{ addsToFifteen }}}
  #eval (addsTo 15 [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]).takeAll
message
"[[7, 8],
 [6, 9],
 [5, 10],
 [4, 5, 6],
 [3, 5, 7],
 [3, 4, 8],
 [2, 6, 7],
 [2, 5, 8],
 [2, 4, 9],
 [2, 3, 10],
 [2, 3, 4, 6],
 [1, 6, 8],
 [1, 5, 9],
 [1, 4, 10],
 [1, 3, 5, 6],
 [1, 3, 4, 7],
 [1, 2, 5, 7],
 [1, 2, 4, 8],
 [1, 2, 3, 9],
 [1, 2, 3, 4, 5]]"
end expect
